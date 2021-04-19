// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.injectableValueAnalysis;

import com.google.common.base.Splitter;
import com.google.common.base.Throwables;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.types.c.CBasicType;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.CoreComponentsFactory;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSetFactory;
import org.sosy_lab.cpachecker.core.specification.Specification;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState.ValueAndType;
import org.sosy_lab.cpachecker.cpa.value.type.NumericValue;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

@Options(prefix = "injectableValueAnalysis")
public class InjectableValueAnalysisExecutor implements Algorithm {

  @Option(
      secure = true,
      description = "Path to the file, where the ids of the datapoints will be stored")
  private String violatingIDsFile = "output/violatingIDs.txt";

  @Option(
      secure = true,
      description = "Path to the file, where the values of the datapoints are  stored")
  private String variableValuesFile = "output/variableValues.csv";

  @Option(
      secure = true,
      description = "Path to the file, where the names of the variables present are stored")
  private String variableNamesFile = "output/variableNames.csv";


  private final LogManager logger;

  private final CFA cfa;
  private final Algorithm algorithm;

  private Configuration config;
  private Specification spec;
  private ReachedSetFactory rfFactory;
  ConfigurableProgramAnalysis cpa;
  ShutdownNotifier shutdownNotifier;
  Configuration updatedCFG;

  public InjectableValueAnalysisExecutor(
      Algorithm pAlgorithm,
      LogManager pLogger,
      CFA pCfa,
      Configuration pConfig,
      ConfigurableProgramAnalysis pCpa,
      ShutdownNotifier pShutdownNotifier,
      Specification pSpecification)
      throws InvalidConfigurationException {
    algorithm = pAlgorithm;
    cfa = Objects.requireNonNull(pCfa);
    logger = Objects.requireNonNull(pLogger);
    this.config = pConfig;
    this.rfFactory = new ReachedSetFactory(config, logger);
    this.cpa = pCpa;
    this.shutdownNotifier = pShutdownNotifier;
    this.spec = pSpecification;
    config.inject(this, InjectableValueAnalysisExecutor.class);
    updatedCFG =
        Configuration.builder().setOption("analysis.injectConcreteValues", "false").build();
  }

  @Override
  public AlgorithmStatus run(ReachedSet pReached) throws CPAException, InterruptedException {
    if (!(pReached instanceof PartitionedReachedSet)) {
      throw new CPAException("Expecting a partioned reached set");
    }
    PartitionedReachedSet reached = (PartitionedReachedSet) pReached;
    AlgorithmStatus status = AlgorithmStatus.NO_PROPERTY_CHECKED;
    algorithm.run(reached);

    if (cfa.getAllLoopHeads().isPresent() && cfa.getLoopStructure().isPresent()) {
      LoopStructure loopStruct = cfa.getLoopStructure().get();

      // TODO: Add support for programs with moer than one loop!
      if (loopStruct.getCount() != 1) {
        logger.log(
            Level.WARNING,
            "The program contains more than one loop. This is currently not supported, hence aborting!");
        throw new CPAException("Currently, only programs with a single loop are supported!");
      }

      CFANode loopHead = cfa.getAllLoopHeads().get().asList().get(0);
      com.google.common.base.Optional<CFANode> opt =
          CFAUtils.allPredecessorsOf(loopHead)
              .filter(
                  n ->
                      !cfa.getLoopStructure()
                          .get()
                          .getAllLoops()
                          .stream()
                          .anyMatch(l -> l.getLoopNodes().contains(n)))
              .first();

      List<AbstractState> argStateOfLoopHead = new ArrayList<>(filter(opt.get(), reached));

      // Create a new state for the given values
      Map<Integer, AbstractState> states = getAllAbstractStates(argStateOfLoopHead.get(0));
      Precision precision = reached.getPrecision(argStateOfLoopHead.get(0));

      List<String> violations = new ArrayList<>();

      for (Entry<Integer, AbstractState> state : states.entrySet()) {
        ShutdownManager manager = ShutdownManager.create();
        ReachedSet currentReached = rfFactory.create();
        currentReached.add(state.getValue(), precision);
        AlgorithmStatus result;
        try {
          ShutdownNotifier n = manager.getNotifier();
          CoreComponentsFactory fac = new CoreComponentsFactory(updatedCFG, logger, n, null);
          Algorithm currentAlg = fac.createAlgorithm(cpa, cfa, spec);

          result = currentAlg.run(currentReached);

        } catch (CPAException | InvalidConfigurationException e) {
          logger.log(
              Level.WARNING,
              String.format(
                  "Aborted execution for id %d due to %s",
                  state.getKey(), Throwables.getStackTraceAsString(e)));
          result = AlgorithmStatus.NO_PROPERTY_CHECKED;
        }

        if (result.equals(AlgorithmStatus.SOUND_AND_PRECISE)
            && currentReached.hasViolatedProperties()) {
          logger.log(Level.INFO, String.format("Violation found for id %s,", state.getKey()));
          violations.add(Integer.toString(state.getKey()));
        }
      }

      try {
        Path outfile;
        try {
          outfile = Files.createFile(Paths.get(this.violatingIDsFile));
        } catch (FileAlreadyExistsException e) {
          outfile = Paths.get(this.violatingIDsFile);
        }
        Files.write(
            outfile,
            String.join(System.lineSeparator(), violations).getBytes(Charset.defaultCharset()),
            StandardOpenOption.WRITE);

      } catch (IOException e) {
        throw new CPAException(
            String.format(
                "Storing the ids failed. Reason: %s", Throwables.getStackTraceAsString(e)));
      }
    }
    return status;
  }

  private Map<Integer, AbstractState> getAllAbstractStates(AbstractState pArgStateOfLoopHead)
      throws CPAException {

    try {
      Map<Integer, AbstractState> idToValues = new HashMap<>();
      List<String> values =
          com.google.common.io.Files.readLines(
              new File(this.variableValuesFile), Charset.defaultCharset());
      List<String> vars =
          com.google.common.io.Files.readLines(
              new File(this.variableNamesFile), Charset.defaultCharset());
      List<Pair<MemoryLocation, CType>> memLocs = parseVars(vars);

      for (String line : values) {
        if (line.isBlank()) {
          continue;
        }
        List<String> split = Splitter.on(',').splitToList(line);
        if (split.size() != memLocs.size() + 2) {
          throw new CPAException(
              String.format(
                  "Cannot parse the values (%s), as it contains %s elements as given in %s",
                  line, split.size() < memLocs.size() + 2 ? "few" : "many", memLocs));
        }
        int id = Integer.parseInt(split.get(0));
        Map<MemoryLocation, ValueAndType> tempMap = new HashMap<>();
        for (int i = 0; i < memLocs.size(); i++) {
          tempMap.put(
              memLocs.get(i).getFirst(),
              new ValueAndType(
                  new NumericValue(Integer.parseInt(split.get(i + 1))),
                  memLocs.get(i).getSecond()));
        }

        ValueAnalysisState s =
            new ValueAnalysisState(
                Optional.of(cfa.getMachineModel()), PathCopyingPersistentTreeMap.copyOf(tempMap));

        List<AbstractState> states =
            AbstractStates.extractStateByType(pArgStateOfLoopHead, CompositeState.class)
                .getWrappedStates();
        List<AbstractState> newStates = new ArrayList<>();
        for (AbstractState abstractState : states) {
          if (abstractState instanceof ValueAnalysisState) {
            newStates.add(s);
          } else {
            newStates.add(abstractState);
          }
        }
        idToValues.put(id, new ARGState(new CompositeState(newStates), null));
      }

      return idToValues;
    } catch (IOException | NumberFormatException e) {
      throw new CPAException("loading the values failed due to ", e);
    }
  }

  private List<Pair<MemoryLocation, CType>> parseVars(List<String> pVars) throws CPAException {
    List<Pair<MemoryLocation, CType>> locs = new ArrayList<>();
    for (String s : pVars) {
      List<String> splitted = Splitter.on(',').splitToList(s);
      if (splitted.size() != 2) {
        throw new CPAException("The variableName file is not well formatted!");
      } else {
        String variableName = splitted.get(0);
        if (variableName.startsWith("|") && variableName.endsWith("|")) {
          variableName = variableName.substring(1, variableName.length() - 1);
        }
        locs.add(Pair.of(MemoryLocation.valueOf(variableName), parseType(splitted.get(1))));
      }
    }
    return locs;
  }

  private CType parseType(String parts) {

    boolean isLongLong = parts.contains("long long");

    CBasicType pType;
    if (parts.endsWith(CBasicType.BOOL.name())) {
      pType = CBasicType.BOOL;
    } else if (parts.endsWith(CBasicType.CHAR.name())) {
      pType = CBasicType.CHAR;
    } else if (parts.endsWith(CBasicType.INT.name())) {
      pType = CBasicType.INT;
    } else if (parts.endsWith(CBasicType.INT128.name())) {
      pType = CBasicType.INT128;
    } else if (parts.endsWith(CBasicType.FLOAT.name())) {
      pType = CBasicType.FLOAT;
    } else if (parts.endsWith(CBasicType.DOUBLE.name())) {
      pType = CBasicType.DOUBLE;
    } else if (parts.endsWith(CBasicType.FLOAT128.name())) {
      pType = CBasicType.FLOAT128;
    } else {
      pType = CBasicType.UNSPECIFIED;
    }

    return new CSimpleType(
        parts.contains("const"),
        parts.contains("volatile"),
        pType,
        parts.contains("long"),
        parts.contains("short"),
        parts.contains("signed"),
        parts.contains("unsigned"),
        parts.contains("_Complex"),
        parts.contains("_Imaginary"),
        isLongLong);
  }

  private Set<AbstractState> filter(CFANode pPredOfLoopHead, PartitionedReachedSet pReached) {
    return pReached
        .asCollection()
        .stream()
        .filter(s -> AbstractStates.extractLocation(s).equals(pPredOfLoopHead))
        .collect(Collectors.toSet());
  }
}
