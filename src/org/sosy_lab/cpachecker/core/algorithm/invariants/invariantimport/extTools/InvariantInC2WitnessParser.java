/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.extTools;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Predicates;
import com.google.common.base.Splitter;
import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableSet;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.channels.ClosedByInterruptException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.CoreComponentsFactory;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.reachedset.AggregatedReachedSets;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.witnessexport.Witness;
import org.sosy_lab.cpachecker.cpa.arg.witnessexport.WitnessExporter;
import org.sosy_lab.cpachecker.cpa.arg.witnessexport.WitnessToOutputFormatsUtils;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.BiPredicates;
import org.sosy_lab.cpachecker.util.Triple;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.resources.ResourceLimitChecker;

public class InvariantInC2WitnessParser {

  public final static Level LOG_LEVEL = Level.ALL;

  Configuration config;

  public InvariantInC2WitnessParser(Configuration pConfiguration) {
    config = pConfiguration;
  }

  public File generateInvariant(
      CFA pCfa,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Path pPath2SubConfig,
      File witnessFile)
      throws CPAException {

    Algorithm currentAlgorithm;

    ReachedSet currentReached;
    try {
      Configuration singleConfig = buildSubConfig(pPath2SubConfig, new HashSet<>(), pLogger);
      ConfigurationBuilder builder = Configuration.builder();

      builder.copyFrom(singleConfig);
      builder.setOption("analysis.generateExternalInvariants", "false");
      Configuration newConfig = builder.build();

      Collection<Statistics> stats = new ArrayList<>();
      CFANode node = pCfa.getMainFunction();
      Triple<Algorithm, ConfigurableProgramAnalysis, ReachedSet> restartAlg =
          createAlgorithm(
              newConfig,
              pPath2SubConfig.toString(),
              node,
              ShutdownManager.createWithParent(pShutdownNotifier),
              new AggregatedReachedSets(),
              stats,
              pLogger,
              pCfa,
              pSpecification);

      currentAlgorithm = restartAlg.getFirst();
      // currentCpa = restartAlg.getSecond();
      currentReached = restartAlg.getThird();
      currentAlgorithm.run(currentReached);

      // start the file, print the result (reached rset as arg to the witness file)
      ImmutableSet<ARGState> rootStates = ARGUtils.getRootStates(currentReached);
      if (rootStates.size() != 1) {
        pLogger.log(Level.INFO, "Could not determine ARG root for witness view");
        throw new CPAException(
            "SeaHorn: Could not determine ARG root for witness view, terminating");
      }
      ARGState rootState = rootStates.iterator().next();

      WitnessExporter argWitnessExporter =
          new WitnessExporter(newConfig, pLogger, Specification.alwaysSatisfied(), pCfa);
      Witness witness =
          argWitnessExporter
              .generateProofWitness(rootState, Predicates.alwaysTrue(), BiPredicates.alwaysTrue());

      @SuppressWarnings("resource")
      BufferedWriter writer =
          Files.newBufferedWriter(witnessFile.toPath(), Charset.defaultCharset());

      WitnessToOutputFormatsUtils.writeToGraphMl(witness, writer);

      writer.flush();
      writer.close();
      // try (BufferedReader br =
      // Files.newBufferedReader(witnessFile.toPath(), Charset.defaultCharset())) {
      // String line;
      // while ((line = br.readLine()) != null) {
      // System.out.println(line);
      // }
      // }

      return witnessFile;

    } catch (InvalidConfigurationException e) {
      pLogger.logUserException(
          Level.WARNING,
          e,
          "Skipping one analysis because the configuration file "
              + pPath2SubConfig.toString()
              + " is invalid");
      throw new CPAException(
          "SeaHorn: The configuration file is invalid: " + Throwables.getStackTraceAsString(e));
    } catch (IOException e) {
      String message =
          "Skipping one analysis because the configuration file "
              + pPath2SubConfig.toString()
              + " could not be read";
      if (pShutdownNotifier.shouldShutdown() && e instanceof ClosedByInterruptException) {
        pLogger.log(Level.WARNING, message);
      } else {
        pLogger.logUserException(Level.WARNING, e, message);
      }
      throw new CPAException(
          "SeaHorn: The configuration file is invalid: " + Throwables.getStackTraceAsString(e));
    } catch (InterruptedException e) {
      throw new CPAException(
          "SeaHorn: The thread was interrupted: " + Throwables.getStackTraceAsString(e));
    }
  }

  protected Configuration

      buildSubConfig(
          Path singleConfigFileName,
          Collection<String> ignoreOptions,
          LogManager pLogger)
          throws IOException, InvalidConfigurationException {

    ConfigurationBuilder singleConfigBuilder = Configuration.builder();
    singleConfigBuilder.copyFrom(config);
    for (String ignore : ignoreOptions) {
      singleConfigBuilder.clearOption(ignore);
    }

    // TODO next line overrides existing options with options loaded from file.
    // Perhaps we want to keep some global options like 'specification'?
    singleConfigBuilder.loadFromFile(singleConfigFileName);

    Configuration singleConfig = singleConfigBuilder.build();
    checkConfigs(config, singleConfig, singleConfigFileName, pLogger);
    return singleConfig;
  }

  protected Triple<Algorithm, ConfigurableProgramAnalysis, ReachedSet> createAlgorithm(
      Configuration singleConfig,
      String nameOfAnalysis,
      CFANode mainFunction,
      ShutdownManager singleShutdownManager,
      AggregatedReachedSets aggregateReached,
      Collection<Statistics> stats,
      LogManager logger,
      CFA cfa,
      Specification specification)
      throws InvalidConfigurationException, CPAException, InterruptedException {

    LogManager singleLogger = logger.withComponentName("Analysis " + nameOfAnalysis);

    ResourceLimitChecker singleLimits =
        ResourceLimitChecker.fromConfiguration(singleConfig, singleLogger, singleShutdownManager);
    singleLimits.start();

    CoreComponentsFactory coreComponents =
        new CoreComponentsFactory(
            singleConfig,
            singleLogger,
            singleShutdownManager.getNotifier(),
            aggregateReached);
    ConfigurableProgramAnalysis cpa = coreComponents.createCPA(cfa, specification);
    GlobalInfo.getInstance().setUpInfoFromCPA(cpa);
    Algorithm algorithm = coreComponents.createAlgorithm(cpa, cfa, specification);
    ReachedSet reached = createInitialReachedSet(cpa, mainFunction, coreComponents, singleLogger);

    if (cpa instanceof StatisticsProvider) {
      ((StatisticsProvider) cpa).collectStatistics(stats);
    }
    if (algorithm instanceof StatisticsProvider) {
      ((StatisticsProvider) algorithm).collectStatistics(stats);
    }

    return Triple.of(algorithm, cpa, reached);
  }

  private static ReachedSet createInitialReachedSet(
      ConfigurableProgramAnalysis cpa,
      CFANode mainFunction,
      CoreComponentsFactory pFactory,
      LogManager singleLogger)
      throws InterruptedException {
    singleLogger.log(Level.FINE, "Creating initial reached set");

    AbstractState initialState =
        cpa.getInitialState(mainFunction, StateSpacePartition.getDefaultPartition());
    Precision initialPrecision =
        cpa.getInitialPrecision(mainFunction, StateSpacePartition.getDefaultPartition());

    ReachedSet reached = pFactory.createReachedSet();
    reached.add(initialState, initialPrecision);
    return reached;
  }

  protected static void checkConfigs(
      Configuration pGlobalConfig,
      Configuration pSingleConfig,
      Path pSingleConfigFileName,
      LogManager pLogger)
      throws InvalidConfigurationException {
    Map<String, String> global = configToMap(pGlobalConfig);
    Map<String, String> single = configToMap(pSingleConfig);
    for (Entry<String, String> entry : global.entrySet()) {
      String key = entry.getKey();
      String value = entry.getValue();
      if (single.containsKey(key) && !value.equals(single.get(key))) {
        pLogger.logf(
            Level.INFO,
            "Mismatch of configuration options when loading from '%s': '%s' has two values '%s' and '%s'. Using '%s'.",
            pSingleConfigFileName,
            key,
            value,
            single.get(key),
            single.get(key));
      }
    }

    // "cfa.*"-options of a subconfig are effectively ignored because the CFA gets only generated
    // once for the NestingAlgorithm, so we check whether all "cfa.*"-options that are set in the
    // subconfig are also present and with the same value in the global config:
    for (Entry<String, String> entry : single.entrySet()) {
      String key = entry.getKey();
      String value = entry.getValue();
      if (key.startsWith("cfa.") && !(global.containsKey(key) && value.equals(global.get(key)))) {
        throw new InvalidConfigurationException(
            "CFA option of a nested sub-configuration must also be present in the outer configuration!\n"
                + String.format(
                    "inner config: \"%s = %s\" ; outer config: \"%s = %s\" ",
                    key,
                    value,
                    key,
                    global.get(key)));
      }
    }
  }

  /** get an iterable data structure from configuration options. Sadly there is no nicer way. */
  private static Map<String, String> configToMap(Configuration config) {
    Map<String, String> mp = new LinkedHashMap<>();
    for (String option : Splitter.on("\n").omitEmptyStrings().split(config.asPropertiesString())) {
      List<String> split = Splitter.on(" = ").splitToList(option);
      checkArgument(split.size() == 2, "unexpected option format: %s", option);
      mp.put(split.get(0), split.get(1));
    }
    return mp;
  }

}
