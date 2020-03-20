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
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.function.Supplier;
import java.util.logging.Level;
import javax.annotation.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;

@Options(prefix = "invariantGeneration.wrapper")
public class UAInvariantGenerator implements ExternalInvariantGenerator {
  private File witnessFile;
  private static final String PATH_TO_SCRIPTS =
      "src/org/sosy_lab/cpachecker/core/algorithm/invariants/invariantimport/scripts/";

  private String pathToOutDir = "output/";

  static final Level LOG_LEVEL = Level.INFO;
  private final String PATH_TO_CPA_DIR;
  String ABSOLUTE_PATH_TO_INV_FILE = "/run/";
  InvariantInC2WitnessParser parser;

  @Option(
    secure = true,
    description = "Path to the config file containing the cpas to generate and load invariants from seahorn")
  @FileOption(FileOption.Type.REQUIRED_INPUT_FILE)
  private Path configForInvGen = null;

  public UAInvariantGenerator(Configuration pConfig) throws InvalidConfigurationException {
    pConfig.inject(this);
    // set the output directory to the directory used by the cpa checker
    PATH_TO_CPA_DIR =
        UAInvariantGenerator.class.getProtectionDomain().getCodeSource().getLocation().getPath()
            + "../";
    parser = new InvariantInC2WitnessParser(pConfig);
    witnessFile = new File("proofWitness_UA.graphml");
  }

  @Override
  public File generateInvariant(
      CFA pCfa,
      @Nullable List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Configuration pConfig)
      throws CPAException {

    return parser.generateInvariant(
        pCfa,
        pSpecification,
        pLogger,
        pShutdownNotifier,
        configForInvGen,
        witnessFile);

  }

  @Override
  public Set<CandidateInvariant> generateInvariantAndLoad(
      CFA pCfa,
      @Nullable List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Configuration pConfig)
      throws CPAException {
    try {
      pLogger.log(Level.FINEST, this.pathToOutDir);
      File tempFile =
          generateInvariant(
              pCfa,
              pTargetNodesToGenerateFor,
              pSpecification,
              pLogger,
              pShutdownNotifier,
              pConfig);

      final Set<CandidateInvariant> candidates = new LinkedHashSet<>();

      final Multimap<String, CFANode> candidateGroupLocations = HashMultimap.create();

      WitnessInvariantsExtractor extractor =
          new WitnessInvariantsExtractor(
              pConfig,
              pSpecification,
              pLogger,
              pCfa,
              pShutdownNotifier,
              tempFile.toPath());
      extractor.extractCandidatesFromReachedSet(candidates, candidateGroupLocations);
      pLogger.log(LOG_LEVEL, "The invariants imported are" + candidates.toString());
      pLogger.log(LOG_LEVEL, "The invariants imported are" + candidates.toString());
      return candidates;
    } catch (InvalidConfigurationException | InterruptedException e) {
      throw new CPAException(getMessage() + System.lineSeparator() + e.toString(), e);
    }
  }

  public Multimap<Integer, Pair<String, String>>
      genInvsAndLoad(CFA pCfa, LogManager pLogger) throws CPAException {

    // Start UA:
    List<Path> sourceFiles = pCfa.getFileNames();
    if (sourceFiles.size() != 1) {
      throw new CPAException("Can onyl handle CFAs, where one source file is contained");
    }
    try {
      return genInvs(sourceFiles.get(0), pLogger);
    } catch (IOException | InterruptedException e) {
      throw new CPAException("", e);
    }
  }

  private Multimap<Integer, Pair<String, String>> genInvs(Path pPath, LogManager pLogger)
      throws IOException, InterruptedException {

    ProcessBuilder builder = new ProcessBuilder().inheritIO();

    pLogger.log(LOG_LEVEL, "Storing generated inv file at files at " + ABSOLUTE_PATH_TO_INV_FILE);

    /**
     * # Usage of the script:: # $1 = path to the file to generate invariant for # $2 = path to the
     * output directory to store generated invariants to # $3 = path to the dir where the scripts
     * are located
     */
    builder.command(
        PATH_TO_CPA_DIR + PATH_TO_SCRIPTS + "UAInvariantGeneration.sh",
        pPath.toFile().getAbsolutePath(),
        ABSOLUTE_PATH_TO_INV_FILE,
        PATH_TO_CPA_DIR + PATH_TO_SCRIPTS);
    Process process = builder.start();

    int exitCode = process.waitFor();
    // After finishing the invariant generation script ensure that everything worked out as planned!
    if (exitCode != 0) {
      pLogger.log(
          Level.WARNING,
          "The invariant genreatino for Ultimate Automizer returned a non-zero value, it is %d!",
          exitCode);
    }

    // Since the cpachecker input does not like "-1*", replace them by a simple "-"
    Path pathToLogFile = Path.of(ABSOLUTE_PATH_TO_INV_FILE + "log.txt");
    UALogParser logParser = new UALogParser(pLogger);
    return logParser.parseLog(pathToLogFile);


  }

  private String getMessage() {
    return "During computation, an interla error occured. The added exception provides a more detailed explanation"
        + System.lineSeparator()
        + "* @throws CPAException If the CFA contains more than one source file"
        + System.lineSeparator()
        + "  * @throws ParserConfigurationException in case of errors while parsing the Witness"
        + System.lineSeparator()
        + " * @throws IOException if the source file is not readable"
        + System.lineSeparator()
        + " * @throws TransformerException If the xml file is invalid"
        + System.lineSeparator()
        + " * @throws InterruptedException, InvalidConfigurationException  in case of problems loading the generated invariant"
        + System.lineSeparator();
  }

  @Override
  public Supplier<Path> getSupplierGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig)
      throws CPAException {
    return new Supplier<>() {

      @Override
      public Path get() {
        try {
          Path res =
              generateInvariant(
                  pCfa,
                  pTargetNodesToGenerateFor,
                  pSpecification,
                  pLogger,
                  pShutdownManager,
                  pConfig).toPath();
          pLogger.log(Level.WARNING, "Invariant generation finished for tool : Ultimate Automizer");
          return res;
        } catch (CPAException e) {
          throw new RuntimeException(e.toString());
        }
      }
    };
  }

  @Override
  public Callable<Path> getCallableGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig)
      throws CPAException {
    return () -> {
      Path res =
          generateInvariant(
              pCfa,
              pTargetNodesToGenerateFor,
              pSpecification,
              pLogger,
              pShutdownManager,
              pConfig).toPath();
      pLogger.log(Level.WARNING, "Invariant generation finished for tool : Ultimate AUtomizer");
      return res;

    };
  }

}
