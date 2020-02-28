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

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.logging.Level;
import javax.annotation.Nullable;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
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

@Options(prefix = "invariantGeneration.kInduction.seahorn")
public class SeahornInvariantGenerator implements ExternalInvariantGenerator {

  private static final String PATH_TO_SCRIPTS =
      "src/org/sosy_lab/cpachecker/core/algorithm/invariants/invariantimport/scripts/";

  @Option(
    secure = true,
    description = "Path to the directory where the generated files should be stored. by default we use the /output dir")
  private String pathToOutDir = "output/";
  private static final int OFFSET = 0;
  private File witnessFile;

  static final Level LOG_LEVEL = Level.ALL;

  private final String PATH_TO_CPA_DIR;

  public SeahornInvariantGenerator(Configuration pConfiguration)
      throws InvalidConfigurationException {
    // set the output directory to the directory used by the cpa checker
    pConfiguration.inject(this);
    witnessFile = new File("proofWitness_Seahorn.graphml");
    PATH_TO_CPA_DIR =
        SeahornInvariantGenerator.class.getProtectionDomain()
            .getCodeSource()
            .getLocation()
            .getPath() + "../";

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
    try {
      witnessFile.createNewFile();
      // Start Seahorn:
      List<Path> sourceFiles = pCfa.getFileNames();
      if (sourceFiles.size() != 1) {
        throw new CPAException("Can onyl handle CFAs, where one source file is contained");
      }
      Multimap<Integer, Pair<String, String>> genINvs =
          genInvsAndLoad(sourceFiles.get(0), pCfa, pLogger);
      pLogger.log(LOG_LEVEL, "Generated %d many invariants via seahorn", genINvs.entries().size());



      InvariantsInC2WitnessTransformer transformer = new InvariantsInC2WitnessTransformer();
      transformer
          .transform(
              genINvs,
              witnessFile,
              pCfa,
              pSpecification,
              sourceFiles.get(0).toFile(),
              pLogger);
      return witnessFile;
    } catch (TransformerException | ParserConfigurationException | IOException
        | InterruptedException e) {
      // throw new CPAException(getMessage() + System.lineSeparator() + e.toString(), e);
      throw new IllegalArgumentException(e);
    }
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

      BufferedReader br;
      try {
        br = new BufferedReader(new FileReader(tempFile));
        String line;
        while ((line = br.readLine()) != null) {
          System.out.println(line);
        }
      } catch (IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }

      System.out.println();
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

  private Multimap<Integer, Pair<String, String>>
      genInvsAndLoad(Path pPath, CFA pCfa, LogManager pLogger)
      throws IOException, InterruptedException {

    ProcessBuilder builder = new ProcessBuilder().inheritIO();
    String absolutePathToInvFile = PATH_TO_CPA_DIR + pathToOutDir;
    pLogger.log(LOG_LEVEL, "Storing generated inv file at files at " + absolutePathToInvFile);

    /**
     * # Usage of the script:: # $1 = path to the file to generate invariant for # $2 = path to the
     * output directory to store generated invariants to # $3 = path to the dir where the scripts
     * are located
     */
    builder.command(
        PATH_TO_CPA_DIR + PATH_TO_SCRIPTS + "compute_invariants_with_seahorn.sh",
        pPath.toFile().getAbsolutePath(),
        absolutePathToInvFile,
        PATH_TO_CPA_DIR + PATH_TO_SCRIPTS);
    Process process = builder.start();

    int exitCode = process.waitFor();
    // After finishing the invariant generation script ensure that everything worked out as planned!
    assert exitCode == 0;
    return parseInvFile(absolutePathToInvFile + "invars_in_c.txt", pCfa);
  }

  /**
   *
   * computes mapping from seahorn invariants to c code lines
   *
   *
   * @param pPathToInvFile the path to the invariant file
   * @param pCfa the cfa of the program
   * @return a multimap, where the first parameter is the line number, the second one a string of
   *         the source code and the third a string with the c invariant
   */
  @SuppressWarnings("resource")
  private Multimap<Integer, Pair<String, String>>
      parseInvFile(String pPathToInvFile, @SuppressWarnings("unused") CFA pCfa) {
    BufferedReader reader = null;
    Multimap<Integer, Pair<String, String>> invs = ArrayListMultimap.create();
    try {
      reader = Files.newBufferedReader(Paths.get(pPathToInvFile), Charset.defaultCharset());
      String line = reader.readLine();
      // Skip the first line
      try {

        // Writer fw =
        // Files.newBufferedWriter(
        // Paths.get("/home/jfh/Documents/seahorn/generatedINvariants.txt"),
        // Charset.defaultCharset(),
        // StandardOpenOption.APPEND);
        // PrintWriter out = new PrintWriter(fw);

        // out.println(pCfa.getFileNames().get(0) + ":");

        while ((line = reader.readLine()) != null) {
          if (line.indexOf(",") == -1) {
            if (line.startsWith("main@entry")
                || line.startsWith("main@verifier.error.split")
                || line.startsWith("main@")) {
              // Cannot parse these invariants (true or false, hence ignore it)
              reader.readLine();
            } else {
              throw new IllegalArgumentException(
                  "The file was not parsed as expected, the line "
                      + line
                      + "does nto have the format 'Linenumber , sourcecode");
            }
          } else {
            int lineNumber = Integer.parseInt(line.substring(0, line.indexOf(",")));
            // +1 to ignore the ','
            String code = line.substring(line.indexOf(",") + 1);
            String inv = reader.readLine();
            // FIXME: Find elegant solution:
            if (inv.contains("(n>=0) && ")) {
              inv = inv.replace("(n>=0) && ", "");
            }
            invs.put(lineNumber - OFFSET, Pair.of(code, inv));

            // out.println(code + " <-->" + inv);

          }
        }
        reader.close();
        // Store the generated invariant for later evaluations

        // out.flush();
        // out.close();
      } catch (IOException e) {
        throw new IllegalArgumentException(e);
      }

    } catch (IOException e) {
      // TOO enhance error logging
      throw new IllegalArgumentException(e);
    }

    return invs;
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
  public Supplier<Path> getSupplierGeneratingInvarian(
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
          return
              generateInvariant(
                  pCfa,
                  pTargetNodesToGenerateFor,
                  pSpecification,
                  pLogger,
                  pShutdownManager,
              pConfig).toPath();
        } catch (CPAException e) {
          throw new RuntimeException(e.toString());
        }
      }
    };
  }

}
