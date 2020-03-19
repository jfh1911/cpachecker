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
import com.google.common.collect.Multimap;
import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.logging.Level;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.util.Pair;

@Options(prefix = "invariantGeneration.kInduction.seahorn")
public class SeahornInvariantGenerator {

  private static final String PATH_TO_SCRIPTS =
      "src/org/sosy_lab/cpachecker/core/algorithm/invariants/invariantimport/scripts/";

  @Option(
    secure = true,
    description = "Path to the directory where the generated files should be stored. by default we use the /output dir")
  private String pathToOutDir = "output/";
  private static final int OFFSET = 0;

  static final Level LOG_LEVEL = Level.ALL;

  private final String PATH_TO_CPA_DIR;

  public SeahornInvariantGenerator(Configuration pConfiguration)
      throws InvalidConfigurationException {
    // set the output directory to the directory used by the cpa checker
    pConfiguration.inject(this);

    PATH_TO_CPA_DIR =
        SeahornInvariantGenerator.class.getProtectionDomain()
            .getCodeSource()
            .getLocation()
            .getPath() + "../";
  }

  /**
   *
   * computes invariants via seahorn and a mapping from seahorn invariants to c code lines
   *
   *
   * @param pPath the path to c file
   * @param pCfa the cfa of the program
   * @param pLogger the logger to use
   * @return a multimap, where the first parameter is the line number, the second one a string of
   *         the source code and the third a string with the c invariant
   */
  public Multimap<Integer, Pair<String, String>>
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

          }
        }
        reader.close();
      } catch (IOException e) {
        throw new IllegalArgumentException(e);
      }

    } catch (IOException e) {
      // TOO enhance error logging
      throw new IllegalArgumentException(e);
    }

    return invs;
  }

}
