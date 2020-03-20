/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.util.Pair;

public class UALogParser {

  private LogManager logger;

  public UALogParser(LogManager pLogger) {
    super();
    logger = pLogger;
  }

  public Multimap<Integer, Pair<String, String>> parseLog(Path pLog) {
    Multimap<Integer, Pair<String, String>> invMapping = ArrayListMultimap.create();

    // PArse a log from UA to a witness understandable by CPAChecker
    // The log is expected to look like this:
    //
    // * Results from de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction:
    // - PositiveResult [Line: 5]: call of __VERIFIER_error() unreachable
    // For all program executions holds that call of __VERIFIER_error() unreachable at this location
    // - AllSpecificationsHoldResult: All specifications hold
    // 1 specifications checked. All of them hold
    // - InvariantResult [Line: 19]: Loop Invariant
    // Derived loop invariant: i + k + j <= l && l <= i + k + j
    // - InvariantResult [Line: 3]: Loop Invariant
    // Derived loop invariant: 1
    // - InvariantResult [Line: 11]: Loop Invariant
    // Derived loop invariant: 1
    // - StatisticsResult: Ultimate Automizer benchmark data

    try {
      @SuppressWarnings("resource")
      BufferedReader reader = Files.newBufferedReader(pLog, Charset.defaultCharset());
      boolean resultsReached = false;
      String line;

      while ((line = reader.readLine()) != null) {

        if (!resultsReached
            && line.trim().startsWith("* Results from de.uni_freiburg.informatik")) {
          resultsReached = true;
        } else if (resultsReached) {
          if (line.trim().startsWith("- InvariantResult")) {
            String lineNumber =
                line.substring(line.indexOf("[Line: ") + "[Line:".length(), line.indexOf("]"))
                    .trim();

            line = reader.readLine();
            if (line.indexOf("Derived loop invariant: ") > 0) {
              String inv =
                  line.substring(
                      line.lastIndexOf("Derived loop invariant: ")
                          + "Derived loop invariant:".length())
                      .trim();

              while (inv.contains("||")) {
                inv = inv.replace("||", "|");
              }
              while (inv.contains("&&")) {
                inv = inv.replace("&&", "&");
              }
              while (inv.contains("-1 * ")) {
                inv = inv.replace("-1 * ", "-");
              }
              invMapping.put(Integer.parseInt(lineNumber), Pair.of("", inv));
            } else {
              logger.log(
                  Level.INFO,
                  "cannot parse invariant for line ",
                  lineNumber,
                  " which is contained in ",
                  line);
            }
          }
        }
      }

    } catch (IOException e) {
      logger.log(
          Level.WARNING,
          "The file that should contain the invariants from Ultimate is not existing");
    }

    return invMapping;
  }

  // public static void main(String[] args) {
  // UALogParser p = new UALogParser();
  // System.out.println("Starting");
  // File f = new File("/home/cppp/Documents/cpachecker/cpachecker/output/log.txt");
  //
  // Multimap<Integer, Pair<String, String>> m = p.parseLog(f.toPath());
  // System.err.println(m.toString());
  // }
}
