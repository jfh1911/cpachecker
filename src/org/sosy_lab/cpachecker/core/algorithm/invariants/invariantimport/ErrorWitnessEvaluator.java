// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.IO;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cpa.automaton.AutomatonGraphmlParser;
import org.sosy_lab.cpachecker.util.automaton.AutomatonGraphmlCommon.WitnessType;

public class ErrorWitnessEvaluator {

  public ErrorWitnessEvaluator(CFA pCfa, LogManager pLogger, ShutdownNotifier pShutdownNotifier) {
    super();
    cfa = pCfa;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
  }

  private CFA cfa;
  private LogManager logger;
  private ShutdownNotifier shutdownNotifier;

  @SuppressWarnings("resource")
  public int determineK(List<Path> pPathToInvariant, Configuration pConfig) {
    List<Path> pathToErrorWitnesses = new ArrayList<>();
    // List<Automaton> lst = new ArrayList<>();
    for (Path path : pPathToInvariant) {
      try {
        IO.checkReadableFile(path);
        if (AutomatonGraphmlParser.isGraphmlAutomatonFromConfiguration(path)
            && AutomatonGraphmlParser.getWitnessType(path) == WitnessType.VIOLATION_WITNESS) {
          pathToErrorWitnesses.add(path);
          // Scope scope =
          // cfa.getLanguage() == Language.C
          // ? new CProgramScope(cfa, logger)
          // : DummyScope.getInstance();
          //
          // lst.addAll(
          // AutomatonParser.parseAutomatonFile(
          // path,
          // pConfig,
          // logger,
          // cfa.getMachineModel(),
          // scope,
          // cfa.getLanguage(),
          // shutdownNotifier));
        }
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Could not read witnesses from file");
      } catch (InvalidConfigurationException | InterruptedException e) {
        logger.log(
            Level.WARNING,
            e,
            "Could not process witness from path ",
            path,
            " hence ignoring it while searching for violation witnesses");
        e.printStackTrace();
      }
    }

    // Collect the scr code lines contianing either "while" or "for"
    Set<Integer> lineNums = new HashSet<>();
    for (CFANode loophead : cfa.getLoopStructure().get().getAllLoopHeads().asList()) {
      for (int i = 0; i < loophead.getNumLeavingEdges(); i++) {
        lineNums.add(loophead.getLeavingEdge(i).getLineNumber());
      }
    }

    logger.log(Level.WARNING, "linesWithLoops are", lineNums.toString());

    // now, Process the automaton
    int maxK = 1;
    for (Path p : pathToErrorWitnesses) {
      int nextk = 1;
    try {
        BufferedReader reader;
        reader =
            new BufferedReader(
                new FileReader(
                    p.toFile(),
                    Charset.defaultCharset()));
        for (String line : reader.lines().toArray(String[]::new)) {
          line = line.trim().strip();
          logger.log(
              Level.INFO,
              ""
                  + line.contains("<data key=\"startline\">")
                  + line.contains("</data>")
                  + "--"
                  + line
                  + "--"
                  + line.strip().trim()
                  +
              "--");
          if (line.contains("<data key=\"startline\">") && line.contains("</data>")) {
            line = line.substring("<data key=\"startline\">)".length() - 1);
            line = line.substring(0, line.indexOf('<')).trim();
            System.out.println(line);
            int lineInt = Integer.valueOf(line);
            if (lineNums.contains(lineInt)) {
              nextk = nextk + 1;
            }
          }

        }
        reader.close();
    } catch (IOException e) {
        logger.log(
            Level.WARNING,
            "Could not determine k for error witness ",
            p,
            " as the file is not readable");
      }
      maxK = Math.max(maxK, nextk);
    }
    logger.log(Level.WARNING, maxK);
    System.err.println(maxK);
    return maxK;
  }

}
