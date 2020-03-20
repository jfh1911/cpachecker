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
package org.sosy_lab.cpachecker.cpa.extinvgen;

import com.google.common.base.Throwables;
import com.google.common.collect.Multimap;
import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.InvariantInC2WitnessParser;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.SeahornInvariantGenerator;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;

public class SeahornInvToARGCPA extends ExternalInvToARGCPA {
  SeahornInvariantGenerator generator;

  /**
   * Gets a factory for creating InvariantCPAs.
   *
   * @return a factory for creating InvariantCPAs.
   */
  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(SeahornInvToARGCPA.class);
  }

  public SeahornInvToARGCPA(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      CFA pCfa,
      Specification pSpecification)
      throws CPAException {
    super(pConfig, pLogger, pShutdownNotifier, pCfa, pSpecification);
    try {
      List<Path> sourceFiles = pCfa.getFileNames();
      if (sourceFiles.size() != 1) {
        throw new CPAException("Can onyl handle CFAs, where one source file is contained");
      }
      generator = new SeahornInvariantGenerator(pConfig);
      Multimap<Integer, Pair<String, String>> mapping =
          generator.genInvsAndLoad(sourceFiles.get(0), pCfa, pLogger);
      super.injectAndParseInvariants(mapping);

    } catch (IOException | InterruptedException | InvalidConfigurationException e) {
      pLogger.log(InvariantInC2WitnessParser.LOG_LEVEL, Throwables.getStackTraceAsString(e));
      throw new CPAException("Could not read file or interruped", e);

    }
  }

}
