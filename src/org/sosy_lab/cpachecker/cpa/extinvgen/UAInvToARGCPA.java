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

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.extTools.UAInvariantGenerator;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.exceptions.CPAException;

@Options(prefix = "coverisinv")
public class UAInvToARGCPA extends ExternalInvToARGCPA {

  @Option(
    secure = true,
    name = "timeoutForInvariantExecution",
    description = "The timeout given to the invariant generators")
  private int pTimeout = -1;

  UAInvariantGenerator generator;

  /**
   * Gets a factory for creating InvariantCPAs.
   *
   * @return a factory for creating InvariantCPAs.
   */
  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(UAInvToARGCPA.class);
  }

  public UAInvToARGCPA(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      CFA pCfa,
      Specification pSpecification)
      throws CPAException, InvalidConfigurationException {
    super(pConfig, pLogger, pShutdownNotifier, pCfa, pSpecification);
    pConfig.inject(this);

    if (pCfa.getFileNames().size() != 1) {
      throw new CPAException("Can onyl handle CFAs, where one source file is contained");
    }
    generator = new UAInvariantGenerator(pConfig);
    super.injectAndParseInvariants(generator.genInvsAndLoad(pCfa, pLogger, pTimeout));

  }

}
