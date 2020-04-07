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

import java.io.File;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.function.Supplier;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.extTools.SeahornInvariantGenerationWrapper;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public interface ExternalInvariantGenerator {

  /**
   *
   * @param pCfa of the program
   * @return A set of candidate invariants generated and verified
   * @throws CPAException If the CFA contains more than one source file or to wrap different
   *         exceptions
   */
  Set<CandidateInvariant> generateInvariantAndLoad(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig)
      throws CPAException;

  /**
   *
   * @param pCfa of the program
   * @return the file containing the invariants
   * @throws CPAException If the CFA contains more than one source file or to wrap different
   *         exceptions
   */
  File generateInvariant(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig)
      throws CPAException;

  /**
   *
   * @param pCfa of the program
   * @return the path to the file containing the invariants
   * @throws CPAException If the CFA contains more than one source file or to wrap different
   *         exceptions
   */
  public Callable<Path> getCallableGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig)
      throws CPAException;

  /**
   *
   * @param pCfa of the program
   * @return the path to the file containing the invariants
   * @throws CPAException If the CFA contains more than one source file or to wrap different
   *         exceptions
   */
  Supplier<Path> getSupplierGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig)
      throws CPAException;

  static ExternalInvariantGenerator
      getInstance(ExternalInvariantGenerators instance, Configuration pConfiguration)
          throws InvalidConfigurationException {
    switch (instance) {
      case ULTIMATEAUTOMIZER:
        return new UAInvariantGenerator(pConfiguration);
      case VERIABS:
        return new VeriAbsInvariantGenerator(pConfiguration);
      case SEAHORN:
      default:
        return new SeahornInvariantGenerationWrapper(pConfiguration);

    }
  }
}