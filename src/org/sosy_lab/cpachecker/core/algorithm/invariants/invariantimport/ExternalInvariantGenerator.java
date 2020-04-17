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
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.function.Supplier;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.ExpressionTreeCandidateInvariant;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.extTools.SeahornInvariantGenerationWrapper;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.extTools.UAInvariantGenerator;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.extTools.VeriAbsInvariantGenerator;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTrees;

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
      Configuration pConfig,
      int pTimeout)
      throws CPAException;



  /**
   *
   * @param pCfa of the program
   * @return the path to the file containing the invariants
   */
  public Callable<InvGenCompRes> getCallableGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig,
      int pTimeout);

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
      Configuration pConfig,
      int pTimeout)
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

  public default boolean checkIfNonTrivial(
      CFA pCfa,
      Configuration pConfig,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Path pRes) {
    boolean nonTrivialFound = false;
    try {

      final Set<CandidateInvariant> candidates = new LinkedHashSet<>();

      final Multimap<String, CFANode> candidateGroupLocations = HashMultimap.create();

      try {
        @SuppressWarnings("resource")
        BufferedReader reader = Files.newBufferedReader(pRes, Charset.defaultCharset());
        String line;
        String witness = "";
        while ((line = reader.readLine()) != null) {
          witness = witness.concat(System.lineSeparator() + line);
        }
        pLogger.log(Level.INFO, "The generated witness is ", witness);
        reader.close();
      } catch (IOException e) {
        // Nothing do to here, since only for debugging purposes
      }

      WitnessInvariantsExtractor extractor =
          new WitnessInvariantsExtractor(
              pConfig,
              pSpecification,
              pLogger,
              pCfa,
              pShutdownNotifier,
              pRes);
      extractor.extractCandidatesFromReachedSet(candidates, candidateGroupLocations);

      for (CandidateInvariant inv : candidates) {
        if (inv instanceof ExpressionTreeCandidateInvariant) {
          ExpressionTree<Object> tree = ((ExpressionTreeCandidateInvariant) inv).asExpressionTree();
          if (!tree.equals(ExpressionTrees.getFalse()) && !tree.equals(ExpressionTrees.getTrue())) {
            // it thee invariant in neither true nor false it is not trivial
            nonTrivialFound = true;
            return nonTrivialFound;
          }
        }
      }

    } catch (InvalidConfigurationException | InterruptedException | CPAException e) {
      pLogger.log(
          Level.WARNING,
          "An error orrucred while loading the genrated invariants. Asusming that only trivial invariants are genrated");
      return false;
    }
    return nonTrivialFound;
  }

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
      ShutdownNotifier pShutdownNotifier,
      Configuration pConfig,
      int pTimeout)
      throws CPAException;
}
