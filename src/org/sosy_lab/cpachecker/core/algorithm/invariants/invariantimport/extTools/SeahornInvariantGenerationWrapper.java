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

import java.io.File;
import java.nio.file.Path;
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
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.ExternalInvariantGenerator;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.ExternalInvariantGenerators;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.InvGenCompRes;
import org.sosy_lab.cpachecker.core.specification.Specification;
import org.sosy_lab.cpachecker.exceptions.CPAException;

@Options(prefix = "invariantGeneration.kInduction.seahorn.wrapper")
public class SeahornInvariantGenerationWrapper implements ExternalInvariantGenerator {

  private File witnessFile;

  static final Level LOG_LEVEL = Level.ALL;

  Configuration config;
  @Option(
    secure = true,
    description = "Path to the config file containing the cpas to generate and load invariants from seahorn")
  @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  private Path configForSeahorn = null;
  // "components/seahornInvGenCPA.properties";
  SeahornInvariantGenerator generator;

  InvariantInC2WitnessParser parser;

  public SeahornInvariantGenerationWrapper(Configuration pConfiguration)
      throws InvalidConfigurationException {
    // set the output directory to the directory used by the cpa checker
    pConfiguration.inject(this);
    witnessFile = new File("proofWitness_Seahorn.graphml");
    config = pConfiguration;

    parser = new InvariantInC2WitnessParser(pConfiguration);
  }

  @Override
  public Set<CandidateInvariant> generateInvariantAndLoad(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig,
      int pTimeout)
      throws CPAException {
    // TODO Implement this
    return null;
  }

  @Override
  public File generateInvariant(
      CFA pCfa,
      @Nullable List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Configuration pConfig,
      int pTimeout)
      throws CPAException {
    return parser.generateInvariant(
        pCfa,
        pSpecification,
        pLogger,
        pShutdownNotifier,
        configForSeahorn,
        witnessFile,
        pTimeout);
  }

  @Override
  public Supplier<Path> getSupplierGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig,
      int pTimeout)
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
                  pConfig,
                  pTimeout).toPath();
          pLogger.log(Level.WARNING, "Invariant generation finished for tool : SeaHorn");
          return res;
        } catch (CPAException e) {
          throw new RuntimeException(e.toString());
        }
      }
    };
  }

  @Override
  public Callable<InvGenCompRes> getCallableGeneratingInvariants(
      CFA pCfa,
      List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownManager,
      Configuration pConfig,
      int pTimeout,
      List<ExternalInvariantGenerators> pExtInvGens,
      boolean pOptimizeForPredicateAbstr) {

    return () -> {
      try {
      Path res =
          generateInvariant(
              pCfa,
              pTargetNodesToGenerateFor,
              pSpecification,
              pLogger,
              pShutdownManager,
                pConfig,
                pTimeout).toPath();
      pLogger.log(Level.WARNING, "Invariant generation finished for tool : SeaHorn");
      if (!checkIfNonTrivial(pCfa, pConfig, pSpecification, pLogger, pShutdownManager, res)) {
        pLogger.log(
            Level.WARNING,
            "The SeaHorn invariant generator only generates trivial invarinats, hence not returning anything");
        return new InvGenCompRes(
            new CPAException(
                "The SeaHorn invariant generator only generates trivial invarinats, hence not returning anything"),
            "SeaHorn");
      }
      return new InvGenCompRes(res, "SeaHorn");
      } catch (CPAException e) {
        return new InvGenCompRes(e, "SeaHorn");
      }
    };
  }

}
