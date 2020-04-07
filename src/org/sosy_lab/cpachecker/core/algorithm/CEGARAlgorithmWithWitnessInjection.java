/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.core.algorithm;

import static com.google.common.base.Verify.verifyNotNull;

import com.google.common.util.concurrent.ListenableFuture;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.ClassOption;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.WitnessInjectable;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.value.refiner.UnsoundRefiner;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class CEGARAlgorithmWithWitnessInjection extends CEGARAlgorithm {

  @Options(prefix = "cegar")
  public static class CEGARAlgorithmFactoryWithInjection implements AlgorithmFactory {

    @Option(
      secure = true,
      name = "refiner",
      required = true,
      description = "Which refinement algorithm to use? "
          + "(give class name, required for CEGAR) If the package name starts with "
          + "'org.sosy_lab.cpachecker.', this prefix can be omitted.")
    @ClassOption(packagePrefix = "org.sosy_lab.cpachecker")
    private Refiner.Factory refinerFactory;

    @Option(
      secure = true,
      name = "globalRefinement",
      description = "Whether to do refinement immediately after finding an error state, or globally after the ARG has been unrolled completely.")
    private boolean globalRefinement = false;

    /*
     * Widely used in CPALockator, as there are many error paths, and refinement all of them takes
     * too much time, so, limit refinement iterations and remove at least some infeasible paths
     */
    @Option(
      name = "maxIterations",
      description = "Max number of refinement iterations, -1 for no limit")
    private int maxRefinementNum = -1;

    private final AlgorithmFactory algorithmFactory;
    private final LogManager logger;
    private final Refiner refiner;
    @Nullable
    private List<ListenableFuture<Path>> pathToWitnesses;

    public CEGARAlgorithmFactoryWithInjection(
        Algorithm pAlgorithm,
        ConfigurableProgramAnalysis pCpa,
        LogManager pLogger,
        Configuration pConfig,
        ShutdownNotifier pShutdownNotifier,
        @Nullable List<ListenableFuture<Path>> pPathToWitnesses)
        throws InvalidConfigurationException {
      this(() -> pAlgorithm, pCpa, pLogger, pConfig, pShutdownNotifier, pPathToWitnesses);
    }

    public CEGARAlgorithmFactoryWithInjection(
        AlgorithmFactory pAlgorithmFactory,
        ConfigurableProgramAnalysis pCpa,
        LogManager pLogger,
        Configuration pConfig,
        ShutdownNotifier pShutdownNotifier,
        @Nullable List<ListenableFuture<Path>> pPathToWitnesses)
        throws InvalidConfigurationException {
      pConfig.inject(this);
      algorithmFactory = pAlgorithmFactory;
      logger = pLogger;
      verifyNotNull(refinerFactory);
      refiner = refinerFactory.create(pCpa, pLogger, pShutdownNotifier);
      pathToWitnesses = pPathToWitnesses;

    }

    @Override
    public CEGARAlgorithmWithWitnessInjection newInstance() {
      return new CEGARAlgorithmWithWitnessInjection(
          algorithmFactory.newInstance(),
          refiner,
          logger,
          globalRefinement,
          maxRefinementNum,
          pathToWitnesses);
    }
  }

  private final List<ListenableFuture<Path>> helperFutures;
  private int numInjectedWitnesses = 0;

  /**
   * This constructor gets a Refiner object instead of generating it from the refiner parameter.
   *
   *
   *
   */
  private CEGARAlgorithmWithWitnessInjection(
      Algorithm pAlgorithm,
      Refiner pRefiner,
      LogManager pLogger,
      boolean pGlobalRefinement,
      int pMaxRefinementNum,
      @Nullable List<ListenableFuture<Path>> pPathToWitnesses) {
    super(pAlgorithm, pRefiner, pLogger, pGlobalRefinement, pMaxRefinementNum);
    this.helperFutures = pPathToWitnesses;

  }

  @Override
  public AlgorithmStatus run(ReachedSet reached) throws CPAException, InterruptedException {
    AlgorithmStatus status = AlgorithmStatus.SOUND_AND_PRECISE;

    boolean refinedInPreviousIteration = false;
    super.stats.totalTimer.start();
    try {
      boolean refinementSuccessful;
      do {
        refinementSuccessful = false;
        AbstractState previousLastState = reached.getLastState();

        // if additional invariant generators are used, check if a new witness is generated:

        if (algorithm instanceof WitnessInjectable) {
          while (numInjectedWitnesses < helperFutures.size()
              && helperFutures.get(numInjectedWitnesses).isDone()) {

            // inject the witnesses
            Path pathToInvariant = null;
            try {
              pathToInvariant = helperFutures.get(numInjectedWitnesses).get();
              logger.log(
                  Level.INFO,
                  "Injecting witneeses from path ",
                  pathToInvariant,
                  "for tool ",
                  helperFutures.get(numInjectedWitnesses).toString());
              if (pathToInvariant != null) {
                ((WitnessInjectable) algorithm).inject(reached, pathToInvariant);
              }
            } catch (InterruptedException | ExecutionException e) {
              logger.log(
                  Level.WARNING,
                  "a problem occured while injecting witnesses from  ",
                  helperFutures.get(numInjectedWitnesses).toString());
            }

            // increase number of injected witnesses
            numInjectedWitnesses = numInjectedWitnesses + 1;
          }
        }
        // run algorithm
        status = status.update(algorithm.run(reached));
        notifyReachedSetUpdateListeners(reached);

        if (stats.countRefinements == maxRefinementNum) {
          logger.log(
              Level.WARNING,
              "Aborting analysis because maximum number of refinements "
                  + maxRefinementNum
                  + " used");
          status = status.withPrecise(false);
          break;
        }

        // if there is any target state do refinement
        if (refinementNecessary(reached, previousLastState)) {
          refinementSuccessful = refine(reached);
          refinedInPreviousIteration = true;
          // Note, with special options reached set still contains violated properties
          // i.e (stopAfterError = true) or race conditions analysis
        }

        // restart exploration for unsound refiners, as due to unsound refinement
        // a sound over-approximation has to be found for proving safety
        else if (mRefiner instanceof UnsoundRefiner) {
          if (!refinedInPreviousIteration) {
            break;
          }

          ((UnsoundRefiner) mRefiner).forceRestart(reached);
          refinementSuccessful = true;
          refinedInPreviousIteration = false;
        }

      } while (refinementSuccessful);

    } finally {
      stats.totalTimer.stop();
    }
    return status;
  }

}
