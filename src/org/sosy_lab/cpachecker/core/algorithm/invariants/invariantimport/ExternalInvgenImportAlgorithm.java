/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2017  Dirk Beyer
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
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.util.concurrent.MoreExecutors.listeningDecorator;
import static java.util.concurrent.Executors.newFixedThreadPool;

import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableSet;
import com.google.common.util.concurrent.Futures;
import com.google.common.util.concurrent.ListenableFuture;
import com.google.common.util.concurrent.ListeningExecutorService;
import java.io.IOException;
import java.nio.channels.ClosedByInterruptException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.algorithm.NestingAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.ParallelAlgorithm.ParallelAnalysisResult;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.reachedset.AggregatedReachedSets;
import org.sosy_lab.cpachecker.core.reachedset.AggregatedReachedSets.AggregatedReachedSetManager;
import org.sosy_lab.cpachecker.core.reachedset.ForwardingReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.exceptions.CPAEnabledAnalysisPropertyViolationException;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CounterexampleAnalysisFailed;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CPAs;
import org.sosy_lab.cpachecker.util.Triple;

@Options(prefix = "coverisinv")
public class ExternalInvgenImportAlgorithm extends NestingAlgorithm {

  @Option(secure = true, description = "Timeout for invariant generation in seconds")
  public int timeoutForInvariantExecution = -1;

  @Option(
    secure = true,
    description = "Define, if a external invariant generation tool should be called in the initale step.")
  public List<ExternalInvariantGenerators> extInvGens = null;

  @Option(
    secure = true,
    description = "If one do not wnat to start imediatly with the invariant generation.")
  public int startInvariantExecutionTimer = -1;

  @Option(secure = true, required = true, description = "TODO")
  @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  private Path masterAnalysisconfigFiles;

  private final ShutdownManager shutdown;

  private final Specification spec;

  private ParallelAnalysisResult finalResult = null;
  private Collection<Statistics> stats;

  private Path pathToGeneratedInvar;

  private AggregatedReachedSetManager aggregatedReachedSetManager;
  protected static final int NUM_OF_THREATS_NEEDED = 2;

  Triple<Algorithm, ConfigurableProgramAnalysis, ReachedSet> master;
  ExternalInvariantProvider provider;

  private @Nullable CFANode mainEntryNode;
  ShutdownManager masterShutdownManager;
  ShutdownManager slaveShutdownManager;

  public ExternalInvgenImportAlgorithm(
      final Configuration pConfig,
      final LogManager pLogger,
      final ShutdownNotifier pShutdownNotifier,
      final Specification pSpecification,
      final CFA pCfa,
      AggregatedReachedSets pAggregatedReachedSets)
      throws InvalidConfigurationException, CPAException, InterruptedException {
    super(pConfig, pLogger, pShutdownNotifier, pSpecification, pCfa);
    pConfig.inject(this);
    if (extInvGens == null) {
      extInvGens = new ArrayList<>();
    }
    pLogger.log(Level.WARNING, extInvGens.toString());

    // logger = pLogger;
    shutdown = ShutdownManager.createWithParent(checkNotNull(pShutdownNotifier));
    spec = checkNotNull(pSpecification);
    // cfa = checkNotNull(pCfa);

    // globalConfig = pConfig;
    aggregatedReachedSetManager = new AggregatedReachedSetManager();
    aggregatedReachedSetManager.addAggregated(pAggregatedReachedSets);

    masterShutdownManager = ShutdownManager.createWithParent(shutdownNotifier);
    slaveShutdownManager = ShutdownManager.createWithParent(shutdownNotifier);
    stats = new HashSet<>();

    // Firstly, initialize the master analysis:
    try {
      master =
          super.createAlgorithm(
              masterAnalysisconfigFiles,
              cfa.getMainFunction(),
              masterShutdownManager,
              aggregatedReachedSetManager.asView(),
              ImmutableSet.of("analysis.generateExternalInvariants"),
              stats);
    } catch (InvalidConfigurationException e) {
      logger.log(
          Level.WARNING,
          Throwables.getStackTraceAsString(e),
          "Skipping SelectionAlgorithm because the configuration file "
              + masterAnalysisconfigFiles.toString()
              + " is invalid");

    } catch (IOException e) {
      String message =
          "Skipping SelectionAlgorithm because the configuration file "
              + masterAnalysisconfigFiles.toString()
              + " could not be read";
      if (shutdownNotifier.shouldShutdown() && e instanceof ClosedByInterruptException) {
        logger.log(Level.WARNING, message);
      } else {
        logger.logUserException(Level.WARNING, e, message);
      }
    }
    // Than, initalize the invariant generation analysis

    provider =
        new ExternalInvariantProvider(
            globalConfig,
            logger,
            cfa,
            spec,
            slaveShutdownManager,
            timeoutForInvariantExecution,
            startInvariantExecutionTimer,
            extInvGens);

  }

  @Override
  public AlgorithmStatus run(ReachedSet pReachedSet) throws CPAException, InterruptedException {

    mainEntryNode = AbstractStates.extractLocation(pReachedSet.getFirstState());

    ForwardingReachedSet forwardingReachedSet = (ForwardingReachedSet) pReachedSet;

    ListeningExecutorService exec = listeningDecorator(newFixedThreadPool(NUM_OF_THREATS_NEEDED));

    AtomicBoolean terminateInvGen = new AtomicBoolean(false);

    Callable<ParallelInvGenResult> masterRunner = new Callable<>() {
      @Override
      public ParallelInvGenResult call() throws Exception {

        try {
          AbstractState initialState =
              master.getSecond()
                  .getInitialState(mainEntryNode, StateSpacePartition.getDefaultPartition());
          Precision initialPrecision =
              master.getSecond()
                  .getInitialPrecision(mainEntryNode, StateSpacePartition.getDefaultPartition());
          master.getThird().add(initialState, initialPrecision);
        } catch (InterruptedException e) {
          logger.logUserException(
              Level.INFO,
              e,
              "Initializing reached set took too long, analysis cannot be started");
          // terminated.set(true);
          return new ParallelInvGenResult();
        }

        AlgorithmStatus result = master.getFirst().run(master.getThird());
        // terminated.set(true);
        return new ParallelInvGenResult(result, master.getThird());

      }
    };

    Callable<ParallelInvGenResult> invGenRunner = new Callable<>() {

      @Override
      public ParallelInvGenResult call() throws Exception {
        provider.start(terminateInvGen);
        if (provider.hasComputedInvariants()) {
          // terminated.set(true);
          logger.log(Level.WARNING, "The invariant generation finished successfully");
          return new ParallelInvGenResult(provider.getFirstComputedPath());
        } else {
          logger.log(Level.WARNING, "No invariants were generated!");
          return new ParallelInvGenResult();
        }
      }
    };
    List<ListenableFuture<ParallelInvGenResult>> futures = new ArrayList<>(NUM_OF_THREATS_NEEDED);

    futures.add(exec.submit(masterRunner));
    futures.add(exec.submit(invGenRunner));

    // shutdown the executor service,
    exec.shutdown();

    try {
      handleFutureResults(futures, terminateInvGen);

    } finally {
      // Wait some time so that all threads are shut down and we have a happens-before relation
      // (necessary for statistics).
      if (!awaitTermination(exec, 10, TimeUnit.SECONDS)) {
        logger.log(Level.WARNING, "Not all threads are terminated although we have a result.");
      }
      exec.shutdownNow();
    }

    if (finalResult != null) {
      forwardingReachedSet.setDelegate(finalResult.getReached());
      return finalResult.getStatus();
    }

    // restart with generated invaraints
    shutdown.getNotifier().shutdownIfNecessary();
    try {
      retryWithGeneratedInvariants(pathToGeneratedInvar, shutdown, forwardingReachedSet);
      if (finalResult != null) {
        forwardingReachedSet.setDelegate(finalResult.getReached());
        return finalResult.getStatus();
      }
    } catch (CPAException | InterruptedException | InvalidConfigurationException | IOException e) {
      logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
    }

    return AlgorithmStatus.UNSOUND_AND_PRECISE;
  }

  private void handleFutureResults(
      List<ListenableFuture<ParallelInvGenResult>> futures,
      AtomicBoolean pTerminateInvGen)
      throws InterruptedException, Error {

    try {
      ListenableFuture<ParallelInvGenResult> f = Futures.inCompletionOrder(futures).get(0);
      ParallelInvGenResult result = f.get();
      if (result.isAnalysis) {
        pTerminateInvGen.getAndSet(true);
        // Wair for a second to let the analysis termiante if it is still sleeping
        try {
          TimeUnit.SECONDS.sleep(1);
        } catch (InterruptedException e) {
          logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
        }
        Futures.inCompletionOrder(futures).get(1).cancel(true);
        finalResult = ParallelAnalysisResult.of(result.reachedSet, result.getResult(), "");
      }

      else {
        // Only, if the provider has generated invariants, abort the parallel analysis and restart
        // them
        try {

          if (result.isTimeout) {

            // wait until the analysis is finished or timeout
            ParallelInvGenResult finalRes = Futures.inCompletionOrder(futures).get(1).get();
            ParallelAnalysisResult.of(finalRes.reachedSet, finalRes.getResult(), "");
            // return analysisRes.get().result;
          } else {
            // Stop the master analysis
            masterShutdownManager.requestShutdown("Invariant generation is finished");
            CPAs.closeCpaIfPossible(master.getSecond(), logger);

            CPAs.closeIfPossible(master.getFirst(), logger);

            logger.log(Level.INFO, "Restarting the master analysis");
            // store the generated invariants for later use

            pathToGeneratedInvar = result.getPathToInvariant();

          }
        } catch (InterruptedException | ExecutionException e) {
          logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
          // return AlgorithmStatus.NO_PROPERTY_CHECKED;
        }

      }

    } catch (ExecutionException e) {
      Throwable cause = e.getCause();
      if (cause instanceof CPAException) {
        if (cause.getMessage().contains("recursion")) {
          logger.logUserException(Level.WARNING, cause, "Analysis not completed due to recursion");
        }
        if (cause.getMessage().contains("pthread_create")) {
          logger
              .logUserException(Level.WARNING, cause, "Analysis not completed due to concurrency");
        }

      } else {
        // cancel other computations
        futures.forEach(future -> future.cancel(true));
        shutdown.requestShutdown("cancelling all remaining analyses");
        Throwables.throwIfUnchecked(cause);
        // probably we need to handle IOException, ParserException,
        // InvalidConfigurationException, and InterruptedException here (#326)
        throw new UnexpectedCheckedException("analysis", cause);
      }
      // do nothing, this is normal if we cancel other analyses
    }
  }

  private static boolean
      awaitTermination(ListeningExecutorService exec, long timeout, TimeUnit unit) {
    long timeoutNanos = unit.toNanos(timeout);
    long endNanos = System.nanoTime() + timeoutNanos;

    boolean interrupted = Thread.interrupted();
    try {
      while (true) {
        try {
          return exec.awaitTermination(timeoutNanos, TimeUnit.NANOSECONDS);
        } catch (InterruptedException e) {
          interrupted = false;
          timeoutNanos = Math.max(0, endNanos - System.nanoTime());
        }
      }
    } finally {
      if (interrupted) {
        Thread.currentThread().interrupt();
      }
    }
  }

  private void retryWithGeneratedInvariants(
      Path pPathToInvariant,
      ShutdownManager singleShutdownManager,
      ForwardingReachedSet pForwardingReachedSet)
      throws CPAEnabledAnalysisPropertyViolationException, CPAException, InterruptedException,
      InvalidConfigurationException, IOException {

    Algorithm currentAlgorithm;
    // ConfigurableProgramAnalysis currentCpa;
    ReachedSet currentReached = null;

    // Update the configuration
    try {
      Configuration singleConfig = super.buildSubConfig(masterAnalysisconfigFiles, new HashSet<>());
      ConfigurationBuilder builder = Configuration.builder();

      builder.copyFrom(singleConfig);
      builder.setOption(
          "invariantGeneration.kInduction.invariantsAutomatonFile",
          pPathToInvariant.toString());
      builder.setOption("cpa.predicate.abstraction.initialPredicates", pPathToInvariant.toString());
      builder.setOption("analysis.generateExternalInvariants", "false");
      // builder.setOption("analysis.generateExternalInvariants", "false");

      Configuration newConfig = builder.build();

      Triple<Algorithm, ConfigurableProgramAnalysis, ReachedSet> restartAlg =
          super.createAlgorithm(
              newConfig,
              masterAnalysisconfigFiles.toString(),
              mainEntryNode,
              singleShutdownManager,
              new AggregatedReachedSets(),
              stats);

      currentAlgorithm = restartAlg.getFirst();
      // currentCpa = restartAlg.getSecond();
      currentReached = restartAlg.getThird();

    } catch (InvalidConfigurationException e) {
      logger.logUserException(
          Level.WARNING,
          e,
          "Skipping one analysis because the configuration file "
              + masterAnalysisconfigFiles.toString()
              + " is invalid");
      throw e;
    } catch (IOException e) {
      String message =
          "Skipping one analysis because the configuration file "
              + masterAnalysisconfigFiles.toString()
              + " could not be read";
      if (shutdownNotifier.shouldShutdown() && e instanceof ClosedByInterruptException) {
        logger.log(Level.WARNING, message);
      } else {
        logger.logUserException(Level.WARNING, e, message);
      }
      throw e;
    }
    pForwardingReachedSet.setDelegate(currentReached);

    AlgorithmStatus status = null;
    try {
      logger.log(Level.INFO, "Re-Starting analysis  ...");
      status = currentAlgorithm.run(currentReached);

      if (currentReached.hasViolatedProperties() && status.isPrecise()) {

        // If the algorithm is not _precise_, verdict "false" actually means "unknown".
        // another algorithm, continue with the next algorithm
        logger.log(Level.INFO, "Analysis  terminated, with violation.");
        this.finalResult = ParallelAnalysisResult.of(currentReached, status, "");
        this.finalResult = ParallelAnalysisResult.of(currentReached, status, "");
      }

      if (!status.isSound()) {
        // if the analysis is not sound and we can proceed with
        // another algorithm, continue with the next algorithm
        logger.log(Level.INFO, "Analysis  terminated, but result is unsound.");
        this.finalResult = ParallelAnalysisResult.of(currentReached, status, "");

      } else if (currentReached.hasWaitingState()) {
        // if there are still states in the waitlist, the result is unknown
        // continue with the next algorithm
        logger.log(
            Level.INFO,
            "Analysis   terminated but did not finish: There are still states to be processed.");

      } else {
        logger.log(Level.INFO, "Analysis terminated .");
        this.finalResult = ParallelAnalysisResult.of(currentReached, status, "");

      }

    } catch (CPAException e) {
      if (e instanceof CounterexampleAnalysisFailed || e instanceof RefinementFailedException) {
        // status = status.withPrecise(false);
      }
      logger.log(
          Level.WARNING,
          "Attention: An error occured! Reason:",
          Throwables.getStackTraceAsString(e));
    } catch (InterruptedException e) {
      logger.log(
          Level.WARNING,
          "Attention: the ananlysis was interrupted! Reason:",
          Throwables.getStackTraceAsString(e));
    }

    // final CoreComponentsFactory coreComponents =
    // new CoreComponentsFactory(
    // newConfig,
    // logger,
    // singleShutdownManager.getNotifier(),
    // new AggregatedReachedSets());
    // final ReachedSet reached = coreComponents.createReachedSet();
    // final ConfigurableProgramAnalysis cpa = coreComponents.createCPA(cfa, specification);
    // final Algorithm algorithm = coreComponents.createAlgorithm(cpa, cfa, specification);
    // try {
    // AbstractState initialState =
    // cpa.getInitialState(mainEntryNode, StateSpacePartition.getDefaultPartition());
    // Precision initialPrecision =
    // cpa.getInitialPrecision(mainEntryNode, StateSpacePartition.getDefaultPartition());
    // reached.add(initialState, initialPrecision);
    // AlgorithmStatus res = algorithm.run(reached);
    // finalResult = ParallelAnalysisResult.of(reached, res, "");
    // } catch (InterruptedException e) {
    // logger.logUserException(
    // Level.INFO,
    // e,
    // "Initializing reached set took too long, analysis cannot be started");
    // // terminated.set(true);
    //
    // }

    // CoreComponentsFactory factory =
    // new CoreComponentsFactory(newConfig, logger, shutdownNotifier, new AggregatedReachedSets());

    // Algorithm algorithm = null;
    // ReachedSet reached = null;
    //
    // Result result = Result.NOT_YET_STARTED;
    // String violatedPropertyDescription = "";
    //
    //
    // final ShutdownRequestListener interruptThreadOnShutdown = interruptCurrentThreadOnShutdown();
    // shutdownNotifier.register(interruptThreadOnShutdown);
    //
    // try {
    //
    // reached = factory.createReachedSet();
    //
    //
    //
    // shutdownNotifier.shutdownIfNecessary();
    //
    // ConfigurableProgramAnalysis cpa;
    // try {
    //
    // cpa = factory.createCPA(cfa, spec);
    // } finally {
    //
    // }
    //
    //
    //
    //
    // algorithm = factory.createAlgorithm(cpa, cfa, specification);
    //
    //
    //
    //
    // initializeReachedSet(reached, cpa, new, cfa.getMainFunction(), cfa);
    //
    //
    //
    // printConfigurationWarnings();
    //
    // stats.creationTime.stop();
    // shutdownNotifier.shutdownIfNecessary();
    //
    // // now everything necessary has been instantiated: run analysis
    //
    // result = Result.UNKNOWN; // set to unknown so that the result is correct in case of exception
    //
    // AlgorithmStatus status = runAlgorithm(algorithm, reached, stats);
    //
    //
    // } catch (IOException e) {
    // logger.logUserException(Level.SEVERE, e, "Could not read file");
    //
    // } catch (ParserException e) {
    // logger.logUserException(Level.SEVERE, e, "Parsing failed");
    // StringBuilder msg = new StringBuilder();
    // msg.append("Please make sure that the code can be compiled by a compiler.\n");
    // if (e.getLanguage() == Language.C) {
    // msg.append("If the code was not preprocessed, please use a C preprocessor\nor specify the
    // -preprocess command-line argument.\n");
    // }
    // msg.append("If the error still occurs, please send this error message\ntogether with the
    // input file to cpachecker-users@googlegroups.com.\n");
    // logger.log(Level.INFO, msg);
    //
    // } catch (ClassNotFoundException e) {
    // logger.logUserException(Level.SEVERE, e, "Could not read serialized CFA. Class is missing.");
    //
    // } catch (InvalidConfigurationException e) {
    // logger.logUserException(Level.SEVERE, e, "Invalid configuration");
    //
    // } catch (InterruptedException e) {
    // // CPAchecker must exit because it was asked to
    // // we return normally instead of propagating the exception
    // // so we can return the partial result we have so far
    // logger.logUserException(Level.WARNING, e, "Analysis interrupted");
    //
    // } catch (CPAException e) {
    // logger.logUserException(Level.SEVERE, e, null);
    //
    // } finally {
    // CPAs.closeIfPossible(algorithm, logger);
    // shutdownNotifier.unregister(interruptThreadOnShutdown);
    // }
    // CPAchecker cpachecker = new CPAchecker(newConfig, logger, shutdown);
    // cpachecker.run(
    // cfa.getFileNames()
    // .stream()
    // .map(s -> s.toAbsolutePath().toString())
    // .collect(Collectors.toList()),
    // spec);

  }

  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    // TODO Auto-generated method stub

  }

  public static class ParallelInvGenResult {

    private boolean isAnalysis;
    private boolean isInvGen;
    private boolean isTimeout;
    private AlgorithmStatus result;
    private Path pathToInvariant;
    private ReachedSet reachedSet;

    public ParallelInvGenResult(AlgorithmStatus pResult, ReachedSet pReachedSet) {
      super();
      isAnalysis = true;
      isInvGen = false;
      isTimeout = false;
      result = pResult;
      reachedSet = pReachedSet;
    }

    public ParallelInvGenResult(Path pPathToInvariant) {
      super();
      isAnalysis = false;
      isInvGen = true;
      isTimeout = false;

      pathToInvariant = pPathToInvariant;
    }

    public ParallelInvGenResult() {
      super();
      isAnalysis = false;
      isInvGen = false;
      isTimeout = true;
    }

    public boolean isAnalysis() {
      return isAnalysis;
    }

    public boolean isInvGen() {
      return isInvGen;
    }

    public boolean isTimeout() {
      return isTimeout;
    }

    public AlgorithmStatus getResult() {
      return result;
    }

    public Path getPathToInvariant() {
      return pathToInvariant;
    }

  }

}

// public class AlgorithmRunner {
//
// private ExecutorService executor;
// private Algorithm algorithm;
//
// public AlgorithmRunner(Algorithm pAlgorithm, ExecutorService pExecutor) {
// super();
// algorithm = pAlgorithm;
// executor = pExecutor;
// }
//
// public Future<ParallelInvGenResult> computeResult(ReachedSet pReachedSet) {
// Future<ParallelInvGenResult> res = executor.submit(() -> {
// AlgorithmStatus status = algorithm.run(pReachedSet);
// return new ParallelInvGenResult(status);
// });
// executor.shutdown();
// return res;
// }
// }
//
// public class InvGenRunner {
//
// private ExecutorService executor;
// private ExternalInvariantProvider provider;
//
// public InvGenRunner(ExternalInvariantProvider pProvider, ExecutorService pExecutor) {
// super();
// executor = pExecutor;
// provider = pProvider;
// }
//
// public Callable<ParallelInvGenResult> computeResult() {
//
//
//
// ListenableFuture<ParallelInvGenResult> res = executor.submit(() -> {
// provider.start();
// if (provider.hasComputedInvariants()) {
// return new ParallelInvGenResult(provider.getFirstComputedPath());
// } else {
// return new ParallelInvGenResult();
// }
// });
// return res;
// }
// }

// private Algorithm getMasterAnalysis() {
// Algorithm chosenAlgorithm;
// Triple<Algorithm, ConfigurableProgramAnalysis, ReachedSet> currentAlg;
// ShutdownManager shutdownManager = ShutdownManager.createWithParent(shutdownNotifier);
// try {
// currentAlg = createAlgorithm(chosenConfig, cfa.getMainFunction(), shutdownManager);
// } catch (InvalidConfigurationException e) {
// logger.logUserException(
// Level.WARNING,
// e,
// "Skipping SelectionAlgorithm because the configuration file "
// + chosenConfig.toString()
// + " is invalid");
// return AlgorithmStatus.UNSOUND_AND_PRECISE;
// } catch (IOException e) {
// String message =
// "Skipping SelectionAlgorithm because the configuration file "
// + chosenConfig.toString()
// + " could not be read";
// if (shutdownNotifier.shouldShutdown() && e instanceof ClosedByInterruptException) {
// logger.log(Level.WARNING, message);
// } else {
// logger.logUserException(Level.WARNING, e, message);
// }
// return AlgorithmStatus.UNSOUND_AND_PRECISE;
// }
//
// chosenAlgorithm = currentAlg.getFirst();
// // ConfigurableProgramAnalysis chosenCpa = currentAlg.getSecond();
// ReachedSet reachedSetForChosenAnalysis = currentAlg.getThird();
//
// ForwardingReachedSet reached = (ForwardingReachedSet) pReachedSet;
// reached.setDelegate(reachedSetForChosenAnalysis);
//
// return chosenAlgorithm.run(reachedSetForChosenAnalysis);
// }
