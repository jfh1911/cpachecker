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

import static com.google.common.util.concurrent.MoreExecutors.listeningDecorator;

import com.google.common.base.Throwables;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimap;
import com.google.common.util.concurrent.Futures;
import com.google.common.util.concurrent.ListenableFuture;
import com.google.common.util.concurrent.ListeningExecutorService;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.LockSupport;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.core.reachedset.AggregatedReachedSets;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;

public class ExternalInvariantProvider {
  private boolean isStared;
  private boolean hasFinished;
  private List<Path> computedPath;
  private LogManager logger;
  private CFA cFA;
  private Specification specification;
  private ShutdownManager shutdownManager;
  private Configuration config;
  // private StaticCandidateProvider provider;
  // private Map<CFANode, CandidateInvariant> computedInvariants;
  // private PredicateAbstractionManager predicateManager;
  // private ReachedSet reachedSet;
  private int startInvariantExecutionTimer;
  private int timeoutForInvariantExecution;
  private List<ExternalInvariantGenerators> extInvGens;
  private boolean waitForOthers = false;
  private AtomicBoolean shoudlShutdownTimeout = new AtomicBoolean(false);
  private ImmutableList<ListenableFuture<Path>> futures;

  public ExternalInvariantProvider(
      Configuration pConfig,
      LogManager pLogger,
      CFA pCFA,
      Specification pSpecification,
      ShutdownManager pShutdownManager,
      int pTimeoutForInvariantExecution,
      int pStartInvariantExecutionTimer,
      List<ExternalInvariantGenerators> pExtInvGens,
      boolean pInjectWitnesses) {
    super();
    // options = pOptions;
    computedPath = new ArrayList<>();
    logger = pLogger;
    cFA = pCFA;
    specification = pSpecification;
    shutdownManager = pShutdownManager;
    config = pConfig;
    isStared = false;
    hasFinished = false;
    // reachedSet = pReachedSet;
    startInvariantExecutionTimer = pStartInvariantExecutionTimer;
    timeoutForInvariantExecution = pTimeoutForInvariantExecution;
    extInvGens = pExtInvGens;

    waitForOthers = pInjectWitnesses;

  }

  public boolean start(AtomicBoolean pShouldTerminate) {
    isStared = true;
    if (startInvariantExecutionTimer > 0) {
      try {
        logger.log(Level.INFO, "Sleeping for ", startInvariantExecutionTimer);
        for (int i = 0; i < startInvariantExecutionTimer && !pShouldTerminate.get(); i++) {
          TimeUnit.SECONDS.sleep(1);
        }
        if (pShouldTerminate.get()) {
          hasFinished = true;
          return hasFinished;
        }
      } catch (InterruptedException e) {
        // IF an error occures, we dont do anything and dont generate invariants.
        logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
        hasFinished = false;
        return hasFinished;

      }
    }

    // Check if a timeout is needed
    int initialCapacity = extInvGens.size();
    // + (timeoutForInvariantExecution > 0 ? 1 : 0);
    if (initialCapacity <= 0) {
      logger.log(Level.WARNING, "No invariant generation present, returning 0");
      this.hasFinished = true;
      return hasFinished;
    }

    List<Callable<Path>> suppliers = new ArrayList<>(initialCapacity);
    // if (timeoutForInvariantExecution > 0) {
    // logger.log(
    // Level.INFO,
    // "Setting up a timmer with timeout of seconds:",
    // timeoutForInvariantExecution);
    // // The timeout supplier waits for the specified timeout and return an empty optional
    //
    // Callable<Path> timeoutCallable =
    // getTimeoutcallable(timeoutForInvariantExecution, shoudlShutdownTimeout);
    // suppliers.add(timeoutCallable);
    // }
    ListeningExecutorService exec =
        listeningDecorator(Executors.newFixedThreadPool(initialCapacity));

    // Add all specified invariant generation tools
    for (ExternalInvariantGenerators invGenTool : extInvGens) {
      ExternalInvariantGenerator gen;
      try {
        gen = ExternalInvariantGenerator.getInstance(invGenTool, config);
        suppliers.add(
            gen.getCallableGeneratingInvariants(
                cFA,
                new ArrayList<CFANode>(),
                specification,
                logger,
                shutdownManager.getNotifier(),
                config));
      } catch (InvalidConfigurationException | CPAException e) {
        logger.log(
            Level.INFO,
            "An error occured while setting up the invarant generation tools."
                + "hence Anort the computation and reutnr without invariant",
            Throwables.getStackTraceAsString(e));
        this.hasFinished = true;
        return hasFinished;

      }

    }

    // Start the computation
    futures =
        ImmutableList
            .copyOf(suppliers.stream().map(s -> exec.submit(s)).collect(Collectors.toList()));

    // shutdown the executor service,
    exec.shutdown();

    try {
      handleFutureResults();

    } catch (Exception e) {
      logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
    } finally {
      // Wait some time so that all threads are shut down and we have a happens-before relation
      // (necessary for statistics).
      // if (!awaitTermination(exec, 10, TimeUnit.SECONDS)) {
      // logger.log(Level.WARNING, "Not all threads are terminated, shutting them down now!");
      // }
      // exec.shutdownNow();
    }

    hasFinished = true;
    return hasFinished;
  }

  private void handleFutureResults() {

    // List<CPAException> exceptions = new ArrayList<>();

    ListenableFuture<Path> f = Futures.inCompletionOrder(futures).get(0);

      Path result;
      try {
        if (timeoutForInvariantExecution > 0) {
          result = f.get(timeoutForInvariantExecution, TimeUnit.SECONDS);
        } else {
          result = f.get();
        }
        if (result != null) {
          this.computedPath.add(result);
        }

      } catch (InterruptedException | ExecutionException e) {
        // logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
        futures.parallelStream().forEach(fut -> fut.cancel(true));
        logger.log(Level.WARNING, "One invairant generation failed!");
      } catch (TimeoutException | CancellationException e) {
        logger.log(Level.WARNING, "The invariant generation timed-out!");
        futures.parallelStream().forEach(fut -> fut.cancel(true));
      }


      if (!this.waitForOthers) {
        // Allow the threads, especially the timeout thread some time to shutdown
        shoudlShutdownTimeout.getAndSet(true);
        LockSupport.parkNanos(TimeUnit.SECONDS.toNanos(1));
        logger.log(Level.INFO, "killing other generators");
        futures.parallelStream().forEach(fut -> fut.cancel(true));
      futures.parallelStream()
          .forEach(fut -> System.out.println(fut.isCancelled() || fut.isDone()));
      }


  }

  // private Callable<Path>
  // getTimeoutcallable(int pTimeoutForInvariantExecution, AtomicBoolean shouldShutdown) {
  // return () -> {
  // for (int i = 0; i < pTimeoutForInvariantExecution && !shouldShutdown.get(); i++) {
  // LockSupport.parkNanos(TimeUnit.SECONDS.toNanos(1));
  // }
  // logger.log(Level.WARNING, "The invariant generation timed out!");
  // return null;
  //
  // };
  // }

  public Path getFirstComputedPath() {
    if (hasFinished) {
      if (computedPath.get(0) == null) {
        logger.log(Level.WARNING, "Returning null path for generated witness");
      }
      return computedPath.get(0);
    } else {
      // FIXME: Enhance error handling
      logger.log(Level.WARNING, "No path found!");
      throw new IllegalArgumentException("");
    }
  }

  // private static boolean
  // awaitTermination(ListeningExecutorService exec, long timeout, TimeUnit unit) {
  // long timeoutNanos = unit.toNanos(timeout);
  // long endNanos = System.nanoTime() + timeoutNanos;
  //
  // boolean interrupted = Thread.interrupted();
  // try {
  // while (true) {
  // try {
  // return exec.awaitTermination(timeoutNanos, TimeUnit.NANOSECONDS);
  // } catch (InterruptedException e) {
  // interrupted = false;
  // timeoutNanos = Math.max(0, endNanos - System.nanoTime());
  // }
  // }
  // } finally {
  // if (interrupted) {
  // Thread.currentThread().interrupt();
  // }
  // }
  // }

  public AggregatedReachedSets getReachedSet() throws CPAException {
    if (hasFinished) {
      try {
        Set<CandidateInvariant> candidates = new HashSet<>();
        final Multimap<String, CFANode> candidateGroupLocations = HashMultimap.create();
        if (!computedPath.isEmpty()) {
          WitnessInvariantsExtractor extractor =
              new WitnessInvariantsExtractor(
                  config,
                  specification,
                  logger,
                  cFA,
                  shutdownManager.getNotifier(),
                  computedPath.get(0));

          extractor.extractCandidatesFromReachedSet(candidates, candidateGroupLocations);
          logger
              .log(Level.WARNING, "The following candidates are imported: ", candidates.toString());
          logger.log(
              Level.WARNING,
              "The following candidateGroupLocations are found: ",
              candidateGroupLocations.toString());
        }
        // provider = new StaticCandidateProvider(candidates);

        // generator =
        // KInductionInvariantGenerator.create(
        // config,
        // logger,
        // shutdownManager,
        // cFA,
        // specification,
        // null,
        // provider,
        // true);
        return parseReachedSet();
      } catch (InvalidConfigurationException | CPAException | InterruptedException e) {
        logger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
        throw new CPAException("", e);
      }

    } else {
      // FIXME: Enhance error handling
      throw new IllegalArgumentException("");
    }
  }

  private AggregatedReachedSets parseReachedSet() {
    throw new IllegalStateException("Not implemented yet!");
  }

  public boolean isStared() {
    return isStared;
  }

  public boolean hasFinished() {
    return hasFinished;
  }

  public List<Path> getComputedPath() {
    return computedPath;
  }

  public boolean hasComputedInvariants() {
    return computedPath != null && computedPath.size() > 0;
  }

  List<ListenableFuture<Path>> getFutures() {
    futures.forEach(f -> logger.log(Level.WARNING, f.toString()));
    return this.futures;
  }

}
