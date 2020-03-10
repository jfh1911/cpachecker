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

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.StaticCandidateProvider;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.core.algorithm.invariants.InvariantSupplier;
import org.sosy_lab.cpachecker.core.algorithm.invariants.KInductionInvariantGenerator;
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
  private StaticCandidateProvider provider;
  private KInductionInvariantGenerator generator;
  // private Map<CFANode, CandidateInvariant> computedInvariants;
  // private PredicateAbstractionManager predicateManager;
  // private ReachedSet reachedSet;
  private int startInvariantExecutionTimer;
  private int timeoutForInvariantExecution;
  private List<ExternalInvariantGenerators> extInvGens;


  public ExternalInvariantProvider(
      Configuration pConfig,
      LogManager pLogger,
      CFA pCFA,
      Specification pSpecification,
      ShutdownManager pShutdownManager,
      int pTimeoutForInvariantExecution,
      int pStartInvariantExecutionTimer,
      List<ExternalInvariantGenerators> pExtInvGens) {
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

  }

  public boolean start() {
    isStared = true;
    if (startInvariantExecutionTimer > 0) {
      try {
        TimeUnit.SECONDS.sleep(startInvariantExecutionTimer);
        logger.log(Level.INFO, "Sleeping for ", startInvariantExecutionTimer);
      } catch (InterruptedException e) {
        // IF an error occures, we dont do anything and dont generate invariants.
        logger.log(
            Level.WARNING,
            "External invariant generation failed! Could not wait due to ",
            e.toString());
        hasFinished = true;
        return hasFinished;

      }
    }

    ExternalInvariantGenerator gen;
    File invariantsAutomatonFile = null;

    try {
      gen = ExternalInvariantGenerator.getInstance(extInvGens.get(0), config);
      invariantsAutomatonFile =
          gen.generateInvariant(
              cFA,
              new ArrayList<CFANode>(),
              specification,
              logger,
              shutdownManager.getNotifier(),
              config);
    } catch (CPAException | InvalidConfigurationException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }
    // Start the computation

    if (invariantsAutomatonFile == null) {
      logger.log(
          Level.WARNING,
          "None of the tools generated an invariant in ",
          timeoutForInvariantExecution,
          " seconds or an error occured. Hence continuing without invariant");
    } else {
      // FIXME: just for tests: print the generated invariant
      BufferedReader reader;
        try {
        String fileContent = "";
        reader =
            Files.newBufferedReader(
                invariantsAutomatonFile.toPath(),
                Charset.defaultCharset());
        String line;
        while ((line = reader.readLine()) != null) {
          fileContent = fileContent.concat(line);
        }
        reader.close();

        logger.log(Level.WARNING, fileContent);
        computedPath.add(invariantsAutomatonFile.toPath());
      } catch (IOException e) {
        logger.log(Level.WARNING, "Cannot print the file");
        }
      }

    // //FIXME: For tests
    // // Check if the external invariant generation needs to be called
    //
    // List<Supplier<Path>> suppliers = new ArrayList<>();
    // if (timeoutForInvariantExecution > 0) {
    // logger.log(
    // Level.INFO,
    // "Setting up a timmer with timeout of seconds:",
    // timeoutForInvariantExecution);
    // // The timeout supplier waits for the specified timeout and return an empty optional
    // Supplier<Path> timeoutSupplier = new Supplier<>() {
    //
    // @Override
    // public Path get() {
    // LockSupport.parkNanos(TimeUnit.SECONDS.toNanos(timeoutForInvariantExecution));
    // return null;
    // }
    // };
    // suppliers.add(timeoutSupplier);
    // }
    //
    // // Add all specified invariant generation tools
    // for (ExternalInvariantGenerators invGenTool : extInvGens) {
    //
    // ExternalInvariantGenerator gen;
    // try {
    // gen = ExternalInvariantGenerator.getInstance(invGenTool, config);
    // suppliers.add(
    // gen.getSupplierGeneratingInvariants(
    // cFA,
    // new ArrayList<CFANode>(),
    // specification,
    // logger,
    // shutdownManager.getNotifier(),
    // config));
    // // Start the computation
    // List<CompletableFuture<Path>> generatedInvariants =
    // suppliers.parallelStream()
    // .map(s -> CompletableFuture.supplyAsync(s))
    // .collect(Collectors.toList());
    // CompletableFuture<Path> c = anyOf(generatedInvariants);
    //
    // Path invariantsAutomatonFile = null;
    // try {
    // invariantsAutomatonFile = c.get();
    // } catch (InterruptedException | ExecutionException e) {
    // logger.log(
    // Level.WARNING,
    // "The invariant generation was interruped. Continue without additional invariant.");
    // e.printStackTrace();
    // }
    // if (invariantsAutomatonFile == null) {
    // logger.log(
    // Level.WARNING,
    // "None of the tools generated an invariant in ",
    // timeoutForInvariantExecution,
    // " seconds or an error occured. Hence continuing without invariant");
    // } else {
    // // FIXME: just for tests: print the generated invariant
    // BufferedReader reader;
    // try {
    // String fileContent = "";
    // reader =
    // Files.newBufferedReader(
    // invariantsAutomatonFile.toFile().toPath(),
    // Charset.defaultCharset());
    // String line;
    // while ((line = reader.readLine()) != null) {
    // fileContent = fileContent.concat(line);
    // }
    // reader.close();
    //
    // logger.log(Level.WARNING, fileContent);
    // computedPath.add(invariantsAutomatonFile);
    // } catch (IOException e) {
    // logger.log(Level.WARNING, "Cannot print the file");
    // }
    // }
    //
    // } catch (InvalidConfigurationException | CPAException e) {
    // // IF an error occures, we dont do anything and dont generate invariants.
    // logger.log(Level.WARNING, "External invariant generation failed!");
    // hasFinished = true;
    // }
    //
    // }
    System.out.println("generation was succesfull");
    hasFinished = true;
    return hasFinished;
  }

  public Path getFirstComputedPath() {
    if (hasFinished) {
      return computedPath.get(0);
    } else {
      // FIXME: Enhance error handling
      throw new IllegalArgumentException("");
    }
  }

  public AggregatedReachedSets getReachedSet() throws CPAException, InterruptedException {
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
        provider = new StaticCandidateProvider(candidates);

        generator =
            KInductionInvariantGenerator.create(
                config,
                logger,
                shutdownManager,
                cFA,
                specification,
                null,
                provider,
                true);
        return parseReachedSet(generator.getSupplier());
      } catch (InvalidConfigurationException | CPAException | InterruptedException e) {
        // TODO Auto-generated catch block
        throw new CPAException("", e);
      }

    } else {
      // FIXME: Enhance error handling
      throw new IllegalArgumentException("");
    }
  }

  private AggregatedReachedSets parseReachedSet(InvariantSupplier pSupplier) {
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

  public static <T> CompletableFuture<T> anyOf(List<? extends CompletionStage<? extends T>> l) {

    // Code is taken from
    // https://stackoverflow.com/questions/33913193/completablefuture-waiting-for-first-one-normally-return
    CompletableFuture<T> f = new CompletableFuture<>();
    Consumer<T> complete = f::complete;
    CompletableFuture
        .allOf(l.stream().map(s -> s.thenAccept(complete)).toArray(CompletableFuture<?>[]::new))
        .exceptionally(ex -> {
          f.completeExceptionally(ex);
          return null;
        });
    return f;
  }

  public boolean hasComputedInvariants() {
    return computedPath != null && computedPath.size() > 0;
  }

}
