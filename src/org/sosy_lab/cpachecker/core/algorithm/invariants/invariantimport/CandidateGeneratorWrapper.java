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
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterators;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.common.util.concurrent.ListenableFuture;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.CandidateGenerator;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;

public class CandidateGeneratorWrapper implements CandidateGenerator {

  private List<ListenableFuture<Path>> pendingInvs;

  // Start with 1, since first invariant is already injected initially
  private int numberOfFinishedGenerators = 1;
  private CandidateGenerator defaultGenerator;
  private List<CandidateInvariant> candidates;
  private Set<CandidateInvariant> foundInvariants;
  private LogManager logger;
  private Configuration pConfig;
  private Specification pSpecification;
  private CFA cfa;
  private ShutdownNotifier pShutdownManager;

  public CandidateGeneratorWrapper(
      List<ListenableFuture<Path>> pPendingInvs,
      CandidateGenerator pDefaultGenerator,
      LogManager pLogger,
      Configuration pPConfig,
      Specification pPSpecification,
      CFA pCfa,
      ShutdownNotifier pPShutdownManager) {
    super();
    pendingInvs = ImmutableList.copyOf(pPendingInvs);
    // pLogger.log(Level.WARNING, "wrapper obtained", pendingInvs.toString());
    defaultGenerator = pDefaultGenerator;
    logger = pLogger;
    pConfig = pPConfig;
    pSpecification = pPSpecification;
    cfa = pCfa;
    pShutdownManager = pPShutdownManager;
    candidates = new ArrayList<>();
    foundInvariants = new HashSet<>();
  }

  @Override
  public boolean produceMoreCandidates() {
    boolean hasProducedNewCandidates = false;
    // check if new invgen finished
    while (numberOfFinishedGenerators < pendingInvs.size()
        && pendingInvs.get(numberOfFinishedGenerators).isDone()) {

      // inject the witnesses
      Path pathToInvariant;
      try {
        pathToInvariant = pendingInvs.get(numberOfFinishedGenerators).get();
        logger.log(
            Level.INFO,
            "Injecting witneeses from path ",
            pathToInvariant);
        final Set<CandidateInvariant> localCandidates = new LinkedHashSet<>();

        final Multimap<String, CFANode> candidateGroupLocations = HashMultimap.create();

        WitnessInvariantsExtractor extractor =
            new WitnessInvariantsExtractor(
                pConfig,
                pSpecification,
                logger,
                cfa,
                pShutdownManager,
                pathToInvariant);
        extractor.extractCandidatesFromReachedSet(localCandidates, candidateGroupLocations);
        candidates.addAll(localCandidates);
        hasProducedNewCandidates = true;
      } catch (InterruptedException | ExecutionException | InvalidConfigurationException
          | CPAException e) {
        logger.log(
            Level.WARNING,
            "A problem occured while injecting witnesses  ");
      }
      // increase number of injected witnesses
      numberOfFinishedGenerators = numberOfFinishedGenerators + 1;
    }
    // Than load and store to internal list of candidates

    return defaultGenerator.produceMoreCandidates() || hasProducedNewCandidates;
  }

  @Override
  public boolean hasCandidatesAvailable() {
    return defaultGenerator.hasCandidatesAvailable()
        || pendingInvs.size() > numberOfFinishedGenerators
        || !candidates.isEmpty();
  }

  @Override
  public void confirmCandidates(Iterable<CandidateInvariant> pCandidates) {
    for (CandidateInvariant inv : pCandidates) {
      logger.log(Level.FINER, "Proven invariant correct", inv.toString());
      candidates.remove(inv);
      foundInvariants.add(inv);
    }
  }

  @Override
  public Set<? extends CandidateInvariant> getConfirmedCandidates() {
    return Sets.union(defaultGenerator.getConfirmedCandidates(), this.foundInvariants);
  }

  @Override
  public Iterator<CandidateInvariant> iterator() {
    return Iterators.concat(defaultGenerator.iterator(), candidates.iterator());
  }

}
