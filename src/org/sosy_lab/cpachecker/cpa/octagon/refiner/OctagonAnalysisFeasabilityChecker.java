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
package org.sosy_lab.cpachecker.cpa.octagon.refiner;

import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.defaults.VariableTrackingPrecision;
import org.sosy_lab.cpachecker.cpa.arg.ARGPath;
import org.sosy_lab.cpachecker.cpa.arg.ARGPath.PathIterator;
import org.sosy_lab.cpachecker.cpa.octagon.OctagonCPA;
import org.sosy_lab.cpachecker.cpa.octagon.OctagonState;
import org.sosy_lab.cpachecker.cpa.octagon.OctagonTransferRelation;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.util.refinement.UseDefRelation;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;

public class OctagonAnalysisFeasabilityChecker {

  private final OctagonTransferRelation transfer;

  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final ARGPath checkedPath;
  private final ARGPath foundPath;
  private final CFA cfa;

  public OctagonAnalysisFeasabilityChecker(CFA pCfa, LogManager pLog, ShutdownNotifier pShutdownNotifier, ARGPath pPath, OctagonCPA pCpa) throws InvalidConfigurationException, CPAException, InterruptedException {
    logger = pLog;
    shutdownNotifier = pShutdownNotifier;
    cfa = pCfa;

    // use the normal configuration for creating the transferrelation
    transfer  = new OctagonTransferRelation(logger, cfa.getLoopStructure().get());
    checkedPath = pPath;

    foundPath = getInfeasiblePrefix(VariableTrackingPrecision.createStaticPrecision(pCpa.getConfiguration(),
                                                                                    cfa.getVarClassification(),
                                                                                    OctagonCPA.class),
                                    new OctagonState(logger, pCpa.getManager()));
  }

  /**
   * This method checks if the given path is feasible, when not tracking the given set of variables.
   *
   * @param path the path to check
   * @return true, if the path is feasible, else false
   * @throws CPAException
   * @throws InterruptedException
   */
  public boolean isFeasible() {
      return checkedPath.size() == foundPath.size();
  }

  public Multimap<CFANode, MemoryLocation> getPrecisionIncrement(VariableTrackingPrecision pOctPrecision) {
    if (isFeasible()) {
      return ArrayListMultimap.<CFANode, MemoryLocation>create();
    } else {

      Multimap<CFANode, MemoryLocation> increment = ArrayListMultimap.<CFANode, MemoryLocation>create();
      for (MemoryLocation loc : getMemoryLocationsFromUseDefRelation()) {
        increment.put(new CFANode("BOGUS-NODE"), loc);
      }

      return increment;
    }
  }

  /**
   * This method returns the variables contained in the use-def relation
   * of the last (failing) assume edge in the found error path.
   */
  private FluentIterable<MemoryLocation> getMemoryLocationsFromUseDefRelation() {
    UseDefRelation useDefRelation = new UseDefRelation(foundPath, Collections.<String>emptySet());

    return FluentIterable.from(useDefRelation.getUsesAsQualifiedName()).transform(MemoryLocation.FROM_STRING_TO_MEMORYLOCATION);
  }

  /**
   * This method obtains the prefix of the path, that is infeasible by itself. If the path is feasible, the whole path
   * is returned
   *
   * @param path the path to check
   * @param pPrecision the precision to use
   * @param pInitial the initial state
   * @return the prefix of the path that is feasible by itself
   * @throws CPAException
   * @throws InterruptedException
   */
  private ARGPath getInfeasiblePrefix(final VariableTrackingPrecision pPrecision, final OctagonState pInitial)
      throws CPAException, InterruptedException {
    try {
      Collection<OctagonState> next = Lists.newArrayList(pInitial);

      Collection<OctagonState> successors = new HashSet<>();

      PathIterator pathIt = checkedPath.pathIterator();
      List<CFAEdge> fullEdgePath = checkedPath.getFullPath();

      for (CFAEdge edge : fullEdgePath) {
        successors.clear();

        for (OctagonState st : next) {
          successors.addAll(transfer.getAbstractSuccessorsForEdge(
              st,
              pPrecision,
              pathIt.getOutgoingEdge()));

          // computing the feasibility check takes sometimes much time with octagons
          // so we let the shutdownNotifer cancel the computation if necessary
          shutdownNotifier.shutdownIfNecessary();
        }

        // no successors => path is infeasible
        if (successors.isEmpty()) {
          // we found an infeasible prefix, if we are currently in a whole
          // of the path we need to advance the iterator by one position
          // so that we have the real infeasible path for later usage
          if (!edge.getPredecessor().equals(extractLocation(pathIt.getAbstractState()))
              && pathIt.hasNext()) {
            pathIt.advance();
          }
          break;
        }

        // update path iterator position if we encounter the next location for
        // which we have an ARGState
        if (edge.getPredecessor().equals(extractLocation(pathIt.getAbstractState()))
            && pathIt.hasNext()) {
          pathIt.advance();
        }

        // get matching successor state and apply precision
        next.clear();
        next.addAll(successors);
      }

      return pathIt.getPrefixInclusive();

    } catch (CPATransferException e) {
      throw new CPAException("Computation of successor failed for checking path: " + e.getMessage(), e);
    }
  }

}
