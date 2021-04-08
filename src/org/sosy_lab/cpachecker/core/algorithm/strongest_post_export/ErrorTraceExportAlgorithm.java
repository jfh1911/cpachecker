// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGCPA;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.path.ARGPath;
import org.sosy_lab.cpachecker.cpa.composite.CompositeCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;

@Options(prefix = "cpa.spexport")
public class ErrorTraceExportAlgorithm implements Algorithm {

  @Option(
      secure = true,
      description =
          "Create a file that contains the StrongestPost for each loop in the program in this directory.")
  private String outdirForExport = "output/";

  private final LogManager logger;

  private final CFA cfa;
  private final Algorithm algorithm;
  Solver solver;

  public ErrorTraceExportAlgorithm(
      Configuration config,
      Algorithm pAlgorithm,
      LogManager pLogger,
      CFA pCfa,
      ConfigurableProgramAnalysis pCpa)
      throws InvalidConfigurationException {
    algorithm = pAlgorithm;
    cfa = Objects.requireNonNull(pCfa);
    logger = Objects.requireNonNull(pLogger);

    config.inject(this, ErrorTraceExportAlgorithm.class);

    if (pCpa instanceof ARGCPA) {
      for (ConfigurableProgramAnalysis cpa : ((ARGCPA) pCpa).getWrappedCPAs()) {
        if (cpa instanceof CompositeCPA) {
          for (ConfigurableProgramAnalysis wrappedCPA : ((CompositeCPA) cpa).getWrappedCPAs()) {
            if (wrappedCPA instanceof PredicateCPA) {
              this.solver = ((PredicateCPA) wrappedCPA).getSolver();
              break;
            }
          }
        }
      }
    }
    assert !Objects.isNull(solver);
  }

  @Override
  public AlgorithmStatus run(ReachedSet pReached) throws CPAException, InterruptedException {
    if (!(pReached instanceof PartitionedReachedSet)) {
      throw new CPAException("Expecting a partioned reached set");
    }
    PartitionedReachedSet reached = (PartitionedReachedSet) pReached;
    AlgorithmStatus status = AlgorithmStatus.NO_PROPERTY_CHECKED;

    //    stats.totalTimer.start();

    // run algorithm
    algorithm.run(reached);
    if (reached.hasWaitingState()) {
      // Nested algortihm is not finished, hence do another round by returning to loop in calling
      // class
      return status;

    } else {
      // Try to get the loop heads and extract the loop invariant conditions for these
      if (cfa.getAllLoopHeads().isPresent() && cfa.getLoopStructure().isPresent()) {
        LoopStructure loopStruct = cfa.getLoopStructure().get();

        // TODO: Add support for programs with moer than one loop!
        if (loopStruct.getCount() != 1) {
          logger.log(
              Level.WARNING,
              "The program contains more than one loop. This is currently not supported, hence aborting!");
          throw new CPAException("Currently, only programs with a single loop are supported!");
        }

        CFANode loopHead = cfa.getAllLoopHeads().get().asList().get(0);
        List<AbstractState> argStateOfLoopHead = new ArrayList<>(filter(loopHead, reached));

        List<PathFormula> pathLeadingToLoophead = new ArrayList<>();
        List<PathFormula> pathThroughLoop = new ArrayList<>();
        ImmutableSet<Loop> loops = loopStruct.getLoopsForLoopHead(loopHead);

        // TO be able to see, which predecessor nodes of the loop head are part of the loop body
        // (and hence need to be processed differently)
        // we first collect all nodes of the looped body
        Set<CFANode> nodesInLoop = new HashSet<>();
        for (Loop loop : loops) {
          nodesInLoop.addAll(loop.getLoopNodes());
        }
        for (int i = 0; i < loopHead.getNumEnteringEdges(); i++) {
          CFANode predOfLoopHead = loopHead.getEnteringEdge(i).getPredecessor();
          if (nodesInLoop.contains(predOfLoopHead)) {
            // We see a path within the loop:
            Optional<PathFormula> pf = getPathFormulaOfNode(predOfLoopHead, reached);
            if (pf.isPresent()) {
              pathThroughLoop.add(pf.get());
            }
          } else {
            Optional<PathFormula> pf = getPathFormulaOfNode(predOfLoopHead, reached);
            if (pf.isPresent()) {
              pathLeadingToLoophead.add(pf.get());
            }
          }
        }

        List<PathFormula> helpfullVerificationCpndition = new ArrayList<>();
        for (AbstractState s : reached.asCollection()) {

          if (AbstractStates.isTargetState(s)) {
            Set<ARGPath> paths =
                ARGUtils.getAllPaths(
                    AbstractStates.extractStateByType(argStateOfLoopHead.get(0), ARGState.class),
                    AbstractStates.extractStateByType(s, ARGState.class));
            for (ARGPath path : paths) {

              // If the path contains exactly two abstraction locations, namely the first (loop
              // head) and the last (error location) and all nodes in between are non-abstration
              // nodes, we know that last but one's node contains the path formula for the full path
              // that need to be checked.

              if (AbstractStates.extractStateByType(
                          path.getFirstState(), PredicateAbstractState.class)
                      .isAbstractionState()
                  && AbstractStates.extractStateByType(
                          path.getLastState(), PredicateAbstractState.class)
                      .isAbstractionState()
                  && allInnerNodesAreNonAbstractionStates(path)) {
                helpfullVerificationCpndition.add(
                    AbstractStates.extractStateByType(
                            path.getStatePairs().get(path.getStatePairs().size() - 1).getFirst(),
                            PredicateAbstractState.class)
                        .getPathFormula()); // to get the last state.
              } else {
                // TODO: Implement
                logger.log(
                    Level.WARNING,
                    "Ecountered a path with intermediated states that have been abstracted. Currently, this is not supported!");
                throw new UnsupportedOperationException("not implemented yet");
              }
            }
          }
        }


        FormulaManagerView formulaManager = solver.getFormulaManager();
        // Finally, serialize the object
        StrongestPost4Loop.serializeLoop(
            pathLeadingToLoophead,
            pathThroughLoop,
            helpfullVerificationCpndition,
            formulaManager,
            logger,
            loopHead,
            outdirForExport);
      }
      return status;
    }
  }

  private boolean allInnerNodesAreNonAbstractionStates(ARGPath pPath) {
    ImmutableList<ARGState> stateList = pPath.asStatesList();
    for (int i = 1;
        i < stateList.size() - 1;
        i++) { // as we want to ignore the first and last state
      if (AbstractStates.extractStateByType(stateList.get(i), PredicateAbstractState.class)
          .isAbstractionState()) {
        return false;
      }
    }
    return true;
  }

  private Optional<PathFormula> getPathFormulaOfNode(
      CFANode pPredOfLoopHead, PartitionedReachedSet pReached) {
    Collection<AbstractState> toProcess = filter(pPredOfLoopHead, pReached);

    for (AbstractState s : toProcess) {
      PredicateAbstractState pred =
          AbstractStates.extractStateByType(s, PredicateAbstractState.class);


      return Optional.of(pred.getPathFormula());
    }
    return Optional.empty();
  }

  private Set<AbstractState> filter(CFANode pPredOfLoopHead, PartitionedReachedSet pReached) {
    return pReached
        .asCollection()
        .stream()
        .filter(s -> AbstractStates.extractLocation(s).equals(pPredOfLoopHead))
        .collect(Collectors.toSet());
  }
}
