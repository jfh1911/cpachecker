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
import com.google.common.collect.Lists;
import com.google.common.graph.GraphBuilder;
import com.google.common.graph.MutableGraph;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.path.ARGPath;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.CPAs;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;

@Options(prefix = "cpa.spexport")
public class ErrorTraceExportAlgorithm implements Algorithm {

  private static final String INV_FUNCTION_NAMING_SCHEMA = "Inv_%s";

  @Option(
      secure = true,
      description =
          "Create a file that contains the StrongestPost for each loop in the program in this directory.")
  private String outdirForExport = "output/";

  private final LogManager logger;

  private final CFA cfa;
  private final Algorithm algorithm;
  Solver solver;
  FormulaManagerView fmgr;
  private ShutdownNotifier shutdown;

  private PathFormulaManager pmgr;

  public ErrorTraceExportAlgorithm(
      Configuration config,
      Algorithm pAlgorithm,
      LogManager pLogger,
      CFA pCfa,
      ConfigurableProgramAnalysis pCpa,
      ShutdownNotifier pShutdown)
      throws InvalidConfigurationException {
    config.inject(this, ErrorTraceExportAlgorithm.class);
    algorithm = pAlgorithm;
    cfa = Objects.requireNonNull(pCfa);
    logger = Objects.requireNonNull(pLogger);

    @SuppressWarnings("resource")
    @NonNull
    PredicateCPA predCPA =
        CPAs.retrieveCPAOrFail(pCpa, PredicateCPA.class, ErrorTraceExportAlgorithm.class);
    solver = predCPA.getSolver();
    fmgr = solver.getFormulaManager();
    this.shutdown = pShutdown;
    pmgr = predCPA.getPathFormulaManager();
  }

  @Override
  public AlgorithmStatus run(ReachedSet pReached) throws CPAException, InterruptedException {
    if (!(pReached instanceof PartitionedReachedSet)) {
      throw new CPAException("Expecting a partioned reached set");
    }
    PartitionedReachedSet reached = (PartitionedReachedSet) pReached;
    AlgorithmStatus status = AlgorithmStatus.NO_PROPERTY_CHECKED;

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
   Map<CFANode, Integer> lineNumbersToNodes = getLineNumbersToNodes(loopStruct.getAllLoopHeads());
        if (loopStruct.getCount() == 1) {
          CFANode loopHead = cfa.getAllLoopHeads().get().asList().get(0);
          List<AbstractState> argStateOfLoopHead = Lists.newArrayList(filter(loopHead, reached));

          // TO be able to see, which predecessor nodes of the loop head are part of the loop body
          // (and hence need to be processed differently)
          // we first collect all nodes of the looped body
          Set<CFANode> nodesInLoop = new HashSet<>();
          for (Loop loop : loopStruct.getLoopsForLoopHead(loopHead)) {
            nodesInLoop.addAll(loop.getLoopNodes());
          }
          Set<PathFormula> initCondition = new HashSet<>();
          Set<PathFormula> preserveCondition = new HashSet<>();
          for (AbstractState state : filter(loopHead, reached)) {
            Optional<PathFormula> initOpt =
                getInitConditionForLoop(loopHead, nodesInLoop, state, reached);
            Optional<PathFormula> presOpt =
                getPreserveConditionForLoop(loopHead, nodesInLoop, state);
            if (initOpt.isPresent()) {
              initCondition.add(initOpt.get());
            }
            if (presOpt.isPresent()) {
              preserveCondition.add(presOpt.get());
            }
          }

          List<PathFormula> terminationCondition = new ArrayList<>();
          for (AbstractState s : reached.asCollection()) {

            if (AbstractStates.isTargetState(s)) {
              Set<ARGPath> paths =
                  ARGUtils.getAllPaths(
                      AbstractStates.extractStateByType(argStateOfLoopHead.get(0), ARGState.class),
                      AbstractStates.extractStateByType(s, ARGState.class));
              for (ARGPath path : paths) {

                // If the path contains exactly two abstraction locations, namely the first (loop
                // head) and the last (error location) and all nodes in between are non-abstration
                // nodes, we know that last but one's node contains the path formula for the full
                // path that need to be checked.

                if (isAbstractionState(path.getFirstState())
                    && isAbstractionState(path.getLastState())
                    && allInnerNodesAreNonAbstractionStates(path)) {
                  terminationCondition.add(
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

          PathFormula init = StrongestPost4Loop.merge(initCondition, formulaManager);
          PathFormula preserve = StrongestPost4Loop.merge(preserveCondition, formulaManager);
          Map<CFANode, PathFormula> map = new HashMap<>();
          map.put(loopHead, getFuncDeclForNode(loopHead, init));
          StrongestPost4Loop.serializeLoop(
              init,
              preserve,
              terminationCondition,
              formulaManager,
              logger,
              loopHead,
              outdirForExport,
              map,
              lineNumbersToNodes);
        } else {

          Map<CFANode, PathFormula> initPathToLoopHead = new HashMap<>();
          Map<CFANode, PathFormula> preservePathToLoopHead = new HashMap<>();
          Map<CFANode, PathFormula> invariants = new HashMap<>();
          Map<CFANode, Set<PathFormula>> otherInvariantsPresentInInit = new HashMap<>();

          List<CFANode> orderedLoopHeads =
              extracted(loopStruct); // We assume that there is only a single target state

          for (CFANode loopHead : orderedLoopHeads) {
            Set<PathFormula> ohterInvsPresnet = new HashSet<>();
            List<PathFormula> initPaths = new ArrayList<>();
            List<PathFormula> preservePaths = new ArrayList<>();
            // TO be able to see, which predecessor nodes of the loop head are part of the
            // loop body  (and hence need to be processed differently)  we first collect all
            // nodes of the looped body
            Set<CFANode> nodesInLoop = new HashSet<>();
            for (Loop loop : loopStruct.getLoopsForLoopHead(loopHead)) {
              nodesInLoop.addAll(loop.getLoopNodes());
            }

            for (AbstractState state : filter(loopHead, reached)) {

              // Just for debugging:
              Set<ARGPath> debPath =
                  ARGUtils.getAllPaths(
                      reached, AbstractStates.extractStateByType(state, ARGState.class));

              for (ARGPath path :
                  ARGUtils.getAllPaths(
                      reached, AbstractStates.extractStateByType(state, ARGState.class))) {
                List<AbstractState> absStateOnPath =
                    path.asStatesList()
                        .stream()
                        .filter(
                            s ->
                                isAbstractionState(s)
                                    && !path.getFirstState().equals(s)
                                    && !path.getLastState().equals(s))
                        .collect(Collectors.toList());
                Optional<PathFormula> initConditionForLoop =
                    getInitConditionForLoop(loopHead, nodesInLoop, state, reached);
                Optional<PathFormula> preserveConditionForLoop =
                    getPreserveConditionForLoop(loopHead, nodesInLoop, state);
                if (preserveConditionForLoop.isPresent()) {
                  preservePaths.add(preserveConditionForLoop.get());
                }
                if (absStateOnPath.isEmpty()) {
                  // we can "simply" take the pathFormulas from the predecessor nodes of the
                  // loopHead
                  if (initConditionForLoop.isPresent()) {
                    initPaths.add(initConditionForLoop.get());
                  }

                } else {
                  // Now, we have at least one  abstract location on the path.
                  // DUe to the ordering we process the loopheads, we know that the inforamtion for
                  // the direcly succesing loopheads are already computed (especiall the init, which
                  // we can reuse).

                  CFANode lastNode =
                      AbstractStates.extractLocation(absStateOnPath.get(absStateOnPath.size() - 1));
                  if (!invariants.containsKey(lastNode)) {
                    logger.log(
                        Level.WARNING,
                        String.format(
                            "An internal error occured. The loop %s cannot be paresd, as a preceeding loop head %s is not processed. Hence aborting!",
                            loopHead, lastNode));
                    throw new CPAException(
                        "An internal error occured, see log for furhter information !");
                  }
                  ohterInvsPresnet.add(invariants.get(lastNode));
                  ohterInvsPresnet.addAll(otherInvariantsPresentInInit.get(lastNode));
                  // Build initCOnd4Loop as follows:
                  //                  sp(lastNode) \wedge inv(lastNode \wedge iniCondForLoop
                  if (initConditionForLoop.isPresent()) {
                    PathFormula combinedInit =
                        StrongestPost4Loop.merge(
                            Lists.newArrayList(
                                initPathToLoopHead.get(lastNode),
                                invariants.get(lastNode),
                                initConditionForLoop.get()),
                            fmgr);
                    initPaths.add(combinedInit);
                  }
                }
              }
            }
            PathFormula initPF = StrongestPost4Loop.merge(initPaths, fmgr);
            initPathToLoopHead.put(loopHead, initPF);
            preservePathToLoopHead.put(loopHead, StrongestPost4Loop.merge(preservePaths, fmgr));
            // now, we can create a pathformula for the invariant (needed for later verification)

            invariants.put(loopHead, getFuncDeclForNode(loopHead, initPF));
          }

          // Compute termiantoin condition:
          Set<PathFormula> terminationConditions = new HashSet<>();
          for (AbstractState target : AbstractStates.getTargetStates(reached)) {

            for (ARGPath path :
                ARGUtils.getAllPaths(
                    reached, AbstractStates.extractStateByType(target, ARGState.class))) {
              List<ARGState> absPath =
                  path.asStatesList()
                      .stream()
                      .filter(s -> isAbstractionState(s) && !path.getFirstState().equals(s))
                      .collect(Collectors.toList());
              Optional<PathFormula> targetPF = getPathFormulaOfNode(target);
              if (absPath.isEmpty() && targetPF.isPresent()) {
                terminationConditions.add(targetPF.get());
              } else {

                CFANode lastNode = AbstractStates.extractLocation(absPath.get(absPath.size() - 1));
                if (!invariants.containsKey(lastNode)) {
                  logger.log(
                      Level.WARNING,
                      String.format(
                          "An internal error occured. The loop %s cannot be paresd, as a preceeding loop head %s is not processed. Hence aborting!",
                          target, lastNode));
                  throw new CPAException(
                      "An internal error occured, see log for furhter information !");
                }
                terminationConditions.add(invariants.get(lastNode));
              }
            }
          }

          // Finally, serialize the objectes
          for (CFANode loopHead : orderedLoopHeads) {

            StrongestPost4Loop.serializeLoop(
                initPathToLoopHead.get(loopHead),
                preservePathToLoopHead.get(loopHead),
                terminationConditions,
                fmgr,
                logger,
                loopHead,
                outdirForExport,
                invariants,
                lineNumbersToNodes);
          }
        }
      }
      return status;
    }
  }

  private PathFormula getFuncDeclForNode(CFANode loopHead, PathFormula initPF) {
    FunctionDeclaration<BooleanFormula> invDecl =
        fmgr.getFunctionFormulaManager()
            .declareUF(
                String.format(INV_FUNCTION_NAMING_SCHEMA, loopHead.toString()),
                FormulaType.BooleanType,
                new ArrayList<FormulaType<?>>());

    PathFormula inv =
        new PathFormula(
            fmgr.getFunctionFormulaManager().callUF(invDecl),
            initPF.getSsa(),
            initPF.getPointerTargetSet(),
            initPF.getLength());
    return inv;
  }

  private Map<CFANode, Integer> getLineNumbersToNodes(ImmutableSet<CFANode> loopHeads)
      throws CPAException {

    Map<CFANode, Integer> res = new HashMap<>();
    // Firstly, determine the loop number needed for the export file name.

    for (CFANode pLoopHead : loopHeads) {
    int lineNumberOfLoopHead = -1;
    for (int i = 0; i < pLoopHead.getNumEnteringEdges(); i++) {
      CFAEdge e = pLoopHead.getEnteringEdge(i);
      if (e.getLineNumber() > 0) {
        lineNumberOfLoopHead = e.getLineNumber();
      }
    }
      if (lineNumberOfLoopHead < 0) {
        throw new CPAException(
            String.format(
                "Cannot determein line number for loop at node %s, hence aborting", pLoopHead));
      } else {
        res.put(pLoopHead, lineNumberOfLoopHead);
      }
    }
    return res;
  }

  private Optional<PathFormula> getPreserveConditionForLoop(
      CFANode loopHead, Set<CFANode> nodesInLoop, AbstractState pAbstractState) {
    List<PathFormula> preserveCondition = new ArrayList<>();
    for (int i = 0; i < loopHead.getNumEnteringEdges(); i++) {
      CFANode predOfLoopHead = loopHead.getEnteringEdge(i).getPredecessor();
      if (nodesInLoop.contains(predOfLoopHead)) {
        // We see a path within the loop:
        Optional<PathFormula> pf = getPathFormulaOfNode(pAbstractState);
        if (pf.isPresent()) {
          preserveCondition.add(pf.get());
        }
      }
    }
    if (preserveCondition.isEmpty()) {
      return Optional.empty();
    }
    return Optional.of(StrongestPost4Loop.merge(preserveCondition, fmgr));
  }

  private Optional<PathFormula> getInitConditionForLoop(
      CFANode loopHead,
      Set<CFANode> nodesInLoop,
      AbstractState pAbstractState,
      PartitionedReachedSet reached) {

    List<PathFormula> initCondition = new ArrayList<>();
    for (int i = 0; i < loopHead.getNumEnteringEdges(); i++) {
      CFANode predOfLoopHead = loopHead.getEnteringEdge(i).getPredecessor();
      if (!nodesInLoop.contains(predOfLoopHead)) {
        // This is the path from the last abstraction location to the loophead

        Optional<PathFormula> pf = getPathFormulaOfNode(predOfLoopHead, reached);
        if (pf.isPresent()) {
          initCondition.add(pf.get());
        }
      }
    }
    if (initCondition.isEmpty()) {
      return Optional.empty();
    }
    return Optional.of(StrongestPost4Loop.merge(initCondition, fmgr));
  }

  private boolean isAbstractionState(ARGState state) {
    return AbstractStates.extractStateByType(state, PredicateAbstractState.class)
        .isAbstractionState();
  }

  private List<CFANode> extracted(LoopStructure loopStruct)
      throws CPAException, InterruptedException {

    // Check, if the loops are consecutive, meaning that we have a unique ordering in the cfa
    // Determeined by the fact, that for each pair of loophead A;B we have a path from A to be
    // but not from B to A
    List<CFANode> loopheads = Lists.newArrayList(loopStruct.getAllLoopHeads());
    // Check if nested loops are present, if a loophead is present in a different loop
    for (Loop loop : loopStruct.getAllLoops()) {
      if (loopheads
          .stream()
          .anyMatch(
              head -> !loop.getLoopHeads().contains(head) && loop.getLoopNodes().contains(head))) {
        logger.log(
            Level.WARNING,
            "The program contains nested loops. This is currently not supported, hence aborting!");
        throw new CPAException("Currently, only programs without neaded loops are supported!");
      }
    }
    // We now that the program does not contain any nested loops
    // now, we determine  a ordering. Therefore, we firstly compute a total order for all loopheads
    // present
    MutableGraph<CFANode> graph = GraphBuilder.directed().build();
    loopheads.forEach(head -> graph.addNode(head));

    // Now, compare each pair of loop heads and determine their ordering.
    // We use a graph, where an directed edge  from A to be B means that A appears before B.
    // If there are no edges between, both (A before B or B before A) is ok.
    Function<CFANode, Iterable<CFAEdge>> func =
        new Function<>() {
          @Override
          public Iterable<CFAEdge> apply(CFANode pT) {
            return CFAUtils.allLeavingEdges(pT);
          }
        };
    for (int i = 0; i < loopheads.size(); i++) {
      for (int j = i + 1; j < loopheads.size(); j++) {

        if (CFAUtils.existsPath(loopheads.get(i), loopheads.get(j), func, shutdown)) {
          graph.putEdge(loopheads.get(i), loopheads.get(j));
        }
        if (CFAUtils.existsPath(loopheads.get(j), loopheads.get(i), func, shutdown)) {
          graph.putEdge(loopheads.get(j), loopheads.get(i));
        }
      }
    }
    GraphOrderingDeterminer<CFANode> determiner = new GraphOrderingDeterminer<>();
    return determiner.determineOrdering(graph, logger);
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

  /** Finds all abstract states with same location as given */
  private Set<AbstractState> filter(CFANode pPredOfLoopHead, ReachedSet pReached) {
      return pReached
          .asCollection()
          .stream()
          .filter(s -> AbstractStates.extractLocation(s).equals(pPredOfLoopHead))
          .collect(Collectors.toSet());
  }

  private Optional<PathFormula> getPathFormulaOfNode(AbstractState pAbsState) {
    PredicateAbstractState pred =
        AbstractStates.extractStateByType(pAbsState, PredicateAbstractState.class);
    return Optional.of(pred.getPathFormula());
  }

  private Optional<PathFormula> getPathFormulaOfNode(CFANode pPredOfLoopHead, ReachedSet pReached) {
    Collection<AbstractState> toProcess = filter(pPredOfLoopHead, pReached);

    for (AbstractState s : toProcess) {
      PredicateAbstractState pred =
          AbstractStates.extractStateByType(s, PredicateAbstractState.class);

      return Optional.of(pred.getPathFormula());
    }
    return Optional.empty();
  }
}
