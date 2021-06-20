// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import static org.sosy_lab.common.collect.MapsDifference.collectMapsDifferenceTo;

import com.google.common.collect.FluentIterable;
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
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.collect.MapsDifference;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.AssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm.AlgorithmStatus;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.path.ARGPath;
import org.sosy_lab.cpachecker.cpa.arg.path.PathIterator;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.CPAs;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class GeneratorSharma {

  public static final String INV_FUNCTION_NAMING_SCHEMA = "Inv_%s";

  private String outdirForExport = "output/";

  private final LogManager logger;

  private final CFA cfa;
  Solver solver;
  FormulaManagerView fmgr;
  private ShutdownNotifier shutdown;

  private PathFormulaManager pfManager;

  private CtoFormulaConverter converter;

  private LoopStructure loopStruct;

  public GeneratorSharma(
      Algorithm pAlgorithm,
      LogManager pLogger,
      CFA pCfa,
      ConfigurableProgramAnalysis pCpa,
      ShutdownNotifier pShutdown,
      String outdirForExport)
      throws InvalidConfigurationException {
    cfa = Objects.requireNonNull(pCfa);
    logger = Objects.requireNonNull(pLogger);

    @SuppressWarnings("resource")
    @NonNull
    PredicateCPA predCPA = CPAs.retrieveCPAOrFail(pCpa, PredicateCPA.class, GeneratorSharma.class);
    solver = predCPA.getSolver();
    fmgr = solver.getFormulaManager();
    pfManager = predCPA.getPathFormulaManager();
    converter = pfManager.getConverter();
    this.shutdown = pShutdown;
    this.outdirForExport = outdirForExport;
  }

  public AlgorithmStatus generate(ReachedSet pReached) throws CPAException, InterruptedException {
    if (!(pReached instanceof PartitionedReachedSet)) {
      throw new CPAException("Expecting a partioned reached set");
    }
    PartitionedReachedSet reached = (PartitionedReachedSet) pReached;

    // Try to get the loop heads and extract the loop invariant conditions for these
    loopStruct = cfa.getLoopStructure().get();
    if (cfa.getAllLoopHeads().isPresent() && cfa.getLoopStructure().isPresent()) {

      Map<CFANode, Integer> lineNumbersToNodes =
          getLineNumbersToNodes(loopStruct.getAllLoopHeads());

      Map<CFANode, List<Pair<PathFormula, PathFormula>>> mapOfLoopHeadsToAllConditions =
          new HashMap<>();

      PathFormula initalPF =
          AbstractStates.extractStateByType(reached.getFirstState(), PredicateAbstractState.class)
              .getPathFormula();

      for (CFANode loopHead : loopStruct.getAllLoopHeads()) {
        List<Pair<PathFormula, PathFormula>> pathForLocation = new ArrayList<>();
        for (AbstractState absLoopHeadState :
            filter(loopHead, reached)
                .stream()
                .filter(s -> !AbstractStates.extractStateByType(s, ARGState.class).isCovered())
                .collect(Collectors.toSet())) {
          for (AbstractState targetState : AbstractStates.getTargetStates(reached)) {
            final Set<ARGPath> allPathsToTarget =
                ARGUtils.getAllPaths(
                    AbstractStates.extractStateByType(absLoopHeadState, ARGState.class),
                    AbstractStates.extractStateByType(targetState, ARGState.class),
                    true);

            for (ARGPath violationPath : allPathsToTarget) {
              for (ARGPath initPath :
                  ARGUtils.getAllPaths(
                      AbstractStates.extractStateByType(reached.getFirstState(), ARGState.class),
                      AbstractStates.extractStateByType(absLoopHeadState, ARGState.class),
                      true)) {
                System.out.println("");
                @Nullable
                PathFormula pathFormulaA =
                    transformPath(reached.getFirstState(), initalPF, initPath, reached);
                @Nullable
                PathFormula pathFormulaB =
                    transformPath(absLoopHeadState, pathFormulaA, violationPath, reached);
                pathForLocation.add(Pair.of(pathFormulaA, pathFormulaB));
              }
            }
          }
        }
        mapOfLoopHeadsToAllConditions.put(loopHead, pathForLocation);
      }

      // Now export all interpolation queries:
      for (Entry<CFANode, List<Pair<PathFormula, PathFormula>>> interpol :
          mapOfLoopHeadsToAllConditions.entrySet()) {

        List<InterpolationTaskExchangeObject>  tasksPerNode = new ArrayList<>();
        for (Pair<PathFormula, PathFormula> task : interpol.getValue()) {
          InterpolationTaskExchangeObject exObj =
              new InterpolationTaskExchangeObject(
                  fmgr.dumpFormula(task.getFirst().getFormula()).toString(),
                  task.getFirst().getSsa(),
                  fmgr.dumpFormula(task.getSecond().getFormula()).toString(),
                  task.getSecond().getSsa());
          tasksPerNode.add(exObj);
        }
        StrongestPost4Loop.dumpObjToFile(
            logger,
            interpol.getKey(),
            outdirForExport,
            lineNumbersToNodes,
            new SharmaInterpolationTaskList(tasksPerNode),
            true);
      }
    }
    return AlgorithmStatus.NO_PROPERTY_CHECKED;
  }

  private ARGPath reducePath(
      ARGPath originalPath, Optional<AbstractState> pStartIncluded, AbstractState pEndNotIncluded) {
    List<ARGState> states = new ArrayList<>();
    List<CFAEdge> edges = new ArrayList<>();
    boolean firstFound = pStartIncluded.isEmpty();

    PathIterator pathIterator = originalPath.pathIterator();
    while (pathIterator.hasNext()) {
      Pair<ARGState, CFAEdge> e =
          Pair.of(pathIterator.getAbstractState(), pathIterator.getOutgoingEdge());
      final @Nullable ARGState currentNode = e.getFirst();
      if (!firstFound && currentNode.equals(pStartIncluded.get())) {
        firstFound = true;
      }
      if (firstFound) {
        if (!currentNode.equals(pEndNotIncluded)) {

          states.add(currentNode);

          edges.add(e.getSecond());
        } else {
          // Remove the last edge
          edges.remove(edges.size() - 1);
          break;
        }
      }
      pathIterator.advance();
    }
    return new ARGPath(states, edges);
  }

  private boolean canBeSAT(PathFormula pPathFormula, PathFormula assertion) {
    ProverEnvironment prover = solver.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    try {
      prover.addConstraint(pPathFormula.getFormula());
      prover.addConstraint(assertion.getFormula());
      return !prover.isUnsat();
    } catch (InterruptedException | SolverException e) {
      // In case of an error, we assume that the formula is sat and should be exported
      return true;
    }
  }

  private @Nullable PathFormula getAssertion(
      AbstractState pAbstractState, PredicateAbstractState pPredicateState, ARGPath pPath)
      throws CPATransferException, InterruptedException {
    PathFormula oldPF = pPredicateState.getPathFormula();
    PathFormula res =
        new PathFormula(
            fmgr.getBooleanFormulaManager().makeTrue(),
            oldPF.getSsa(),
            oldPF.getPointerTargetSet(),
            oldPF.getLength());

    boolean start = false;
    // Iterate through all edges of the path and start to build the path fromula from
    // pStateBeforeAssertion to last state

    PathIterator pathIterator = pPath.pathIterator();
    while (pathIterator.hasNext()) {
      Pair<ARGState, CFAEdge> e =
          Pair.of(pathIterator.getAbstractState(), pathIterator.getOutgoingEdge());
      if (e.getFirst().equals(pAbstractState)) {
        start = true;
      }
      if (start) {
        res = pfManager.makeAnd(res, e.getSecond());
      }
      pathIterator.advance();
    }
    return res;
  }

  private @Nullable PathFormula transformPath(
      AbstractState startingPoint,
      PathFormula oldPF,
      final ARGPath pPath,
      PartitionedReachedSet reached)
      throws CPATransferException, InterruptedException {

    PathFormula res =
        new PathFormula(
            fmgr.getBooleanFormulaManager().makeTrue(),
            oldPF.getSsa(),
            oldPF.getPointerTargetSet(),
            oldPF.getLength());

    boolean start = false;
    // Iterate through all edges of the path and start to build the path fromula from
    // pStateBeforeAssertion to last state

    PathIterator pathIterator = pPath.fullPathIterator();

    do {
      if (pathIterator.isPositionWithState()) {
        final ARGState abstractState = pathIterator.getAbstractState();
        if (abstractState.equals(startingPoint)) {
          start = true;
        }
        if (start) {
          // Now, check if we have an abstractionState. Then, we need to add one loop iteration
          @Nullable
          PredicateAbstractState currentPredState =
              AbstractStates.extractStateByType(abstractState, PredicateAbstractState.class);
          ARGState first = pPath.getFirstState();
          if (currentPredState.isAbstractionState()
              && !abstractState.equals(pPath.getFirstState())
              && !abstractState.equals(
                  reached.getFirstState()) // First is abstraction state by default
              && !abstractState.isTarget()) { // Last aswell, but both not loophead

            res = addOneLoopIterationAndUpdateSSA(abstractState, res, reached);
            continue;
          }
        }
      }
      if (pathIterator.hasNext()) {
        @Nullable CFAEdge edge = pathIterator.getOutgoingEdge();
        if (start && Objects.nonNull(edge)) {
          res = pfManager.makeAnd(res, edge);
        }
      }

    } while (pathIterator.advanceIfPossible());
    return res;
  }

  private PathFormula addOneLoopIterationAndUpdateSSA(
      ARGState pLoopHeadABS, PathFormula pCUrrentPathFormula, PartitionedReachedSet reached)
      throws CPATransferException, InterruptedException {

    // FIrstly, determie which predecessor is inside the loop
    CFANode loopHead = AbstractStates.extractLocation(pLoopHeadABS);
    if (!loopStruct.getAllLoopHeads().contains(loopHead)) {
      throw new IllegalArgumentException(
          String.format(
              "An internal error occured, because abstraction is not conducted at loophead. The abstraction location is %s, availabel loopheads are %s",
              loopHead, loopStruct.getAllLoopHeads()));
    }

    // AS we have a empty precision, there is exactly a second ARG-node X associated with the
    // loophead, covered by the abstract state pLoopHeadABS
    // We search for this node and compute all path through the loop by exploring all path
    // pLoopHeadABS to

    Set<CFANode> nodesInLoop = new HashSet<>();
    for (Loop loop : loopStruct.getLoopsForLoopHead(loopHead)) {
      nodesInLoop.addAll(loop.getLoopNodes());
    }
    Optional<CFANode> predecessorInLoop =
        CFAUtils.allEnteringEdges(loopHead)
            .stream()
            .map(e -> e.getPredecessor())
            .filter(n -> nodesInLoop.contains(n))
            .findFirst();
    if (predecessorInLoop.isEmpty()) {
      throw new IllegalArgumentException(
          "THere has to be at least one node in the loop leading to the loophead");
    }

    // Now, get all path from the loopHead to the pedecessorInLoop (the corresponding-ARG_Node
    Set<PathFormula> allPathFormulae = new HashSet<>();
    PathFormula pf1LoopITeration =
        new PathFormula(
            fmgr.getBooleanFormulaManager().makeTrue(),
            pCUrrentPathFormula.getSsa(),
            pCUrrentPathFormula.getPointerTargetSet(),
            pCUrrentPathFormula.getLength());
    for (AbstractState absLoopHeadState : filter(predecessorInLoop.get(), reached)) {
      // AS the arg is a tree (due to abstraction at loop heads and covered by, as empty precision,
      // we dont need to care about neasted loops
      final Set<ARGPath> allPaths =
          ARGUtils.getAllPaths(
              AbstractStates.extractStateByType(pLoopHeadABS, ARGState.class),
              AbstractStates.extractStateByType(absLoopHeadState, ARGState.class),
              false);
      // Compute for each path the path formula (use transformPath to handle neasted loops
      for (ARGPath path : allPaths) {
        allPathFormulae.add(transformPath(pLoopHeadABS, pf1LoopITeration, path, reached));
      }
    }
    // Now, disjoin the path (as only one can be executed, hence all other should be false)
    PathFormula result ;
    ArrayList<PathFormula> pfList = Lists.newArrayList(allPathFormulae);
    if (allPathFormulae.size() == 1) {
      result = pfList.get(0);
    } else {
      PathFormula first = pfList.get(0);
      for (int i = 1; i < pfList.size(); i++) {
        first = pfManager.makeOr(first, pfList.get(i));
      }
      result = first;
    }



    // FIXME: ITE einbauen
    if(loopHead.isLoopStart() && loopHead.getNumLeavingEdges() == 2 && CFAUtils.allLeavingEdges(loopHead).allMatch(e -> e instanceof CAssumeEdge)){

      CAssumeEdge outEdge;
      if (((CAssumeEdge) loopHead.getLeavingEdge(0)).getTruthAssumption()) {
        outEdge = (CAssumeEdge) loopHead.getLeavingEdge(0);
      } else {
        outEdge = (CAssumeEdge) loopHead.getLeavingEdge(1);
      }
      BooleanFormula loopCondition =
          converter.makePredicate(
              outEdge.getExpression(),
              outEdge,
              loopHead.getFunctionName(),
              pCUrrentPathFormula.getSsa().builder());
      BooleanFormula oldANdLoopIteration =
          fmgr.makeAnd(pCUrrentPathFormula.getFormula(), result.getFormula());
      BooleanFormula oldAndNOLoopIteration =
          fmgr.makeAnd(
              pCUrrentPathFormula.getFormula(),
              mapSSAIndicesfromFIrstTOSecond(pCUrrentPathFormula, result));
      BooleanFormula ite =
          fmgr.getBooleanFormulaManager()
              .ifThenElse(loopCondition, oldANdLoopIteration, oldAndNOLoopIteration);
      result =
          new PathFormula(
              ite,
              pf1LoopITeration.getSsa(),
              pf1LoopITeration.getPointerTargetSet(),
              pf1LoopITeration.getLength());

    }else {
      //We cannot build an ite
      logger.log(Level.WARNING, String.format("CAnnot build ITE for loophead %s!",loopHead));

    }
    return result;
  }

  /** Creates assignemnts for each var xi in pOld and xj in PNew, s.t. xi=xj
   * @param pCUrrentPathFormula
   * @param pPf1LoopITeration
   * @return
   */
  private BooleanFormula mapSSAIndicesfromFIrstTOSecond(
      PathFormula pOld, PathFormula pNew) {
    //Take all variables from the old path formula (leading o the loop, remove all ssa indices
  Set<Formula> varsInOld = fmgr.extractVariables(pOld.getFormula()).entrySet().stream().map(e -> fmgr.uninstantiate(e.getValue())).collect(Collectors.toSet());
  // for ech variable, build an assignent, where the lhs has the new ssa indiex and the rhs the old

  Set<BooleanFormula> equations = varsInOld.stream().map(var -> fmgr.makeEqual(fmgr.instantiate(var,pNew.getSsa()),fmgr.instantiate(var,pOld.getSsa()))).collect(Collectors.toSet());
    return fmgr.getBooleanFormulaManager().and(equations);
  }

  private Optional<AbstractState> getStateWithAssertion(ARGPath pPath) {
    for (Pair<ARGState, ARGState> pair : pPath.getStatePairs()) {
      CFAEdge e = pair.getFirst().getEdgeToChild(pair.getSecond());
      if (Objects.nonNull(e)
          && AbstractStates.extractLocation(pair.getFirst())
              .getFunctionName()
              .equals("__VERIFIER_assert")) {
        if (e instanceof AssumeEdge
            && ((AssumeEdge) e).getTruthAssumption()) { // as the function says: if (! cond) {Error}
          return Optional.ofNullable(pair.getFirst());
        }
      }
    }
    return Optional.empty();
  }

  private List<AbstractState> filterAbstractStatesOnPath(ARGPath path) {
    return path.asStatesList()
        .stream()
        .filter(s -> isAbstractionState(s) && !path.getFirstState().equals(s))
        .collect(Collectors.toList());
  }

  private List<AbstractState> filterAbstractStatesOnPathWOLast(ARGPath path) {
    return path.asStatesList()
        .stream()
        .filter(
            s ->
                isAbstractionState(s)
                    && !path.getFirstState().equals(s)
                    && !path.getLastState().equals(s))
        .collect(Collectors.toList());
  }

  private PathFormula getFuncDeclForNode(CFANode loopHead, PathFormula initPF) {
    FunctionDeclaration<BooleanFormula> invDecl =
        fmgr.getFunctionFormulaManager()
            .declareUF(
                String.format(INV_FUNCTION_NAMING_SCHEMA, getLineNumberForNode(loopHead)),
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
      int lineNumberOfLoopHead = getLineNumberForNode(pLoopHead);
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

  private int getLineNumberForNode(CFANode pLoopHead) {
    int lineNumberOfLoopHead = -1;
    for (int i = 0; i < pLoopHead.getNumEnteringEdges(); i++) {
      CFAEdge e = pLoopHead.getEnteringEdge(i);
      if (e.getLineNumber() > 0) {
        lineNumberOfLoopHead = e.getLineNumber();
      }
    }
    return lineNumberOfLoopHead;
  }

  private Optional<PathFormula> getPreserveConditionForLoop(
      CFANode loopHead, Set<CFANode> nodesInLoop, AbstractState pAbstractState, ReachedSet reached)
      throws CPAException {
    List<PathFormula> preserveCondition = new ArrayList<>();
    for (int i = 0; i < loopHead.getNumEnteringEdges(); i++) {
      CFANode predOfLoopHead = loopHead.getEnteringEdge(i).getPredecessor();
      if (nodesInLoop.contains(predOfLoopHead)) {
        // We see a path within the loop:
        Optional<PathFormula> pf = getPathFormulaOfNode(predOfLoopHead, reached, pAbstractState);
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
      CFANode loopHead, AbstractState pLoopHeadAbstractState) {

    @Nullable
    PredicateAbstractState loopHeadPredState =
        AbstractStates.extractStateByType(pLoopHeadAbstractState, PredicateAbstractState.class);
    // Ensure that this is a abstraction location and the loop head is visited only once (no loop
    // iteration is taken)
    if (loopHeadPredState.isAbstractionState()
        && loopHeadPredState.getAbstractionLocationsOnPath().getOrDefault(loopHead, 0) < 2) {
      return Optional.of(loopHeadPredState.getAbstractionFormula().getBlockFormula());
    } else {
      return Optional.empty();
    }
  }
  /**
   * Looks for all nodes that leaf the loop and takes the ssa map of these nodes
   *
   * @param pLoopHead the loop head node
   * @param pNodesInLoop all nodes in the loop
   * @param pState the abstract state of the loop head
   * @return a pair of abstract state and ssa map of the edge leaving the loop
   */
  private Optional<Pair<AbstractState, SSAMap>> getSSAForLoophead(
      CFANode pLoopHead, Set<CFANode> pNodesInLoop, AbstractState pState) {
    Optional<CFANode> toProcess = StrongestPostUtils.getLoopBranchForLoopHead(pLoopHead, logger);

    if (toProcess.isEmpty()) {
      return Optional.empty();
    }
    Optional<AbstractState> succAbsStateOfLoopHead =
        StrongestPostUtils.getAbstractStateForLoopHead(
            AbstractStates.extractStateByType(pState, ARGState.class), toProcess.get(), logger);
    if (succAbsStateOfLoopHead.isEmpty()) {
      return Optional.empty();
    }

    for (int i = 0; i < toProcess.get().getNumLeavingEdges(); i++) {
      CFANode succOfLoopHead = toProcess.get().getLeavingEdge(i).getSuccessor();

      if (!pNodesInLoop.contains(succOfLoopHead)) {
        // We see a path out of the loop
        Optional<PathFormula> pf =
            getPathFormulaOfLoopheadSuccessor(succOfLoopHead, succAbsStateOfLoopHead.get());
        if (pf.isPresent()) {
          // As pSttate is the loopHead, we nned to return the ssamap wrt. the loophead!
          return Optional.of(Pair.of(pState, pf.get().getSsa()));
        }
      }
    }

    return Optional.empty();
  }

  private SSAMap getSSAMapForAbstratLocatons(Set<Pair<AbstractState, SSAMap>> pSsaMaps4Loophead) {
    List<Pair<AbstractState, SSAMap>> rootNodes = new ArrayList<>();

    for (Pair<AbstractState, SSAMap> pair : pSsaMaps4Loophead) {
      // Check, if the current node is covered:
      if (!AbstractStates.extractStateByType(pair.getFirst(), ARGState.class).isCovered()) {
        rootNodes.add(pair);
      }
    }
    if (rootNodes.size() == 1) {
      return rootNodes.get(0).getSecond();
    } else {
      SSAMap res = SSAMap.emptySSAMap();
      final List<MapsDifference.Entry<String, Integer>> symbolDifferences = new ArrayList<>();
      for (Pair<AbstractState, SSAMap> n : rootNodes) {
        res = SSAMap.merge(res, n.getSecond(), collectMapsDifferenceTo(symbolDifferences));
      }
      return res;
    }
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
    //    for (Loop loop : loopStruct.getAllLoops()) {
    //      if (loopheads
    //          .stream()
    //          .anyMatch(
    //              head -> !loop.getLoopHeads().contains(head) &&
    // loop.getLoopNodes().contains(head))) {
    //        logger.log(
    //            Level.WARNING,
    //            "The program contains nested loops. This is currently not supported, hence
    // aborting!");
    //        throw new CPAException("Currently, only programs without neaded loops are
    // supported!");
    //      }
    //    }
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
          //          Map<CFANode, List> callStack = new HashMap<>();

          @Override
          public Iterable<CFAEdge> apply(CFANode pT) {
            // To avoid confusions with method calls!
            if (pT.getLeavingSummaryEdge() != null) {
              return Lists.newArrayList(pT.getLeavingSummaryEdge());
            }

            FluentIterable<CFAEdge> edges = CFAUtils.allLeavingEdges(pT);
            return edges;
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

  /**
   * Returns the path formula of the child node with the licaton node of the given arg state
   *
   * @param node the successor CFANode of the loop head leaving the node
   * @param argStatetOfLoopHead the abstract state of the loop
   * @return a path formula, if the arg state has a child associated to node
   */
  private Optional<PathFormula> getPathFormulaOfLoopheadSuccessor(
      CFANode node, AbstractState argStatetOfLoopHead) {

    for (AbstractState s :
        AbstractStates.extractStateByType(argStatetOfLoopHead, ARGState.class).getChildren()) {
      if (AbstractStates.extractLocation(s).equals(node)) {
        PredicateAbstractState pred =
            AbstractStates.extractStateByType(s, PredicateAbstractState.class);

        return Optional.of(pred.getPathFormula());
      }
    }
    return Optional.empty();
  }

  private Optional<PathFormula> getPathFormulaOfNode(
      CFANode pPredOfLoopHead, ReachedSet pReached, AbstractState partenARGState) {
    Collection<AbstractState> toProcess = filter(pPredOfLoopHead, pReached);
    @Nullable ARGState argChild = AbstractStates.extractStateByType(partenARGState, ARGState.class);
    for (AbstractState s : toProcess) {

      final Collection<ARGState> children =
          AbstractStates.extractStateByType(s, ARGState.class).getChildren();
      // We need to check that the argstate with the pathformula is either a direct successor of the
      // loop node process
      // or it has a children covered by the parent node (which is the same but not merged to have a
      // tree)
      if (children.contains(argChild)
          || children
              .stream()
              .anyMatch(
                  child -> child.isCovered() && child.getCoveringState().equals(partenARGState))) {

        PredicateAbstractState pred =
            AbstractStates.extractStateByType(s, PredicateAbstractState.class);

        return Optional.of(pred.getPathFormula());
      }
    }
    return Optional.empty();
  }

  private PathFormula addBranchingCondition(PathFormula pathFormula, ARGPath path)
      throws UnrecognizedCodeException, InterruptedException {
    // Add the branching conditions
    List<BooleanFormula> pathConditions = Lists.newArrayList();

    PathIterator pathIterator = path.pathIterator();
    while (pathIterator.hasNext()) {
      Pair<ARGState, CFAEdge> e =
          Pair.of(pathIterator.getAbstractState(), pathIterator.getOutgoingEdge());
      if (e.getSecond() instanceof CAssumeEdge) {
        CAssumeEdge assume = (CAssumeEdge) e.getSecond();
        @Nullable
        PredicateAbstractState predState =
            AbstractStates.extractStateByType(e.getFirst(), PredicateAbstractState.class);
        BooleanFormula pred =
            converter.makePredicate(
                assume.getExpression(),
                assume,
                AbstractStates.extractLocation(e.getFirst()).getFunctionName(),
                predState.getPathFormula().getSsa().builder());
        if (assume.getTruthAssumption()) {

          pathConditions.add(pred);
        } else {
          pathConditions.add(fmgr.getBooleanFormulaManager().not(pred));
        }
      }
      pathIterator.advance();
    }

    BooleanFormula and = fmgr.getBooleanFormulaManager().and(pathConditions);

    final BooleanFormula newPF = fmgr.makeAnd(and, pathFormula.getFormula());
    return new PathFormula(
        newPF, pathFormula.getSsa(), pathFormula.getPointerTargetSet(), pathFormula.getLength());
  }
}
