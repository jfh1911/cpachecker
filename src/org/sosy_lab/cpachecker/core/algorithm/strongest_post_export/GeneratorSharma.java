// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
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
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.CPAs;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;

public class GeneratorSharma {

  public static final String INV_FUNCTION_NAMING_SCHEMA = "Inv_%s";

  private String outdirForExport = "output/";

  private final LogManager logger;

  private final CFA cfa;
  Solver solver;
  FormulaManagerView fmgr;

  private PathFormulaManager pfManager;

  private CtoFormulaConverter converter;

  private LoopStructure loopStruct;

  public GeneratorSharma(
      LogManager pLogger, ConfigurableProgramAnalysis pCpa, CFA pCfa, String outdirForExport)
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

        List<InterpolationTaskExchangeObject> tasksPerNode = new ArrayList<>();
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
    PathFormula result;
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
    if (loopHead.isLoopStart()
        && loopHead.getNumLeavingEdges() == 2
        && CFAUtils.allLeavingEdges(loopHead).allMatch(e -> e instanceof CAssumeEdge)) {

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

    } else {
      // We cannot build an ite
      logger.log(Level.WARNING, String.format("CAnnot build ITE for loophead %s!", loopHead));
    }
    return result;
  }

  /** Creates assignemnts for each var xi in pOld and xj in PNew, s.t. xi=xj */
  private BooleanFormula mapSSAIndicesfromFIrstTOSecond(PathFormula pOld, PathFormula pNew) {
    // Take all variables from the old path formula (leading o the loop, remove all ssa indices
    Set<Formula> varsInOld =
        fmgr.extractVariables(pOld.getFormula())
            .entrySet()
            .stream()
            .map(e -> fmgr.uninstantiate(e.getValue()))
            .collect(Collectors.toSet());
    // for ech variable, build an assignent, where the lhs has the new ssa indiex and the rhs the
    // old

    Set<BooleanFormula> equations =
        varsInOld
            .stream()
            .map(
                var ->
                    fmgr.makeEqual(
                        fmgr.instantiate(var, pNew.getSsa()), fmgr.instantiate(var, pOld.getSsa())))
            .collect(Collectors.toSet());
    return fmgr.getBooleanFormulaManager().and(equations);
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

  /** Finds all abstract states with same location as given */
  private Set<AbstractState> filter(CFANode pPredOfLoopHead, ReachedSet pReached) {
    return pReached
        .asCollection()
        .stream()
        .filter(s -> AbstractStates.extractLocation(s).equals(pPredOfLoopHead))
        .collect(Collectors.toSet());
  }
}
