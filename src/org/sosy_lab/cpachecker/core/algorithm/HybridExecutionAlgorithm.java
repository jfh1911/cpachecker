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
/**
 * The core algorithms of CPAchecker.
 */
package org.sosy_lab.cpachecker.core.algorithm;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;

import javax.annotation.Nullable;

import org.apache.commons.math.distribution.PascalDistribution;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.core.AnalysisDirection;
import org.sosy_lab.cpachecker.core.algorithm.ParallelAlgorithm.ReachedSetUpdateListener;
import org.sosy_lab.cpachecker.core.algorithm.ParallelAlgorithm.ReachedSetUpdater;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.WrapperCPA;
import org.sosy_lab.cpachecker.core.interfaces.WrapperPrecision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGCPA;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.arg.path.ARGPath;
import org.sosy_lab.cpachecker.cpa.automaton.InvalidAutomatonException;
import org.sosy_lab.cpachecker.cpa.composite.CompositeCPA;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.hybrid.HybridAnalysisCPA;
import org.sosy_lab.cpachecker.cpa.hybrid.HybridAnalysisState;
import org.sosy_lab.cpachecker.cpa.hybrid.HybridAnalysisStatistics;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFATraversal;
import org.sosy_lab.cpachecker.util.CFATraversal.EdgeCollectingCFAVisitor;
import org.sosy_lab.cpachecker.util.CPAs;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.predicates.pathformula.CachingPathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManagerImpl;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This class implements a CPA algorithm based on the idea of concolic execution It traversals the
 * CFA via DFS and introduces new edges for the ARG on branching states in order to cover more
 * branches
 */
public final class HybridExecutionAlgorithm implements Algorithm, ReachedSetUpdater {

  @Options(prefix = "hybridExecution")
  public static class HybridExecutionAlgorithmFactory implements AlgorithmFactory {

    @Option(
      secure = true,
      name = "useValueSets",
      description = "Whether to use multiple values on a state.")
    private boolean useValueSets = false;

    private final Algorithm algorithm;
    private final CFA cfa;
    private final ConfigurableProgramAnalysis cpa;
    private final LogManager logger;
    private final Configuration configuration;
    private final ShutdownNotifier notifier;

    /**
     *
     * @param pAlgorithm        The composed algorithm created up to this point
     * @param pCFA              The cfa for the code to be checked
     * @param pLogger           The logger instance
     * @param pConfiguration    The applications configuration
     * @param pShutdownNotifier A shutdown notifier
     * @throws InvalidConfigurationException Throws InvalidConfigurationException if injection of
     *                                       the factories options fails
     */
    public HybridExecutionAlgorithmFactory(
        Algorithm pAlgorithm,
        CFA pCFA,
        ConfigurableProgramAnalysis pCpa,
        LogManager pLogger,
        Configuration pConfiguration,
        ShutdownNotifier pShutdownNotifier)
        throws InvalidConfigurationException {
      pConfiguration.inject(this);
      this.algorithm = pAlgorithm;
      this.cfa = pCFA;
      this.cpa = pCpa;
      this.logger = pLogger;
      this.configuration = pConfiguration;
      this.notifier = pShutdownNotifier;
    }

    @Override
    public Algorithm newInstance() {
      try {
        return new HybridExecutionAlgorithm(
            algorithm,
            cfa,
            cpa,
            logger,
            configuration,
            notifier,
            useValueSets);
      } catch (InvalidConfigurationException e) {
        // this is a bad place to catch an exception
        logger.log(Level.SEVERE, e.getMessage());
      }
      // meh...
      return algorithm;
    }

  }

  private final Algorithm algorithm;
  private final CFA cfa;
  private final HybridAnalysisCPA cpa;
  private final int hybridAnalysisIndex;
  private final LogManager logger;

  private final Solver solver;
  private final FormulaManagerView formulaManagerView;
  private final PathFormulaManager pathFormulaManager;
  private final HybridAnalysisStatistics statistics;

  private final Splitter FUNCTION_SCOPE_SPLITTER = Splitter.on("::");

  // we could run the search with several values satisfying certain conditions to achieve a broader coverage
  // this must be experimental validated (in theory it is very easy to find several variable values for a specific state that will later on lead to different executions)
  /*
   * here we might have the precondition, that y is never less than 1 (meaning, there is no path through the code that might lead to y being smaller than 1)
   * int calc(int x, int y) {
   *  int result = 0;
   *  if(x <= 0) {
   *    return 0; // we want the calculated value to never be smaller than 0
   *  }
   *
   *  result = x * y;
   *  if(result > x) {
   *    // at this point, we know that y must have been greater than 1
   *    return result;
   *  }
   *
   *  return x * predefinedConstant; // so if y was actually 1, we multiply x with a predefined constant value (for some reasons ;) )
   *
   * }
   *
   * multiple value assignments for this example:
   * (1) x = 3, y = 1 -> this leads to 3* predefinedConstant
   * (2) x = 3, y = 2 -> this leads to 6
   * we could probably use some sort of negation heuristic for existing assignments like this
   * negateOrMinimize(assignments(1)):
   * (3) x = -3, y = 1 -> leads to 0
   * here y is not negated, because of precondition being y >= 1
   *
   * with these 3 assigments we catch every path through the method
   *
   * thus, without any further investigation (and runs of the cpa algorithm), we might be able to reach many different states
   * by simply executing the search strategy for all those assignments (maybe even in parallel ...)
   *
   */
  @SuppressWarnings("unused")
  private boolean useValueSets;
  private final List<ReachedSetUpdateListener> reachedSetUpdateListeners;

  private HybridExecutionAlgorithm(
      Algorithm pAlgorithm,
      CFA pCFA,
      ConfigurableProgramAnalysis pCpa,
      LogManager pLogger,
      Configuration pConfiguration,
      ShutdownNotifier pNotifier,
      boolean pUseValueSets)
      throws InvalidConfigurationException {

    this.algorithm = pAlgorithm;
    this.cfa = pCFA;

    Pair<HybridAnalysisCPA, Integer> pair = hybridAnalysisCPAIndexPair(pCpa);

    this.cpa = pair.getFirst();
    this.hybridAnalysisIndex = pair.getSecond();

    this.logger = pLogger;
    this.useValueSets = pUseValueSets;
    this.reachedSetUpdateListeners = new ArrayList<>();

    this.solver = Solver.create(pConfiguration, pLogger, pNotifier);
    this.formulaManagerView = solver.getFormulaManager();

    this.pathFormulaManager = new CachingPathFormulaManager(
        new PathFormulaManagerImpl(
            formulaManagerView,
            pConfiguration,
            pLogger,
            pNotifier,
            pCFA,
            AnalysisDirection.FORWARD));
            
    statistics = cpa.getStatisticsInstance();
  }

  @Override
  public AlgorithmStatus run(ReachedSet pReachedSet)
      throws CPAException, InterruptedException {

    logger.log(Level.INFO, "Hybrid Execution algorithm started.");

    // first we need to collect all assume edges from the cfa to distinguish between already visited and new paths
    CFATraversal traversal = CFATraversal.dfs();
    EdgeCollectingCFAVisitor edgeCollectingVisitor = new EdgeCollectingCFAVisitor();
    CFANode startingNode = cfa.getMainFunction();
    traversal.traverseOnce(startingNode, edgeCollectingVisitor);
    final List<CAssumeEdge> allAssumptions = extractAssumptions(edgeCollectingVisitor.getVisitedEdges());

    logger.log(Level.FINEST, "Assume edges from program cfa collected.");

    return runInternal(pReachedSet, allAssumptions);
  }

  @Override
  public void register(ReachedSetUpdateListener pReachedSetUpdateListener) {

    if(algorithm instanceof ReachedSetUpdater) {
      ((ReachedSetUpdater) algorithm).register(pReachedSetUpdateListener);
    }

    reachedSetUpdateListeners.add(pReachedSetUpdateListener);
  }

  @Override
  public void unregister(ReachedSetUpdateListener pReachedSetUpdateListener) {

    if(algorithm instanceof ReachedSetUpdater) {
      ((ReachedSetUpdater) algorithm).unregister(pReachedSetUpdateListener);
    }

    reachedSetUpdateListeners.remove(pReachedSetUpdateListener);
  }

  /**
   * Internal implementation of the algorithm
   * @param pReachedSet The current reachedSet
   * @param pAllAssumptions All assumptions occurring in the cfa
   * @return An algorithm status
   */
  private AlgorithmStatus runInternal(ReachedSet pReachedSet, List<CAssumeEdge> pAllAssumptions)
      throws CPAException, InterruptedException {
    
    // start with good status
    AlgorithmStatus currentStatus = AlgorithmStatus.SOUND_AND_PRECISE;

    while(checkContinue(pReachedSet)) {

      currentStatus = algorithm.run(pReachedSet);
      notifyListeners(pReachedSet);

      final Set<ARGState> allARGStates = collectARGStates(pReachedSet);

      // get all bottom states (has no children and is not part of the wait list)
      final Set<ARGState> bottomStates = allARGStates
          .stream()
          .filter(argState -> !argState.isDestroyed() 
                  && argState.getChildren().isEmpty()
                  && !pReachedSet.getWaitlist().contains(argState))
          .collect(Collectors.toSet());

      // there is nothing left to do in this run
      if(bottomStates.isEmpty()){
        continue;
      }

      @Nullable
      Pair<CAssumeEdge, ARGState> nextAssumptionContext = getNextAssumptionWithPredecessor(
        pAllAssumptions,
        allARGStates,
        bottomStates);

      if(nextAssumptionContext == null) {
        // no more assumptions left

        break;
      }

      statistics.incrementAssumptionFound();
      CAssumeEdge nextAssumptionEdge = nextAssumptionContext.getFirst();
      ARGState priorAssumptionState = nextAssumptionContext.getSecond();

      // remove the current assumedge from all edges
      pAllAssumptions.remove(nextAssumptionEdge);

      // the path from a parent state to the next flip assumption
      ARGPath pathToAssumption = ARGUtils.getOnePathTo(priorAssumptionState);

      assert priorAssumptionState.equals(pathToAssumption.getLastState());

      List<CFAEdge> pathEdges = Lists.newArrayList(pathToAssumption.getInnerEdges());

      // we need to add the assumption to the edge path
      pathEdges.add(nextAssumptionEdge);

      // build path formula with edge path containing the new assumption
      BooleanFormula formulaToCheck = buildPathFormula(pathEdges);

      try {

        boolean satisfiable = !solver.isUnsat(formulaToCheck);

        // get assignments for the new path containing the flipped assumption
        if(satisfiable) {

          statistics.incrementFeasiblePathFound();
          try {

            tryAddNewStateToARG(formulaToCheck, priorAssumptionState, pReachedSet);

          } catch(InvalidAutomatonException iae) {
            throw new CPAException("Error occurred while parsing the value assignments into assumption expressions.", iae);
          }

        } else {

          // not satisfiable
          logger.log(Level.INFO, String.format("The boolean formula %s is not satisfiable for the solver", formulaToCheck));
        }

      } catch(SolverException sException) {
        throw new CPAException("Exception occurred in SMT-Solver.", sException);
      }

    }

    return currentStatus;
  }

  @Nullable
  private Pair<CAssumeEdge, ARGState> getNextAssumptionWithPredecessor(
    List<CAssumeEdge> pAllAssumptions,
    Collection<ARGState> pStates,
    Set<ARGState> pBottomStates) {

      AssumeEdgeCollectingARGVisitor visitor = new AssumeEdgeCollectingARGVisitor(pBottomStates);
      visitor.collectAssumeEdges();
      Set<CAssumeEdge> visitedEdges = visitor.getCollectedEdges();

      pAllAssumptions.removeAll(visitedEdges);

      if(pAllAssumptions.isEmpty()) {
        return null;
      }

      List<CAssumeEdge> coveredEdges = Lists.newArrayList();
      @Nullable
      Pair<CAssumeEdge, ARGState> result = null;

      for(CAssumeEdge nextAssumptionEdge : pAllAssumptions) {

        CFANode assumptionPredecessor = nextAssumptionEdge.getPredecessor();

        for(ARGState nextState : pStates) {

          // check for location
          CFANode stateNode = AbstractStates.extractLocation(nextState);
          if(assumptionPredecessor.equals(stateNode)) {

            // check for child state with assume edge
            @Nullable
            ARGState childState = getChildStateForAssumption(nextState, nextAssumptionEdge);
            if(childState == null) {
              result = Pair.of(nextAssumptionEdge, nextState);
            } else {
              // assumption is covered, path has not yet reached bottom state
              coveredEdges.add(nextAssumptionEdge);
            }

            // nodes match
            break;
          }
        }
        if(result != null) {
          break;
        }
      }

      pAllAssumptions.removeAll(coveredEdges);

      return result;
  }

  private void tryAddNewStateToARG(
      BooleanFormula pFormula,
      ARGState pPriorAssumptioState,
      ReachedSet pReachedSet)
      throws InterruptedException, SolverException, InvalidAutomatonException {

    try (ProverEnvironment proverEnvironment = solver
        .newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      proverEnvironment.push(pFormula);
      Preconditions.checkState(
          !proverEnvironment.isUnsat(),
          String.format("Formula wasn't pre-checked and is not satisfiable. %s%s", System.lineSeparator(), pFormula));
      // retrieve the new assignments
      Collection<ValueAssignment> valueAssignments = proverEnvironment.getModelAssignments();
      statistics.nextNumOfAssignments(valueAssignments.size());

      // convert all value assignments (their respective formulas) to expressions
      Set<CBinaryExpression> assumptions = parseAssignments(valueAssignments);

      HybridAnalysisState newState = new HybridAnalysisState(assumptions);

      // extract states from composite state
      CompositeState compositeState = AbstractStates
          .extractStateByType(pPriorAssumptioState, CompositeState.class);

      List<AbstractState> wrappedStates = compositeState.getWrappedStates()
          .stream()
          .filter(state -> !HybridAnalysisState.class.isInstance(state))
          .collect(Collectors.toList());

      // CompositeTransferRelation relies on the order .... this is bad
      wrappedStates.add(hybridAnalysisIndex, newState);

      // fork ARGState with this new hybrid analysis state
      ARGState stateToAdd = pPriorAssumptioState.forkWithReplacements(
          Collections.singletonList(new CompositeState(wrappedStates)));

      // save to cast, priorAssumptionState is ARG state
      WrapperPrecision precision = (WrapperPrecision) pReachedSet.getPrecision(pPriorAssumptioState);
      pPriorAssumptioState.replaceInARGWith(stateToAdd);
      pReachedSet.add(stateToAdd, precision);
      pReachedSet.remove(pPriorAssumptioState);

    }

  }

  // builds the complete path formula for a path through the application denoted by the set of edges
  private BooleanFormula buildPathFormula(Collection<CFAEdge> pEdges)
      throws CPATransferException, InterruptedException {
    PathFormula formula = pathFormulaManager.makeEmptyPathFormula();

    pEdges = pEdges
        .stream()
        .filter(edge -> edge != null)
        .filter(edge -> !(edge.getEdgeType() == CFAEdgeType.BlankEdge))
        .collect(Collectors.toList());

    for(CFAEdge edge : pEdges) {
      formula = pathFormulaManager.makeAnd(formula, edge);
    }

    return formula.getFormula();
  }

  // notify listeners on update of the reached set
  private void notifyListeners(ReachedSet pReachedSet) {
    reachedSetUpdateListeners.forEach(listener -> listener.updated(pReachedSet));
  }

  // check if the algorithm should continue
  private boolean checkContinue(ReachedSet pReachedSet) {

    boolean check = true;
    // some checks for the state
    // update check

    check = check && pReachedSet.hasWaitingState();
    return check;
  }

  // helper method to extract assumptions from a given collection of cfa edges
  private List<CAssumeEdge> extractAssumptions(Collection<CFAEdge> pEdges) {
    return pEdges
      .stream()
      .filter(edge -> edge != null)
      .filter(edge -> edge.getEdgeType() == CFAEdgeType.AssumeEdge)
        // we need to invert on false truth assumption, because the information of the inversion gets lost otherwise
      .map(edge -> (CAssumeEdge) edge)
      .collect(Collectors.toList());
  }

  private Set<ARGState> collectARGStates(ReachedSet pReachedSet) {
    return pReachedSet
        .asCollection()
        .stream()
        .map(state -> AbstractStates.extractStateByType(state, ARGState.class))
        .filter(state -> state != null)
        .collect(Collectors.toSet());
  }

  private Set<CBinaryExpression> parseAssignments(Collection<ValueAssignment> pAssignments)
      throws InvalidAutomatonException {

    Set<CBinaryExpression> assumptions = Sets.newHashSet();
    for(ValueAssignment assignment : pAssignments) {
      String fixedName = removeSSAMapIndex(assignment);
      Collection<CBinaryExpression> assumptionCollection
          = cpa.getAssumptionParser()
            .parseAssumptions(String.format("%s=%s", fixedName, assignment.getValue()));
      assumptions.addAll(assumptionCollection);
      statistics.incrementSolverGenerated();
    }

    assert assumptions.size() == pAssignments.size();

    return assumptions;
  }

  private String removeSSAMapIndex(ValueAssignment pAssignment) {

    String name = pAssignment.getName();

    // function scoped
    if(name.contains("::")) {
      name = Iterables.get(FUNCTION_SCOPE_SPLITTER.split(name), 1);
    }

    int index = name.indexOf('@');

    if(index > 0) {
      name = name.substring(0, index);
    }

    return name;
  }

  private Pair<HybridAnalysisCPA, Integer> hybridAnalysisCPAIndexPair(ConfigurableProgramAnalysis pCpa) {

    // we first extract the ARGCPA to check all CPA preconditions
    ARGCPA argCpa = CPAs.retrieveCPA(pCpa, ARGCPA.class);
    Preconditions
        .checkNotNull(argCpa, "ARGCPA is required for HybridExecutionAlgorithm.");

    WrapperCPA wrapperCPA = argCpa.retrieveWrappedCpa(CompositeCPA.class);

    int index = 0;
    for(ConfigurableProgramAnalysis configurableProgramAnalysis : wrapperCPA.getWrappedCPAs()) {
      if(configurableProgramAnalysis instanceof HybridAnalysisCPA) {
        return Pair.of(((HybridAnalysisCPA)configurableProgramAnalysis), index);
      }
      index++;
    }

    throw new AssertionError("HybridExecutionAgorithm cannot be run without HybridAnalysisCPA.");
  }

  @Nullable
  private ARGState getChildStateForAssumption(ARGState pState, CAssumeEdge pAssumeEdge) {
    for(ARGState childState : pState.getChildren()) {
      for(CFAEdge edge : pState.getEdgesToChild(childState)) {
        if(edge.getEdgeType() == CFAEdgeType.AssumeEdge) {
          if(pAssumeEdge.equals(edge)) {
            return childState;
          }
        }
      }
    }
    return null;
  } 

  /**
   * This class traverses recursively over a set of ARGStates and their parents
   * and collects all Assumeedges on the  
   */
  private static class AssumeEdgeCollectingARGVisitor {

    private final ImmutableSet<ARGState> bottomStates;
    private Set<CAssumeEdge> collectedEdges;

    AssumeEdgeCollectingARGVisitor(Collection<ARGState> pBottomStates) {
      Preconditions.checkNotNull(pBottomStates, "Bottom states for ARGVisitor must not be null");
      bottomStates = ImmutableSet.copyOf(pBottomStates);
      collectedEdges = Sets.newHashSet();
    }

    void collectAssumeEdges() {
      for(ARGState bottomState : bottomStates) {
        visitState(bottomState);
      }
    }

    void visitState(ARGState pState) {

      for(ARGState parentState : pState.getParents()) {
        for(CFAEdge edge : parentState.getEdgesToChild(pState)) {
          if(edge.getEdgeType() ==  CFAEdgeType.AssumeEdge) {
            collectedEdges.add((CAssumeEdge)edge);
            break;
          }
        }
        visitState(parentState);
      }
    }

    Set<CAssumeEdge> getCollectedEdges() {
      return collectedEdges;
    }
  }

}
