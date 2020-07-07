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
package org.sosy_lab.cpachecker.cpa.extinvgen;

import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CParser;
import org.sosy_lab.cpachecker.cfa.CProgramScope;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.parser.Scope;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.DelegateAbstractDomain;
import org.sosy_lab.cpachecker.core.defaults.StopSepOperator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.specification.Specification;
import org.sosy_lab.cpachecker.cpa.automaton.CParserUtils;
import org.sosy_lab.cpachecker.cpa.automaton.CParserUtils.ParserTools;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTrees;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;

//@Options(prefix = "cpa.extinvgen")
public abstract class ExternalInvToARGCPA implements ConfigurableProgramAnalysis {

  // @Option(secure = true, description = "Path to auxillary invariants generated by Seahorn.")
  // @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  // @Nullable
  // private Path path2InvFile = null;

  Map<CFANode, ExpressionTree<AExpression>> globalInvMap = new HashMap<>();

  private static final String TRUE = "true";
  private static final String FALSE = "false";
  CtoFormulaConverter converter;
  Multimap<Integer, Pair<String, String>> mapping;
  Configuration config;
  LogManager logger;
  ShutdownNotifier shutdownNotifier;
  CFA cfa;
  Specification specification;

  private AbstractDomain abstractDomain;

  /**
   * Gets a factory for creating InvariantCPAs.
   *
   * @return a factory for creating InvariantCPAs.
   */
  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(ExternalInvToARGCPA.class);
  }

  public ExternalInvToARGCPA(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      CFA pCfa,
      Specification pSpecification) {
    config = pConfig;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
    cfa = pCfa;
    specification = pSpecification;
    abstractDomain = DelegateAbstractDomain.<ExternalnvToArgState>getInstance();
  }

  protected void injectAndParseInvariants(Multimap<Integer, Pair<String, String>> pMapping)
      throws CPAException {
    mapping = pMapping;
    try {
      Map<Integer, Set<CFAEdge>> lineToEdges = getMappingLinesToEdges(cfa);

      // afterwards, find the node where the invariants belong to.

      // Since we only want to evaluate the cases where the invariant is in fact helpful,
      // meaning that at least one invariant is non-trivial and hence unequal to "true/false", we
      // can get better results and abort, if only trivial invariants are generated:
      boolean nonTrivialInvariantGenerated = false;

      for (Entry<Integer, Pair<String, String>> inv : mapping.entries()) {

        if (inv.getValue().getSecond().strip().equalsIgnoreCase(TRUE)
            || inv.getValue().getSecond().strip().equalsIgnoreCase(FALSE)) {
          // No need to add true or false
          continue;
        }

        int lineNumber = inv.getKey();
        if (!lineToEdges.containsKey(lineNumber)) {
          logger.log(
              Level.FINE,
              "Cannot parse the invariant, because no matching line number was found: "
                  + inv.toString());
          continue;
        }

        // Determine the minimal Start and maximal end offset for a given line (if there are more
        // statements present

        logger.log(
            Level.INFO,
            "starting parsing inv ",
            inv.getValue().getSecond(),
            "to location",
            lineNumber,
            " having %d many locations associated",
            lineToEdges.get(lineNumber).size());

        for (CFAEdge edge : lineToEdges.get(lineNumber)) {
          ExpressionTree<AExpression> invariantInC =
              parseInv2Tree(inv.getValue().getSecond(), edge.getSuccessor().getFunction());

          if (!invariantInC.equals(ExpressionTrees.getTrue())) {
            nonTrivialInvariantGenerated = true;

            logger.log(
                Level.INFO,
                "adding inv ",
                invariantInC.toString(),
                "to location",
                edge.getSuccessor());
            globalInvMap.put(edge.getSuccessor(), invariantInC);
          }
        }
      }
      if (!nonTrivialInvariantGenerated) {
        throw new CPAException("There were only trivila invariants generated, hence aborting");
      }
    } catch (InterruptedException e) {
      logger.log(Level.WARNING, "an error occured while parsing the invariants");
    }
    // logger.log(Level.INFO, globalInvMap.toString());
  }

  private ExpressionTree<AExpression> parseInv2Tree(String pInv, AFunctionDeclaration function)
      throws InterruptedException {

    CParser parser =
        CParser.Factory.getParser(
            logger,
            CParser.Factory.getDefaultOptions(),
            cfa.getMachineModel(),
            shutdownNotifier);
    ParserTools parserTools =
        ParserTools.create(ExpressionTrees.newFactory(), cfa.getMachineModel(), logger);
    Scope candidateScope = new CProgramScope(cfa, logger).withFunctionScope(function.getName());

    ExpressionTree<AExpression> invariant =
        CParserUtils.parseStatementsAsExpressionTree(
            Sets.newHashSet(pInv),
            Optional.of(function.getName()),
            parser,
            candidateScope,
            parserTools);

    return invariant;
  }

  // private CExpression parseInv2C(String pInv, AFunctionDeclaration function) {
  // ExpressionTree<AExpression> invariant = parseInv2Tree(pInv, function);
  //
  // if (invariant instanceof LeafExpression) {
  // CExpression invInC =
  // (CExpression) ((LeafExpression<AExpression>) invariant).getExpression();
  // return invInC;
  //
  // } else {
  // throw new IllegalArgumentException("Seahorn cannot handle java expressions");
  // }
  // }

  @Override
  public AbstractDomain getAbstractDomain() {
    return abstractDomain;
  }

  @Override
  public TransferRelation getTransferRelation() {
    return new ExternalInvToArgTransferRelation(globalInvMap, ExpressionTrees.getTrue());
  }

  @Override
  public MergeOperator getMergeOperator() {
    return new MergeOperator() {

      @Override
      public AbstractState merge(AbstractState pState1, AbstractState pState2, Precision pPrecision)
          throws CPAException, InterruptedException {
        return pState2;
      }
    };
  }

  @Override
  public StopOperator getStopOperator() {
    return new StopSepOperator(abstractDomain);
  }

  @Override
  public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition)
      throws InterruptedException {
    return new ExternalnvToArgState(globalInvMap, ExpressionTrees.getTrue(), pNode);
  }

  /**
   *
   * Computes for each source code line the edges associated to that line
   *
   * @param pCfa the cfa to search in
   * @return map containing the mapping
   */
  private Map<Integer, Set<CFAEdge>> getMappingLinesToEdges(CFA pCfa) {
    Map<Integer, Set<CFAEdge>> lineToEdgesOfMain = new HashMap<>();
    for (CFANode n : pCfa.getAllNodes()) {

      for (int i = 0; i < n.getNumEnteringEdges(); i++) {
        CFAEdge enteringEdge = n.getEnteringEdge(i);
        if (lineToEdgesOfMain.containsKey(enteringEdge.getLineNumber())) {
          lineToEdgesOfMain.get(enteringEdge.getLineNumber()).add(enteringEdge);
        } else {
          HashSet<CFAEdge> edges = new HashSet<>();
          edges.add(enteringEdge);
          lineToEdgesOfMain.put(enteringEdge.getLineNumber(), edges);
        }

      }
    }
    // Cleanup due to performance reasons
    // cleanup(lineToEdgesOfMain);
    reapir(lineToEdgesOfMain);
    // System.out.println(lineToEdgesOfMain.toString());
    return lineToEdgesOfMain;
  }

  private  void reapir(Map<Integer, Set<CFAEdge>> pLineToEdgesOfMain) {
    for (Entry<Integer, Set<CFAEdge>> entry : pLineToEdgesOfMain.entrySet()) {
      if(entry.getValue().size()>1) {
        Set<CFAEdge> set = entry.getValue();
        CFANode firstFrom = set.stream().findAny().get().getPredecessor();
        boolean isBranchHead =
            entry.getValue()
                .parallelStream()
                .allMatch(
                    e -> e.getEdgeType().equals(CFAEdgeType.AssumeEdge)
                        && e.getPredecessor().equals(firstFrom));
        if(isBranchHead) {
          for (int i = 0; i < firstFrom.getNumEnteringEdges(); i++) {
            set.add(firstFrom.getEnteringEdge(i));
          }

          pLineToEdgesOfMain.replace(entry.getKey(), set);
        }
        }
      }


  }

  public Map<CFANode, ExpressionTree<AExpression>> getGlobalInvMap() {
    return globalInvMap;
  }

//  private void cleanup(Map<Integer, Set<CFAEdge>> pLineToEdgesOfMain) {
//
//    // IF any location has an edge, that is an loop enter head, remove the other locations
//    for (Entry<Integer, Set<CFAEdge>> entry : pLineToEdgesOfMain.entrySet()) {
//      List<CFAEdge> loopHeads =
//          entry.getValue()
//              .parallelStream()
//              .filter(edge -> edge instanceof BlankEdge && edge.getPredecessor().isLoopStart())
//              .collect(Collectors.toList());
//      if (loopHeads.size() > 0) {
//        CFAEdge temp = loopHeads.get(0).getSuccessor().getLeavingEdge(0);
//        pLineToEdgesOfMain.replace(entry.getKey(), Sets.newHashSet(loopHeads.get(0)));
//      }
//    }
  //
  // }

}
