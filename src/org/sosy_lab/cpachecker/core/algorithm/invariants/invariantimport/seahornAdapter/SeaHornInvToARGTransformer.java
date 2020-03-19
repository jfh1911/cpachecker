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
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.seahornAdapter;

import com.google.common.base.Throwables;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CParser;
import org.sosy_lab.cpachecker.cfa.CProgramScope;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.model.AssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.parser.Scope;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.core.AnalysisDirection;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.cpa.automaton.CParserUtils;
import org.sosy_lab.cpachecker.cpa.automaton.CParserUtils.ParserTools;
import org.sosy_lab.cpachecker.cpa.invariants.InvariantsCPA;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTrees;
import org.sosy_lab.cpachecker.util.expressions.LeafExpression;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaTypeHandler;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.FormulaEncodingOptions;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.cpachecker.util.variableclassification.VariableClassification;
import org.w3c.dom.Element;

public class SeaHornInvToARGTransformer extends InvariantsCPA {

  public static final String MAIN_FUNCTION = "main";
  private static final String TRUE = "true";
  private static final String FALSE = "false";
  CtoFormulaConverter converter;

  /**
   * Gets a factory for creating InvariantCPAs.
   *
   * @return a factory for creating InvariantCPAs.
   */
  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(SeaHornInvToARGTransformer.class)
        .withOptions(InvariantsOptions.class);
  }

  public SeaHornInvToARGTransformer(
      Configuration pConfig,
      LogManager pLogger,
      InvariantsOptions pOptions,
      ShutdownNotifier pShutdownNotifier,
      CFA pCfa,
      Specification pSpecification,
      Multimap<Integer, Pair<String, String>> mapping)
      throws InvalidConfigurationException {
    super(pConfig, pLogger, pOptions, pShutdownNotifier, pCfa, pSpecification);

    @SuppressWarnings("resource")
    Solver solver = Solver.create(pConfig, pLogger, pShutdownNotifier);

    FormulaManagerView fmgr = solver.getFormulaManager();

    FormulaEncodingOptions options = new FormulaEncodingOptions(pConfig);
    Optional<VariableClassification> a = Optional.of(VariableClassification.empty(pLogger));
    CtoFormulaTypeHandler pTypeHandler = new CtoFormulaTypeHandler(pLogger, pCfa.getMachineModel());
    converter =
        new CtoFormulaConverter(
            options,
            fmgr,
            pCfa.getMachineModel(),
            a,
            pLogger,
            pShutdownNotifier,
            pTypeHandler,
            AnalysisDirection.FORWARD);

    solver.close();

    // Now, associate the invariants to the nodes:
    Map<Integer, Set<CFAEdge>> lineToEdgesOfMain = new HashMap<>();
    getMappingLinesToEdgesOfFunction(pCfa, -1, lineToEdgesOfMain, MAIN_FUNCTION);

    // afterwards, find the node where the invariants belong to. If more than one, abort
    // Otherwise, add a path from entering node f main to that node

    // Get the edge containing the line number of the invariant, the starting node of the edge is
    // the desired one

    // FIXME: Since we only want to evaluate the cases where the invariant is in fact helpfull,
    // meaning that at least one invariant is non-trivial and hence unequal to "true/false", we can
    // save computation time (for the first evaluation and abort, if only non-trivial invariants are
    // generated:
    boolean nonTrivialInvariantGenerated = false;

    Set<Pair<CFAEdge, Element>> nodesWithOutInvToAdd = new HashSet<>();
    Map<CFANode, Element> nodesInvGeneratedFor = new HashMap<>();

    for (Entry<Integer, Pair<String, String>> inv : mapping.entries()) {

      if (inv.getValue().getSecond().strip().equalsIgnoreCase(TRUE)
          || inv.getValue().getSecond().strip().equalsIgnoreCase(FALSE)) {
        // No need to add true or false
        continue;
      }

      int lineNumber = inv.getKey();
      if (!lineToEdgesOfMain.containsKey(lineNumber)) {
        pLogger.log(
            Level.FINE,
            "Cannot parse the invariant, because no matching line number was found: "
                + inv.toString());
        continue;
      }
      nonTrivialInvariantGenerated = true;
      // Determine the minimal Start and maximal end offset for a given line (if there are more
      // statements present

      for (CFAEdge edge : lineToEdgesOfMain.get(lineNumber)) {
        AssumeEdge edgeWithInv =
            parseInv2C(inv.getValue().getSecond(), edge.getSuccessor().getFunction());
        try {
          super.injectInvariant(edge.getSuccessor(), edgeWithInv);
        } catch (UnrecognizedCodeException e) {
          pLogger.log(
              Level.WARNING,
              "The invariant",
              edgeWithInv.toString(),
              " could not be injected to node ",
              edge.getSuccessor(),
              " due to",
              Throwables.getStackTraceAsString(e));
        }
      }
    }

  }

  private AssumeEdge parseInv2C(String pInv, AFunctionDeclaration function) {

    try {
      CParser parser =
          CParser.Factory.getParser(
              LogManager.createTestLogManager(),
              CParser.Factory.getDefaultOptions(),
              MachineModel.LINUX32,
              ShutdownNotifier.createDummy());
      String code = "(( ( n + -x + -y  ) )<=0) & (( ( x + y + -n  ) )<=0)";

      ParserTools parserTools =
          ParserTools
              .create(ExpressionTrees.newFactory(), super.cfa.getMachineModel(), super.logManager);
      Scope candidateScope =
          new CProgramScope(super.cfa, super.logManager).withFunctionScope(function.getName());

      ExpressionTree<AExpression> invariant =
          CParserUtils.parseStatementsAsExpressionTree(
              Sets.newHashSet(pInv),
              Optional.of(function.getName()),
              parser,
              candidateScope,
              parserTools);

      // FIXME: Handle the case where the invariant cannot be parsed (ture is returned)

      if (invariant instanceof LeafExpression) {
        CExpression invInC =
            (CExpression) ((LeafExpression<AExpression>) invariant).getExpression();
        return new CAssumeEdge(
            invInC.toASTString(),
            FileLocation.DUMMY,
            new CFANode(function),
            new CFANode(function),
            invInC,
            true);

      } else {
        throw new IllegalArgumentException("Seahorn cannot handle java expressions");
      }

    } catch (InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
      return null;
    }

  }

  // public static void main(String[] args) {
  // try {
  // CParser parser =
  // CParser.Factory.getParser(
  // LogManager.createTestLogManager(),
  // CParser.Factory.getDefaultOptions(),
  // MachineModel.LINUX32,
  // ShutdownNotifier.createDummy());
  // String code = "(( ( n + -x + -y ) )<=0) & (( ( x + y + -n ) )<=0)";
  //
  // this.parserTools =
  // ParserTools
  // .create(ExpressionTrees.newFactory(), super.cfa.getMachineModel(), super.logger);
  // Optional<String> explicitInvariantScope = Optional.empty();
  // Scope candidateScope =
  // new CProgramScope(super.cfa, super.logger).withFunctionScope(pFunctionName);
  //
  // Optional<String> explicitAssumptionResultFunction =
  // getFunction(
  // pGraphMLParserState,
  // thread,
  // pTransition.getExplicitAssumptionResultFunction());
  // Optional<String> resultFunction =
  // determineResultFunction(explicitAssumptionResultFunction, scope);
  // ExpressionTree<AExpression> invariant =
  // CParserUtils.parseStatementsAsExpressionTree(
  // pTransition.getTarget().getInvariants(),
  // resultFunction,
  // pCParser,
  // candidateScope,
  // parserTools);
  //
  // String fileName = "";
  // ParseResult result = parser.parseString(fileName, code);
  // FileLocation mainLoc = result.getFunctions().get("main").getFileLocation();
  //
  // // expr = cParser.parseSingleStatement(pInv, scope);
  //
  // // aus dem CAST eine CExpresion bauen
  // CExpression assumption = null;
  //
  // } catch (CParserException | InterruptedException e) {
  // // TODO Auto-generated catch block
  // e.printStackTrace();
  //
  // }
  // }

  /**
   *
   * Computes for each source code line the edges associated to that line
   *
   * @param pCfa the cfa to search in
   * @param lineNumberOfMain the line number of the main function
   * @param lineToEdgesOfMain the map to add elements to
   * @param pNameOfFunction the name of the function to considere
   * @return the extended map
   */
  private int getMappingLinesToEdgesOfFunction(
      CFA pCfa,
      int lineNumberOfMain,
      Map<Integer, Set<CFAEdge>> lineToEdgesOfMain,
      String pNameOfFunction) {
    // if (!pNameOfFunction.equals(MAIN_FUNCTION)) {
    // throw new IllegalStateException("Not implemented now! Only main methods are supported");
    // }
    for (CFANode n : pCfa.getAllNodes()) {
      if (n.getFunctionName().equals(pNameOfFunction)) {
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
    }
    if (pCfa.getMainFunction().getNumLeavingEdges() > 1) {
      throw new IllegalStateException("Expecting only one call t main");
    } else {
      lineNumberOfMain = pCfa.getMainFunction().getLeavingEdge(0).getLineNumber();
    }

    // Cleanup due to performance reasons
    cleanup(lineToEdgesOfMain);

    return lineNumberOfMain;
  }

  // private void computeAllEdgesForLineNumber(
  // CFA pCfa,
  // Map<Integer, Set<CFAEdge>> lineToEdgesOfMain,
  // AssumeEdge pEdge,
  // int lineNumber,
  // Set<Pair<CFAEdge, Element>> pNodesWithOutInvToAdd,
  // Map<CFANode, Element> pNodesInvGeneratedFor) {
  // for (CFAEdge e : lineToEdgesOfMain.get(lineNumber)) {
  // // Set<FileLocation> fileLocs =
  // // AutomatonGraphmlCommon.getFileLocationsFromCfaEdge(e, pCfa.getMainFunction());
  // // if (fileLocs.isEmpty()) {
  // // if (e.getFileLocation() != null && e instanceof BlankEdge) {
  // // // Determine the predrecesor locations (only if unique and add an edge in the witness for
  // // // that location
  // // // (Since the location is a blank one and hence associated to the previous spot
  // // Optional<Element> invElement = Optional.empty();
  // // for (int i = 0; i < e.getPredecessor().getNumEnteringEdges(); i++) {
  // // int prevLine = e.getPredecessor().getEnteringEdge(i).getLineNumber();
  // // if (prevLine > 0) {
  // // invElement =
  // // computeOneEdgeForLineNumber(
  // // pCfa,
  // // lineToEdgesOfMain,
  // // inv,
  // // prevLine,
  // // e.getSuccessor().isLoopStart(),
  // // invElement);
  // // // FIXME:we could check if the location is used once to avoid duplicates
  // // if (invElement.isPresent()) {
  // // pNodesInvGeneratedFor.put(e.getSuccessor(), invElement.get());
  // // // Finally, add the successors of the added note to a list to add them later to the
  // // // witness
  // // // (as empty nodes)
  // // pNodesWithOutInvToAdd.add(Pair.of(e, invElement.get()));
  // // }
  // // }
  // // }
  // //
  // // }
  // // } else {
  //
  // // for (FileLocation loc : fileLocs) {
  // // // TODO: Add handling for edges with different starting and finishing line
  // // minStartOffset = Math.min(minStartOffset, loc.getNodeOffset());
  // // maxEndOffset = Math.max(maxEndOffset, loc.getNodeOffset() + loc.getNodeLength());
  // // }
  //
  //
  //
  //
  // // Check if a controledge (assume edge) is present
  // if (e instanceof AssumeEdge) {
  // isControlEdge = Optional.of(((AssumeEdge) e).getTruthAssumption());
  // }
  //
  // // Check if the flag "enterLoopHead" is true, meaning that the edge is one into a loop
  // // head
  // // Create a edge in the witness from mainEntryElement to the invElement node
  // Element edge =
  // getEdge(
  // doc,
  // mainEntryElement,
  // invElement,
  // e.getSuccessor().isLoopStart(),
  // lineNumber,
  // lineNumber,
  // minStartOffset,
  // maxEndOffset,
  // isControlEdge);
  // graph.appendChild(edge);
  //
  // // Finally, add the successors of the added note to a list to add them later to the witness
  // // (as empty nodes)
  // pNodesWithOutInvToAdd.add(Pair.of(e, invElement));
  // }
  // }

  private void cleanup(Map<Integer, Set<CFAEdge>> pLineToEdgesOfMain) {
    // IF any location has an edge, that is an loop enter head, remove the other locations
    for (Entry<Integer, Set<CFAEdge>> entry : pLineToEdgesOfMain.entrySet()) {
      List<CFAEdge> loopHeads =
          entry.getValue()
              .parallelStream()
              .filter(edge -> edge instanceof BlankEdge && edge.getSuccessor().isLoopStart())
              .collect(Collectors.toList());
      if (loopHeads.size() > 0) {
        pLineToEdgesOfMain.replace(entry.getKey(), Sets.newHashSet(loopHeads.get(0)));
      }
    }

  }

}
