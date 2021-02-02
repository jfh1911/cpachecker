// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.valueExport;

import com.google.common.base.Charsets;
import com.google.common.collect.Sets;
import java.io.File;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.ADeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.AParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.ADeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.AReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.AStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.AssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.Type;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.defaults.SingletonPrecision;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisInformation;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

public class ValueAnalysisExportTransferRelation
    extends ForwardingTransferRelation<
        ValueAnalysisExportState, ValueAnalysisExportState, SingletonPrecision> {

  private static final String VERIFIER_NONDET = "__VERIFIER_nondet_";
  private static final String VERIFIER_ASSERT = "__VERIFIER_assert";

  private String variableValuesCsvFilePath = null;
  private AtomicInteger id_counter;
  private boolean storeVariableValues = false;

  private final LogManagerWithoutDuplicates logger;
  private CFA cfa;

  private Map<String, ExportStateStorage> exportStates;
  private String defaultValueForUndefined;
  private Map<Integer, Set<String>> varsAssignedInLoop;
  private boolean exportAfter50Iterations;
  private int counter = 0;

  public ValueAnalysisExportTransferRelation(
      LogManager pLogger,
      String variableValuesCsvFile,
      boolean storeVariableValues,
      CFA pCfa,
      int pFirstID,
      String defaultValueForUndefined,
      boolean pExportAfter50Iterations) {

    logger = new LogManagerWithoutDuplicates(pLogger);
    this.variableValuesCsvFilePath = variableValuesCsvFile;
    this.storeVariableValues = storeVariableValues;
    this.cfa = pCfa;
    this.id_counter = new AtomicInteger(pFirstID);
    exportStates = new HashMap<>();
    this.defaultValueForUndefined = defaultValueForUndefined;
    // Compute a coarse approximation of variables changed within the loop
    this.varsAssignedInLoop = computeVarsAssingeedInLoop();
    this.exportAfter50Iterations = pExportAfter50Iterations;
  }



  @Override
  protected ValueAnalysisExportState handleFunctionCallEdge(
      FunctionCallEdge callEdge,
      List<? extends AExpression> arguments,
      List<? extends AParameterDeclaration> parameters,
      String calledFunctionName)
      throws UnrecognizedCodeException {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleBlankEdge(BlankEdge cfaEdge) {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleReturnStatementEdge(AReturnStatementEdge returnEdge)
      throws UnrecognizedCodeException {

    return state;
  }

  /**
   * Handles return from one function to another function.
   *
   * @param functionReturnEdge return edge from a function to its call site
   * @return new abstract state
   */
  @Override
  protected ValueAnalysisExportState handleFunctionReturnEdge(
      FunctionReturnEdge functionReturnEdge,
      FunctionSummaryEdge summaryEdge,
      AFunctionCall exprOnSummary,
      String callerFunctionName)
      throws UnrecognizedCodeException {

    return state;
  }

  @Override
  protected ValueAnalysisExportState handleFunctionSummaryEdge(CFunctionSummaryEdge cfaEdge)
      throws CPATransferException {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleAssumption(
      AssumeEdge cfaEdge, AExpression expression, boolean truthValue)
      throws UnrecognizedCodeException {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleDeclarationEdge(
      ADeclarationEdge declarationEdge, ADeclaration declaration) throws UnrecognizedCodeException {

    return state;
  }

  @Override
  protected ValueAnalysisExportState handleStatementEdge(
      AStatementEdge cfaEdge, AStatement expression) throws UnrecognizedCodeException {

    return state;
  }

  @Override
  public Collection<? extends AbstractState> strengthen(
      AbstractState pElement,
      Iterable<AbstractState> pElements,
      CFAEdge pCfaEdge,
      Precision pPrecision)
      throws CPATransferException {
    assert pElement instanceof ValueAnalysisExportState;

    // Do post processing
    final Collection<AbstractState> postProcessedResult = new ArrayList<>(1);
    postProcessedResult.add(pElement);

    if (storeVariableValues) {
      //      List<String> lines = new ArrayList<>();
      //      StringBuilder builder = new StringBuilder();
      if (pCfaEdge != null && pCfaEdge.getPredecessor() != null) {

        // Now, we can do something
        CFANode node = pCfaEdge.getPredecessor();
        if (pCfaEdge.getPredecessor() instanceof CFunctionEntryNode) {
          // We are entering a new function, hence create a new ExportState for the function
          exportStates.put(node.getFunctionName(), new ExportStateStorage(node.getFunctionName(), defaultValueForUndefined));
        }
        if (pCfaEdge.getPredecessor() instanceof FunctionExitNode
            || (pCfaEdge.getSuccessor() != null
                && pCfaEdge.getSuccessor() instanceof FunctionExitNode
                && cfa.getMainFunction()
                    .getFunctionName()
                    .equals(pCfaEdge.getSuccessor().getFunctionName()))) {
          // We are exiting a function, hence store all states computed for this function
          storeStates(exportStates.get(node.getFunctionName()), node.getFunctionName());

        }
        for (AbstractState other : pElements) {
          if (other instanceof ValueAnalysisState
              && pCfaEdge.getPredecessor().isLoopStart()
              && !postProcessedResult.isEmpty()) {

            // We are at a loop head

            ValueAnalysisInformation info = ((ValueAnalysisState) other).getInformation();
            ExportStateStorage currentState = exportStates.get(node.getFunctionName());
            currentState.addNewState(info, pCfaEdge.getLineNumber());
            counter += 1;
            if (this.exportAfter50Iterations && counter % 50 == 0) {
              storeStates(exportStates.get(node.getFunctionName()), node.getFunctionName());
            }
          }
        }
      }
    }
    return postProcessedResult;
  }

  private void storeStates(ExportStateStorage pExportStateStorage, String pFunctionName) {
    if (!pExportStateStorage.isEmpty()) {
      Path currentFile =
          new File(variableValuesCsvFilePath + "§" + pFunctionName + ".csv").toPath();
      try {
        // Clean the file
        FileChannel.open(currentFile, StandardOpenOption.WRITE).truncate(0).close();
      } catch (IOException e) {
        // Nothing to do here, assuming that the file does not exists
      }

      try {
        // get Header
        List<String> information =
            printVariableInformations(
                pExportStateStorage.getLocationsUsedInMethod(), pFunctionName);
        information.add("");
        // Get the body
        information.addAll(pExportStateStorage.printBody(id_counter, this.varsAssignedInLoop));

        // Write the information to the file
        Files.write(currentFile, information, Charsets.UTF_8);
      } catch (IOException e) {
        logger.log(Level.WARNING, "Could not create csv file, as the file does not exists");
      }
    }
  }

  private List<String> printVariableInformations(
      List<Pair<MemoryLocation, Type>> pList, String pFunctionName) {
    List<String> lines = new ArrayList<>();
    StringBuilder information = new StringBuilder();
    information = information.append("## Varname, type, isUnsinged, isConstant, isRandomValue");
    lines.add(information.toString());
    information = new StringBuilder();
    Set<CFAEdge> edges = new HashSet<>();
    for (CFANode n : cfa.getAllNodes()) {
      if (n.getFunctionName().equals(pFunctionName)) {
        for (int i = 0; i < n.getNumEnteringEdges(); i++) {
          edges.add(n.getEnteringEdge(i));
        }
      }
    }
    Set<String> varsWithUnchangedValue = computeUnchagnedVars(edges);

    Set<String> varsWithRandomValueAssignedTo = new HashSet<>();

    for (CFAEdge e : edges) {
      if (e instanceof CStatementEdge) {
        CStatement statement = ((CStatementEdge) e).getStatement();
        if (statement instanceof CFunctionCallAssignmentStatement) {
          CFunctionCallAssignmentStatement statement2 =
              (CFunctionCallAssignmentStatement) statement;
          if (statement2.getRightHandSide().toString().startsWith(VERIFIER_NONDET)) {
            varsWithRandomValueAssignedTo.add(statement2.getLeftHandSide().toASTString());
          }
        }
      }
    }

    for (Pair<MemoryLocation, Type> entry : pList) {

      information =
          information.append(
              "|" + entry.getFirst().getAsSimpleString() + "|" + "," + entry.getSecond() + ",");
      if (entry.getSecond() instanceof CSimpleType) {
        CSimpleType t = (CSimpleType) entry.getSecond();
        boolean isConst =
            t.isConst() || varsWithUnchangedValue.contains(entry.getFirst().getIdentifier());
        information = information.append(t.isUnsigned() + "," + isConst + ",");
      } else {
        information = information.append("?,?,");
      }

      information =
          information.append(
              varsWithRandomValueAssignedTo.contains(entry.getFirst().getIdentifier()));
      lines.add(information.toString());
      information = new StringBuilder();
    }
    return lines;
  }

  private Set<String> computeUnchagnedVars(Set<CFAEdge> pEdges) {
    Set<String> nonConstVars = new HashSet<>();
    Set<String> allVars = new HashSet<>();
    for (CFAEdge e : pEdges) {
      if (e instanceof CDeclarationEdge) {
        CDeclarationEdge ce = (CDeclarationEdge) e;
        if (ce.getDeclaration() instanceof CVariableDeclaration) {
          allVars.add(((CVariableDeclaration) ce.getDeclaration()).getName());
        }
      } else if (e instanceof CStatementEdge) {
        CStatementEdge stmt = (CStatementEdge) e;
        if (e instanceof CFunctionSummaryStatementEdge) {
          CFunctionCall call = ((CFunctionSummaryStatementEdge) e).getFunctionCall();
          CFunctionCallExpression expr = call.getFunctionCallExpression();
          if (expr.getDeclaration().getName().equals(VERIFIER_ASSERT)) {
            List<CExpression> params =
                ((CFunctionSummaryStatementEdge) e)
                    .getFunctionCall()
                    .getFunctionCallExpression()
                    .getParameterExpressions();

            for (CExpression param : params) {
              nonConstVars.addAll(stripExpression(param));
            }

          }
        }
        if (stmt.getStatement() instanceof CAssignment) {

          CAssignment assign = (CAssignment) stmt.getStatement();
          if (assign.getLeftHandSide() instanceof CIdExpression) {
            nonConstVars.add(((CIdExpression) assign.getLeftHandSide()).getName());
          }
        }
      }
    }
    // Constant = allVars - nonConstantVars
    return Sets.difference(allVars, nonConstVars);
  }

  private Set<String> stripExpression(CExpression pParam) {
    Set<String> varsPresent = new HashSet<>();
    if (pParam instanceof CBinaryExpression) {
      CBinaryExpression binary = (CBinaryExpression) pParam;
      varsPresent.addAll(stripExpression(binary.getOperand1()));
      varsPresent.addAll(stripExpression(binary.getOperand2()));
    } else if (pParam instanceof CIdExpression) {
      return Sets.newHashSet(((CIdExpression) pParam).getName());
    }
    return varsPresent;
  }

  private Map<Integer, Set<String>> computeVarsAssingeedInLoop() {
    Map<Integer, Set<String>> mapping = new HashMap<>();

    if (this.cfa.getLoopStructure().isPresent()) {
      LoopStructure loopStrcutre = cfa.getLoopStructure().get();
      for (Loop loop : loopStrcutre.getAllLoops()) {
        Set<String> modifiedVars = new HashSet<>();

        for (CFANode looped : loop.getLoopNodes()) {
          for (int i = 0; i < looped.getNumLeavingEdges(); i++) {
            CFAEdge e = looped.getLeavingEdge(i);
            if (e instanceof CStatementEdge) {
              CStatementEdge stmt = (CStatementEdge) e;
              if (e instanceof CFunctionSummaryStatementEdge) {
                CFunctionCall call = ((CFunctionSummaryStatementEdge) e).getFunctionCall();
                CFunctionCallExpression expr = call.getFunctionCallExpression();
                if (expr.getDeclaration().getName().equals(VERIFIER_ASSERT)) {
                  List<CExpression> params =
                      ((CFunctionSummaryStatementEdge) e)
                          .getFunctionCall()
                          .getFunctionCallExpression()
                          .getParameterExpressions();
                  for (CExpression param : params) {
                    modifiedVars.addAll(stripExpression(param));
                  }
                }
              }
              if (stmt.getStatement() instanceof CAssignment) {

                CAssignment assign = (CAssignment) stmt.getStatement();
                if (assign.getLeftHandSide() instanceof CIdExpression) {
                  CIdExpression temp = (CIdExpression) assign.getLeftHandSide();
                  modifiedVars.add(temp.toQualifiedASTString().replace("__", "::"));
                }
              }
            }
          }
        }
        for (CFANode loopHead : loop.getLoopHeads()) {
          int linenumber = loopHead.getLeavingEdge(0).getLineNumber();
          if (mapping.containsKey(linenumber)) {
            Set<String> tempList = mapping.get(linenumber);
            tempList.addAll(modifiedVars);
            mapping.put(linenumber, tempList);
          } else {
            mapping.put(linenumber, modifiedVars);
          }
        }
      }
    }
    return mapping;
  }
}
