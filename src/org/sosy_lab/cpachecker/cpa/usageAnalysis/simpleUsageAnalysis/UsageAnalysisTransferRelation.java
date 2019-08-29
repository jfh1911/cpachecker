/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializerExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.transformer.StatementTrasformer;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.transformer.UpdateTransformer;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.transformer.UsageTransformer;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.util.EnhancedExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

public class UsageAnalysisTransferRelation extends
    ForwardingTransferRelation<ArraySegmentationState<VariableUsageState>, ArraySegmentationState<VariableUsageState>, Precision> {

  private final LogManagerWithoutDuplicates logger;
  private final MachineModel machineModel;
  public static final String PREFIX = "USAGE_ANALYSIS:";
  ExpressionSimplificationVisitor visitor;

  UsageTransformer usageTransformer;
  StatementTrasformer statementTransformer;

  public UsageAnalysisTransferRelation(
      LogManagerWithoutDuplicates pLogger,
      MachineModel pMachineModel) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
    visitor = new EnhancedExpressionSimplificationVisitor(machineModel, logger);

    usageTransformer = new UsageTransformer(machineModel, logger, visitor);
    statementTransformer = new StatementTrasformer(logger, visitor, this.usageTransformer);
  }

  @Override
  protected ArraySegmentationState<VariableUsageState>
      handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
          throws CPATransferException {
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }

    // Check if a variable is assigned
    if (pDecl instanceof CVariableDeclaration
        && ((CVariableDeclaration) pDecl).getInitializer() instanceof CInitializerExpression) {
      CVariableDeclaration varDecl = (CVariableDeclaration) pDecl;
      // Now ensure that the variable needs to be checked (is a array variable
      return logTransformation(
          inpUtArgumentsAsString,
          statementTransformer.reassign(
              new CIdExpression(pDecl.getFileLocation(), pDecl),
              ((CInitializerExpression) varDecl.getInitializer()).getExpression(),
              state.clone()));
    }
    return logTransformation(inpUtArgumentsAsString, state != null ? state.clone() : state);
  }

  @Override
  protected @Nullable ArraySegmentationState<VariableUsageState>
      handleAssumption(CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
          throws CPATransferException {
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if any variable is used
    Collection<CArraySubscriptExpression> uses = usageTransformer.getUses(pExpression);
    if (!uses.isEmpty()) {

      state = usageTransformer.explUse(new ArrayList<>(uses), state.clone());
    }

    // Check again, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, super.state);
    }

    // Case 3: Update(e,d)
    if (pExpression instanceof CBinaryExpression) {
      UpdateTransformer u = new UpdateTransformer();
      return logTransformation(
          inpUtArgumentsAsString,
          u.update(
              (CBinaryExpression) pExpression,
              pTruthAssumption,
              state.clone(),
              logger,
              visitor));
    } else {
      return logTransformation(inpUtArgumentsAsString, state);
    }
  }

  @Override
  protected ArraySegmentationState<VariableUsageState>
      handleBlankEdge(BlankEdge pCfaEdge) {
    // TODO: Verify that this is the correct behavior
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    return logTransformation(inpUtArgumentsAsString, state.clone());
  }

  @Override
  protected ArraySegmentationState<VariableUsageState> handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {// TODO: Verify that this is the correct behavior
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    return logTransformation(inpUtArgumentsAsString, state.clone());
  }

  @Override
  protected ArraySegmentationState<VariableUsageState> handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    return logTransformation(inpUtArgumentsAsString, state.clone());
  }

  @Override
  protected ArraySegmentationState<VariableUsageState>
      handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge) throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    return logTransformation(inpUtArgumentsAsString, state.clone());
  }

  @Override
  protected ArraySegmentationState<VariableUsageState>
      handleReturnStatementEdge(CReturnStatementEdge pCfaEdge) throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    return logTransformation(inpUtArgumentsAsString, state.clone());
  }

  @Override
  protected ArraySegmentationState<VariableUsageState>
      handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
          throws CPATransferException {
    String inpUtArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inpUtArgumentsAsString, state);
    }
    StatementTrasformer stmtTransformer =
        new StatementTrasformer(logger, visitor, usageTransformer);
    state = stmtTransformer.transform(state.clone(), pStatement);
    return logTransformation(inpUtArgumentsAsString, state);

  }

  public static boolean isCornerCase(ArraySegmentationState<VariableUsageState> s) {
    return s instanceof ErrorSegmentation || s instanceof UnreachableArraySegmentation;
  }

  private ArraySegmentationState<VariableUsageState> logTransformation(
      String inputToTransfer,
      @Nullable ArraySegmentationState<VariableUsageState> pState) {
    logger.log(Level.FINE, PREFIX + " " + inputToTransfer + ")=" + pState);
    logger.flush();
    // try {
    // Thread.sleep(400);
    // } catch (InterruptedException e) {
    // // TODO Auto-generated catch block
    // e.printStackTrace();
    // }
    return pState;
  }


  private String computeInnputString(AbstractCFAEdge pCfaEdge) {
    return pCfaEdge.getSuccessor().getNodeNumber()
        + " Compute PHI("
        + pCfaEdge.getRawStatement()
        + this.state;
  }

}
