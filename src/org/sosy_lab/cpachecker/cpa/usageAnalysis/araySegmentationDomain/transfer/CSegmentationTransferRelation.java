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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.transfer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
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
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
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
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ErrorSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ExtendedCompletLatticeAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.UnreachableSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.formula.FormulaState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.util.EnhancedCExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

public class CSegmentationTransferRelation<T extends ExtendedCompletLatticeAbstractState<T>> extends
    ForwardingTransferRelation<ArraySegmentationState<T>, ArraySegmentationState<T>, Precision> {

  private final LogManagerWithoutDuplicates logger;
  private final MachineModel machineModel;
  public final String PREFIX;
  private ExpressionSimplificationVisitor visitor;

  TransferRelation transferRelationForInnerDomain;
  CStatementTrasformer<T> statementTransformer;
  CUpdateTransformer<T> updateTransformer;

  /**
   *
   * @param transferRelationForInnerDomain needs to return a single element!
   * @param pLogger
   * @param pMachineModel
   * @param typeOfAnalysis
   */
  public CSegmentationTransferRelation(
      TransferRelation transferRelationForInnerDomain,
      LogManagerWithoutDuplicates pLogger,
      MachineModel pMachineModel,
      String typeOfAnalysis) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
    visitor = new EnhancedCExpressionSimplificationVisitor(machineModel, logger);
    PREFIX = typeOfAnalysis + "_ANALYSIS:";

    this.transferRelationForInnerDomain = transferRelationForInnerDomain;
    statementTransformer = new CStatementTrasformer<>(logger, visitor);
    updateTransformer = new CUpdateTransformer<>();
  }

  @SuppressWarnings("unchecked")
  @Override
  protected ArraySegmentationState<T>
      handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
          throws CPATransferException {
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());

    // Check if a variable is assigned
    if (pDecl instanceof CVariableDeclaration
        && ((CVariableDeclaration) pDecl).getInitializer() instanceof CInitializerExpression) {
      CVariableDeclaration varDecl = (CVariableDeclaration) pDecl;
      // Now ensure that the variable needs to be checked (is a array variable
      return logTransformation(
          inputArgumentsAsString,
          statementTransformer.reassign(
              new CIdExpression(pDecl.getFileLocation(), pDecl),
              ((CInitializerExpression) varDecl.getInitializer()).getExpression(),
              resState));
    }
    return logTransformation(inputArgumentsAsString, state != null ? state.clone() : state);
  }

  @Override
  protected @Nullable ArraySegmentationState<T>
      handleAssumption(CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
          throws CPATransferException {
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());

    // Case 3: Update(e,d)
    if (pExpression instanceof CBinaryExpression) {
      return logTransformation(
          inputArgumentsAsString,
          updateTransformer.update(
              (CBinaryExpression) pExpression,
              pTruthAssumption,
              resState,
              logger,
              visitor));
    } else {
      return logTransformation(inputArgumentsAsString, state.clone());
    }
  }

  @Override
  protected ArraySegmentationState<T> handleBlankEdge(BlankEdge pCfaEdge) {
    // TODO: Verify that this is the correct behavior
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    try {
      ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());
      return logTransformation(inputArgumentsAsString, resState);
    } catch (CPATransferException e) {
      // TODO: enhance error handling
      throw new IllegalArgumentException(e);
    }

  }

  @Override
  protected ArraySegmentationState<T> handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {// TODO: Verify that this is the correct behavior
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());
    return logTransformation(inputArgumentsAsString, resState);
  }

  @Override
  protected ArraySegmentationState<T> handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());
    return logTransformation(inputArgumentsAsString, resState);
  }

  @Override
  protected ArraySegmentationState<T> handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge)
      throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());
    return logTransformation(inputArgumentsAsString, resState);
  }

  @Override
  protected ArraySegmentationState<T> handleReturnStatementEdge(CReturnStatementEdge pCfaEdge)
      throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());
    return logTransformation(inputArgumentsAsString, resState);
  }

  @Override
  protected ArraySegmentationState<T>
      handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
          throws CPATransferException {
    String inputArgumentsAsString = computeInnputString(pCfaEdge);
    if (super.state == null) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return logTransformation(inputArgumentsAsString, state);
    }
    // Apply the inner transfer function
    ArraySegmentationState<T> resState = applyInnerTransferRelation(pCfaEdge, state.clone());
    state = statementTransformer.transform(resState, pStatement);
    return logTransformation(inputArgumentsAsString, state);

  }

  /**
   * If parameter pOTherStates contains an FormulaState, the segmentation may be updated
   */
  @Override
  public Collection<ArraySegmentationState<T>> strengthen(
      AbstractState pState,
      Iterable<AbstractState> pOtherStates,
      @Nullable CFAEdge pCfaEdge,
      Precision pPrecision)
      throws CPATransferException, InterruptedException {
    if (pState instanceof ArraySegmentationState) {
      @SuppressWarnings("unchecked")
      ArraySegmentationState<T> s = (ArraySegmentationState<T>) pState;
      if (isCornerCase(s)) {
        return Collections.emptyList();
      }

      // Try to extract information for the array segmentations:
      // 1. get all variables present in the segmentation
      FormulaState formulaState = null;
      for (AbstractState a : pOtherStates) {
        if (a instanceof FormulaState) {
          formulaState = (FormulaState) a;
        }
      }
      if (formulaState != null) {
        CSegmentationStrengthener<T> strengthener =
            new CSegmentationStrengthener<>(machineModel, logger, updateTransformer);
        // FIXME: Just for test
        if (pCfaEdge.getLineNumber() == 13) {
          System.out.println();
        }

        s = strengthener.strengthen(s, formulaState, formulaState.getPathFormula(), pCfaEdge);
        return Collections.singleton(s);
      }

    }

    // TODO Auto-generated method stub
    return Collections.emptyList();
  }

  public boolean isCornerCase(ArraySegmentationState<T> s) {
    return s instanceof ErrorSegmentation || s instanceof UnreachableSegmentation;
  }

  private ArraySegmentationState<T> applyInnerTransferRelation(
      CFAEdge pCfaEdge,
      ArraySegmentationState<T> pArraySegmentationState)
      throws CPATransferException {

    List<? extends AbstractState> res;
    try {
      res =
          new ArrayList<AbstractState>(
              transferRelationForInnerDomain
                  .getAbstractSuccessorsForEdge(pArraySegmentationState, precision, pCfaEdge));
    } catch (InterruptedException e) {
      throw new CPATransferException("Could not apply inner transfer function", e);
    }
    if (res.size() != 1) {
      throw new CPATransferException(
          "The inner transfer function does not lead to a single result. Results are "
              + res.toString());
    } else if (!(res.get(0) instanceof ArraySegmentationState)) {
      throw new CPATransferException(
          "The inner transfer function does not return an ArraySegmentationState. Instead, the following state is returned:"
              + res.get(0).toString()
              + " that is a "
              + res.get(0).getClass());
    } else if (!this.state.gettEmptyElement()
        .getClass()
        .equals(((ArraySegmentationState) res.get(0)).gettEmptyElement().getClass())) {
      throw new CPATransferException(
          "The inner transfer function does not return an ArraySegmentationState paramterized with T. Requiered class:"
              + this.getState().gettEmptyElement().getClass().toString()
              + " Returned:"
              + ((ArraySegmentationState) res.get(0)).gettEmptyElement().getClass());
    }
    @SuppressWarnings("unchecked")
    ArraySegmentationState<T> resState = (ArraySegmentationState<T>) res.get(0);
    return resState;
  }

  private ArraySegmentationState<T>
      logTransformation(String inputToTransfer, @Nullable ArraySegmentationState<T> pState) {
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
