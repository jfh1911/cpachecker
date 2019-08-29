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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.transformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageType;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ErrorSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UsageAnalysisTransferRelation;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;

public class UsageTransformer {

  private MachineModel machineModel;
  private LogManager logger;
  private ExpressionSimplificationVisitor visitor;

  public UsageTransformer(
      MachineModel pMachineModel,
      LogManager pLogger,
      ExpressionSimplificationVisitor pVisitor) {
    super();
    machineModel = pMachineModel;
    logger = pLogger;
    visitor = pVisitor;
  }

  public @Nullable ArraySegmentationState<VariableUsageState>
      use(CStatement pStatement, ArraySegmentationState<VariableUsageState> state) {
    List<CArraySubscriptExpression> arrayUses = getUses(pStatement);
    return explUse(arrayUses, state);
  }

  public @Nullable ArraySegmentationState<VariableUsageState>
      explUse(
          List<CArraySubscriptExpression> pArrayUses,
          ArraySegmentationState<VariableUsageState> state) {
    CBinaryExpressionBuilder builder = new CBinaryExpressionBuilder(machineModel, logger);
    for (CArraySubscriptExpression use : pArrayUses) {
      // Check, if the expression used to access the array element is present in the current state
      CExpression subscriptExpr = use.getSubscriptExpression();
      int pos = state.getSegBoundContainingExpr(subscriptExpr);
      if (pos < 0) {
        logger.log(
            Level.FINE,
            UsageAnalysisTransferRelation.PREFIX
                + "Cannot create a usage sincethe variable "
                + subscriptExpr.toASTString()
                + " is not present in the segmentation, hence the error symbol is returned. Current State is: "
                + state.toDOTLabel()
                + " for the expression :"
                + pArrayUses.toString());
        return new ErrorSegmentation<>();
      } else {
        // Create a new segment after the segment containing the expression to access the array
        // elements and mark this as used
        ArraySegment<VariableUsageState> leftBound = state.getSegments().get(pos);
        CExpression exprPlus1;
        try {
          exprPlus1 =
              visitor.visit(
                  builder.buildBinaryExpression(
                      subscriptExpr,
                      CIntegerLiteralExpression.ONE,
                      CBinaryExpression.BinaryOperator.PLUS));
        } catch (UnrecognizedCodeException e) {
          e.printStackTrace();
          logger.log(
              Level.FINE,
              UsageAnalysisTransferRelation.PREFIX
                  + "Cannot create a usage due to internal problems, hence the error symbol is returned. Current State is: "
                  + state.toDOTLabel()
                  + " for the expression :"
                  + pArrayUses.toString());
          return new ErrorSegmentation<>();
        }
        if (!leftBound.getNextSegment().getSegmentBound().contains(exprPlus1)) {
          // Add the segment bound
          List<AExpression> bounds = new ArrayList<>();
          bounds.add(exprPlus1);
          ArraySegment<VariableUsageState> newSeg =
              new ArraySegment<>(bounds, leftBound.getAnalysisInformation(), true, null);
          state.addSegment(newSeg, leftBound);
        }
        leftBound.setAnalysisInformation(new VariableUsageState(VariableUsageType.USED));
        leftBound.setPotentiallyEmpty(false);
      }

    }
    return state;
  }

  public List<CArraySubscriptExpression> getUses(CStatement pStatement) {
    List<CArraySubscriptExpression> uses = new ArrayList<>();
    if (pStatement instanceof CAssignment) {
      uses.addAll(getUses(((CAssignment) pStatement).getLeftHandSide()));
      uses.addAll(getUses(((CAssignment) pStatement).getRightHandSide()));
    } else if (pStatement instanceof CFunctionCall) {
      uses.addAll(getUses(((CFunctionCall) pStatement).getFunctionCallExpression()));
    }
    return uses;
  }

  public Collection<CArraySubscriptExpression> getUses(CRightHandSide pExpr) {
    List<CArraySubscriptExpression> uses = new ArrayList<>();
    if (pExpr instanceof CFunctionCallExpression) {
      ((CFunctionCallExpression) pExpr).getParameterExpressions()
          .parallelStream()
          .forEach(p -> uses.addAll(getUses(p)));
    } else if (pExpr instanceof CBinaryExpression) {
      uses.addAll(getUses(((CBinaryExpression) pExpr).getOperand1()));
      uses.addAll(getUses(((CBinaryExpression) pExpr).getOperand2()));
    } else if (pExpr instanceof CArraySubscriptExpression) {
      uses.add((CArraySubscriptExpression) pExpr);
    }
    return uses;
  }

}
