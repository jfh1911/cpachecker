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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.extenedArraySegmentationDomain;

import com.google.common.collect.Lists;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ExtendedCompletLatticeAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.transfer.CUpdateTransformer;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.util.SegmentationReachabilityChecker;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.java_smt.api.SolverException;

public class CExtendedUpdateTransformer<T extends ExtendedCompletLatticeAbstractState<T>>
    extends CUpdateTransformer<T> {

  private CSplitTransformer<T> splitTransformer;

  public CExtendedUpdateTransformer(
      LogManager pLogger,
      ExpressionSimplificationVisitor pVisitor,
      CBinaryExpressionBuilder pBuilder,
      CSplitTransformer<T> pSplitTransformer) {
    super(pLogger, pVisitor, pBuilder, new SegmentationReachabilityChecker(pLogger));
    splitTransformer = pSplitTransformer;
  }

  /**
   * An extended version of the update transformer, making use of splitting
   * 
   * @param pCfaEdge
   *
   * @throws CPATransferException
   * @throws InterruptedException
   * @throws SolverException
   *
   * @throws CPAException if the code cannot be modified
   */

  public @Nullable ExtendedArraySegmentationState<T> updateWithSplit(
      CBinaryExpression expr,
      boolean pTruthAssumption,
      @Nullable ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge)
      throws CPATransferException, SolverException, InterruptedException {

    // Apply the truth assumption. In case of false, invert the operator
    if (!pTruthAssumption) {
      expr =
          new CBinaryExpression(
              expr.getFileLocation(),
              expr.getExpressionType(),
              expr.getCalculationType(),
              expr.getOperand1(),
              expr.getOperand2(),
              expr.getOperator().getOppositLogicalOperator());

    }

    if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.EQUALS)) {
      // Case 3.1
      if (isVarType(expr.getOperand1())) {
        return computeExtension(
            super.updateEquals(expr.getOperand1(), expr.getOperand2(), expr.getOperator(), pState));
      } else if (isVarType(expr.getOperand2())) {
        return computeExtension(
            super.updateEquals(expr.getOperand2(), expr.getOperand1(), expr.getOperator(), pState));
      } else {
        return computeExtension(pState);
      }
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.NOT_EQUALS)) {
      // Case 3.2
      return computeExtension(updateNotEquals(expr.getOperand1(), expr.getOperand2(), pState));
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.GREATER_THAN)) {
      // Check if the split (CAse 4.1 is applicable)
      if (splitIsApplicable(expr.getOperand1(), expr.getOperand2(), pState)) {
        return splitTransformer
            .splitGreaterThan(
                (CIdExpression) expr.getOperand1(),
                expr.getOperand2(),
                pState,
                pCfaEdge);
      }

      // Apply Case 3.3
      return computeExtension(updateGreater(expr.getOperand1(), expr.getOperand2(), pState));
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.LESS_THAN)) {
      if (splitIsApplicable(expr.getOperand1(), expr.getOperand2(), pState)) {
        return splitTransformer
            .splitLessThan(
                (CIdExpression) expr.getOperand1(),
                expr.getOperand2(),
                pState,
                pCfaEdge);
      }
      // Case 3.4
      return computeExtension(updateGreater(expr.getOperand2(), expr.getOperand1(), pState));
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.GREATER_EQUAL)) {
      if (splitIsApplicable(expr.getOperand1(), expr.getOperand2(), pState)) {
        // Return Split(i < E-1,d)
        return splitTransformer.splitGreaterThan(
            (CIdExpression) expr.getOperand1(),
            builder.buildBinaryExpression(
                expr.getOperand2(),
                CIntegerLiteralExpression.ONE,
                BinaryOperator.MINUS),
            pState,
            pCfaEdge);
      }
      // Case 3.5
      return computeExtension(updateGreaterEq(expr.getOperand1(), expr.getOperand2(), pState));
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.LESS_EQUAL)) {
      if (splitIsApplicable(expr.getOperand1(), expr.getOperand2(), pState)) {
        // Return Split(i < E-1,d)
        return splitTransformer.splitLessThan(
            (CIdExpression) expr.getOperand1(),
            builder.buildBinaryExpression(
                expr.getOperand2(),
                CIntegerLiteralExpression.ONE,
                BinaryOperator.PLUS),
            pState,
            pCfaEdge);
      }

      // Case 3.6
      return computeExtension(updateGreaterEq(expr.getOperand2(), expr.getOperand1(), pState));
    } else {
      // TODO: log missing case
      return computeExtension(pState);
    }
  }

  private @Nullable ExtendedArraySegmentationState<T>
      computeExtension(@Nullable ArraySegmentationState<T> pState) {
    return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
  }

  private boolean splitIsApplicable(
      CExpression pOperand1,
      CExpression pOperand2,
      @Nullable ArraySegmentationState<T> pState) {
    // Check, if there is a constant present on the LHS:
    if (isVarType(pOperand1)) {
      List<ArraySegment<T>> segmentsContainingFirst = getSegmentsContainingExpr(pOperand1, pState);
      List<ArraySegment<T>> segmentsContainingSecond = getSegmentsContainingExpr(pOperand2, pState);
      return !segmentsContainingFirst.isEmpty()
          && segmentsContainingSecond.isEmpty()
          && pState.getSegBoundContainingExpr(pOperand1) == pState.getSegments().size() - 2;
    }
    return false;
  }
}
