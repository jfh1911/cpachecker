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

import java.math.BigInteger;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.c.CAddressOfLabelExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CCastExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CTypeIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageState;

public class SegmentationReachabilityChecker {

  /**
   * Checks, if the given segmentation is reachable w.r.t. Definition 4.10 given by Jan Haltermann
   * in his Masther thesis. Currently, only the case 1-4 are implement, neither case 5 nor
   * transitive dependecies are checked.
   *
   * @param pSegmentation the segmentation
   * @param pVar the variable on the LHS of the expression
   * @param pOp2 he RHS of the expression
   * @param pOperator the operator of the expression
   * @param pLogger used for loggign
   * @param pVisitor statement simplifaction visitor to compute cannonical form
   * @return true, if the segmentation is reachable, false otherwise
   */
  public static @Nullable ArraySegmentationState<VariableUsageState> checkReachability(
      ArraySegmentationState<VariableUsageState> pSegmentation,
      CIdExpression pVar,
      CExpression pOp2,
      BinaryOperator pOperator,
      LogManager pLogger,
      ExpressionSimplificationVisitor pVisitor) {

    int segOfVar = pSegmentation.getSegBoundContainingExpr(pVar);
    int segOfExpr = pSegmentation.getSegBoundContainingExpr(pOp2);
    List<ArraySegment<VariableUsageState>> segments = pSegmentation.getSegments();
    // Case 1: If e = (i = c), i and c are present in different segment bounds and there is a
    // segment {e j }d j {e k } between the segment bounds containing i and c that is not marked
    // with ’?’,
    if (segOfExpr != -1
        && segOfVar != -1
        && segOfExpr != segOfVar
        && pOperator.equals(BinaryOperator.EQUALS)) {
      int min = Integer.min(segOfExpr, segOfVar);
      int max = Integer.max(segOfExpr, segOfVar);
      for (int i = min; i < max; i++) {
        if (!segments.get(i).isPotentiallyEmpty()) {
          return new UnreachableArraySegmentation<>();
        }
      }
    }

    // Case 2: if e = (i = c) and there is a second expression e 0 , such that i and e 0 are present
    // in one segment bound, but c != e 0 holds
    // Check if the RHS evaluates to a integer value
    CExpression valueOfpOp2 = getValueOrNull(pOp2, pVisitor);
    if (valueOfpOp2 != null && valueOfpOp2 instanceof CIntegerLiteralExpression) {
      BigInteger v = ((CIntegerLiteralExpression) valueOfpOp2).getValue();
      if (segOfVar != -1) {
        ArraySegment<VariableUsageState> segment = segments.get(segOfVar);
        if (segment.getSegmentBound()
            .parallelStream()
            .anyMatch(
                s -> s instanceof CIntegerLiteralExpression
                    && !((CIntegerLiteralExpression) s).getValue().equals(v))) {
          return new UnreachableArraySegmentation<>();
        }
      }
    }

    // Case 3: e = (i != c) and there is a segment bound containing the expressions c and i.
    if (segOfExpr == segOfVar && pOperator.equals(BinaryOperator.NOT_EQUALS)) {
      return new UnreachableArraySegmentation<>();
    }

    // Case 4: The ordering of segment bounds implies that i ≤ c, but e = (i > c) or vice versa
    if (pOperator.equals(BinaryOperator.GREATER_THAN) && segOfVar < segOfExpr
        || pOperator.equals(BinaryOperator.LESS_THAN) && segOfVar > segOfExpr) {
      return new UnreachableArraySegmentation<>();
    }

    // TODO: implement Case 5: Between two segment bounds e 1 ,e 2 with | e 1 −e 2 |= n are more
    // than n-1 segment bounds not marked with ’?’ and thus more than n segments present.
    // if (segOfExpr != -1
    // && segOfVar != -1
    // && segOfExpr != segOfVar) {
    // int min = Integer.min(segOfExpr, segOfVar);
    // int max = Integer.max(segOfExpr, segOfVar);
    // //Check if there are more elements marked as "not potentially empty = defentlyEmpty"
    // if (segments.subList(min, max+1).parallelStream().filter(s ->
    // !s.isPotentiallyEmpty()).count() > ) {
    //
    // }
    // }
    return pSegmentation;

  }

  private static CExpression
      getValueOrNull(CExpression pExpr, ExpressionSimplificationVisitor visitor) {
    CExpression returnExpr = null;
    if (pExpr instanceof CAddressOfLabelExpression) {
      returnExpr = visitor.visit((CAddressOfLabelExpression) pExpr);
    } else if (pExpr instanceof CBinaryExpression) {
      returnExpr = visitor.visit((CBinaryExpression) pExpr);
    } else if (pExpr instanceof CCastExpression) {
      returnExpr = visitor.visit((CCastExpression) pExpr);
    } else if (pExpr instanceof CTypeIdExpression) {
      returnExpr = visitor.visit((CTypeIdExpression) pExpr);
    } else if (pExpr instanceof CUnaryExpression) {
      returnExpr = visitor.visit((CUnaryExpression) pExpr);
    }
    return returnExpr;
  }

}
