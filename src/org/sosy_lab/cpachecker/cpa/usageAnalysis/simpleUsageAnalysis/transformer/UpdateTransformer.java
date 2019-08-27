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
import java.util.List;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageDomain;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageType;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ErrorSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.SegmentationReachabilityChecker;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UnreachableArraySegmentation;

public class UpdateTransformer {

  private ArraySegmentationState<VariableUsageDomain> state;
  private LogManager logger;
  private static final String PREFIX = "USAGE_ANALYSIS update";
  ExpressionSimplificationVisitor visitor;

  public UpdateTransformer() {

  }

  public @Nullable ArraySegmentationState<VariableUsageDomain>
      update(
          CBinaryExpression expr,
          @Nullable ArraySegmentationState<VariableUsageDomain> pState,
          LogManagerWithoutDuplicates pLogger,
          ExpressionSimplificationVisitor pVisitor) {
    this.state = pState;
    this.logger = pLogger;
    this.visitor = pVisitor;
    if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.EQUALS)) {// Case 3.1
      // AS explained by Jan Haltermann in hismaster thesis, we need to ensure that the LHS of the
      // equality expression is a variable. IN all other cases, this is not important. Hence, we
      // will check this only, iff the operand is a '='
      // To avoid redundant code, the transformation will firstly ensure that the first parameter is
      // a variable!
      if (isVarType(expr.getOperand1())) {
        return this.updateEquals(expr.getOperand1(), expr.getOperand2(), expr.getOperator());
      } else if (isVarType(expr.getOperand2())) {
        return this.updateEquals(expr.getOperand2(), expr.getOperand1(), expr.getOperator());
      } else {
        return state;
      }
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.NOT_EQUALS)) {// Case 3.2
      return updateNotEquals(expr.getOperand1(), expr.getOperand2());
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.GREATER_THAN)) {// Case
                                                                                          // 3.3
      return updateGreater(expr.getOperand1(), expr.getOperand2());
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.LESS_THAN)) {// Case 3.4
      return updateGreater(expr.getOperand2(), expr.getOperand1());
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.GREATER_EQUAL)) { // Case
                                                                                            // 3.5
      return updateGreaterEq(expr.getOperand1(), expr.getOperand2());
    } else if (expr.getOperator().equals(CBinaryExpression.BinaryOperator.LESS_EQUAL)) {// Case 3.6
      return updateGreaterEq(expr.getOperand2(), expr.getOperand1());
    } else {
      // TODO: log missing case
      return state;
    }
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain>
      updateEquals(CExpression pVar, CExpression pOp2, BinaryOperator pOperator) {
    if (!(pVar instanceof CIdExpression)) {
      // CUrrently, there is no behaviour defined in this case
      return state;
    }
    CIdExpression var = (CIdExpression) pVar;
    List<ArraySegment<VariableUsageDomain>> segmentsContainingOp2 = getSegmentsContainingExpr(pOp2);
    if (segmentsContainingOp2.isEmpty()) {
      // Case 3.1.1 and 3.1.2
      return state;
    } else if (segmentsContainingOp2.size() > 1) {
      // The analysis seems to be not working, since there is more than one segment bound
      // containing an expression. This is an illegal state of the analysis, hence the analysis is
      // aborted by returning the errorSymbol!
      logger.log(
          Level.FINE,
          PREFIX
              + "THe segmentation is invalid, since the expression that should be reassigned is present twice."
              + "Hence, the error symbol is returned. Current State is: "
              + this.state.toDOTLabel()
              + " for the expression :"
              + pVar.toASTString()
              + " := "
              + pOp2.toASTString());
      return new ErrorSegmentation<>();

    } else {
      // Check, if the variable is present in any state:
      List<ArraySegment<VariableUsageDomain>> segmentsContainingVar =
          getSegmentsContainingExpr(var);
      if (segmentsContainingVar.isEmpty()) {
        // Case 3.1.3
        segmentsContainingOp2.get(0).addSegmentBound(var);
        return validate(state, var, pOp2, pOperator);
      } else if (segmentsContainingVar.size() > 1) {
        // The analysis seems to be not working, since there is more than one segment bound
        // containing an expression. This is an illegal state of the analysis, hence the analysis is
        // aborted by returning the errorSymbol!
        logger.log(
            Level.FINE,
            PREFIX
                + "THe segmentation is invalid, since the expression that should be reassigned is present twice."
                + "Hence, the error symbol is returned. Current State is: "
                + this.state.toDOTLabel()
                + " for the expression :"
                + pVar.toASTString()
                + " := "
                + pOp2.toASTString());
        return new ErrorSegmentation<>();
      } else {

        @Nullable
        ArraySegmentationState<VariableUsageDomain> validated =
            this.validate(state, var, pOp2, pOperator);
        if (validated instanceof UnreachableArraySegmentation) {
          return validated;
        } else {
          // Check, if there is usage between the segments containing i and the pOp2
          int posSegmentContainsVar = state.getSegments().indexOf(segmentsContainingVar.get(0));
          int posSegmentContainsOp2 = state.getSegments().indexOf(segmentsContainingOp2.get(0));
          int min = Integer.min(posSegmentContainsVar, posSegmentContainsOp2);
          int max = Integer.max(posSegmentContainsVar, posSegmentContainsOp2);
          for (int i = min; i < max; i++) {
            if (state.getSegments()
                .get(i)
                .getAnalysisInformation()
                .getType()
                .equals(VariableUsageType.USED)) {
              logger.log(
                  Level.FINE,
                  "The analysis result would be under-approximated when removing a segment bound containing array elements marked as used for "
                      + state.toDOTLabel()
                      + " for the expression "
                      + pVar.toASTString()
                      + pOperator.toString()
                      + pOp2.toASTString());
              return new ErrorSegmentation<>();
            }
          }
          // We can safely merge the segment bounds between posSegmentContainsVar and
          // posSegmentContainsOp2, since all elements are marked as unused.
          List<ArraySegment<VariableUsageDomain>> newSegments = new ArrayList<>();
          List<ArraySegment<VariableUsageDomain>> prevSegs = state.getSegments();

          // Add all segemtns before min(posSegmentContainsVar,posSegmentContainsOp2)
          for (int i = 0; i < min; i++) {
            newSegments.add(prevSegs.get(i));
          }
          // Merge the segment information from min to max into max (since max will be kept
          ArraySegment<VariableUsageDomain> keeptSeg = prevSegs.get(max);
          for (int i = min; i < max; i++) {
            keeptSeg.addSegmentBounds(prevSegs.get(i).getSegmentBound());
          }
          // Set the pointer of the last element of newSegs to keeptSeg and add keeptSeg to
          // newSegments
          newSegments.get(min - 1).setNextSegment(keeptSeg);
          newSegments.add(keeptSeg);

          // Add the remaining segments;
          for (int i = max; i < prevSegs.size(); i++) {
            newSegments.add(prevSegs.get(i));
          }
          return new ArraySegmentationState<>(
              newSegments,
              state.gettBottom(),
              state.gettTop(),
              state.gettEmptyElement(),
              state.gettMeet(),
              state.gettLisOfArrayVariables(),
              state.gettArray(),
              logger);
        }
      }
    }
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain>
      updateNotEquals(CExpression op1, CExpression pOp2) {

    if (state.getSegments()
        .parallelStream()
        .anyMatch(s -> s.getSegmentBound().contains(op1) && s.getSegmentBound().contains(pOp2))) {
      return new UnreachableArraySegmentation<>();
    } else {
      // Check if they var and op2 are present in consecutive segments and remove a ? in that case

      List<ArraySegment<VariableUsageDomain>> segmentsContainingOp2 =
          getSegmentsContainingExpr(pOp2);
      if (segmentsContainingOp2.isEmpty()) {
        return state;
      } else if (segmentsContainingOp2.size() > 1) {
        // The analysis seems to be not working, since there is more than one segment bound
        // containing an expression. This is an illegal state of the analysis, hence the analysis is
        // aborted by returning the errorSymbol!
        return new ErrorSegmentation<>();
      } else {
        // Check, if the variable is present in any state:
        List<ArraySegment<VariableUsageDomain>> segmentsContainingOp1 =
            getSegmentsContainingExpr(op1);
        if (segmentsContainingOp1.size() > 1) {
          // The analysis seems to be not working, since there is more than one segment bound
          // containing an expression. This is an illegal state of the analysis, hence the analysis
          // is
          // aborted by returning the errorSymbol!
          logger.log(
              Level.FINE,
              PREFIX
                  + "THe segmentation is invalid, since the expression that should be reassigned is present twice."
                  + "Hence, the error symbol is returned. Current State is: "
                  + this.state.toDOTLabel()
                  + " for the expression :"
                  + op1.toASTString()
                  + " != "
                  + pOp2.toASTString());
          return new ErrorSegmentation<>();
        } else if (segmentsContainingOp1.size() == 1) {
          // Check, if the segment bounds are consecutive:
          int posSegmentContainsOp1 = state.getSegments().indexOf(segmentsContainingOp1.get(0));
          int posSegmentContainsOp2 = state.getSegments().indexOf(segmentsContainingOp2.get(0));
          int min = Integer.min(posSegmentContainsOp1, posSegmentContainsOp2);
          int max = Integer.max(posSegmentContainsOp1, posSegmentContainsOp2);
          if (max - min == 1) {
            state.getSegments().get(min).setPotentiallyEmpty(false);
          }
        }
      }
      return state;
    }
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain>
      updateGreater(CExpression greater, CExpression smaller) {
    List<ArraySegment<VariableUsageDomain>> segmentsContainingGreater =
        getSegmentsContainingExpr(greater);
    List<ArraySegment<VariableUsageDomain>> segmentsContainingSmaller =
        getSegmentsContainingExpr(smaller);
    // CHeck, if both expressions are present in exactly one segment bound
    if (segmentsContainingGreater.isEmpty() || segmentsContainingSmaller.isEmpty()) {
      // Nothing to change
      return state;
    } else if (segmentsContainingGreater.size() > 1 || segmentsContainingSmaller.size() > 1) {
      logger.log(
          Level.FINE,
          PREFIX
              + "THe segmentation is invalid, since the expression that should be reassigned is present twice."
              + "Hence, the error symbol is returned. Current State is: "
              + this.state.toDOTLabel()
              + " for the expression :"
              + greater.toASTString()
              + " > "
              + smaller.toASTString());
      return new ErrorSegmentation<>();
    } else {
      // check if the two segmetns are ordered correctly!
      int posSmaller = state.getSegments().indexOf(segmentsContainingSmaller.get(0));
      int posGreater = state.getSegments().indexOf(segmentsContainingGreater.get(0));
      if (posSmaller >= posGreater) {
        return new UnreachableArraySegmentation<>();
      } else if (posGreater - posSmaller == 1) {
        state.getSegments().get(posSmaller).setPotentiallyEmpty(false);
      }
    }
    return state;
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain>
      updateGreaterEq(CExpression greater, CExpression smaller) {
    List<ArraySegment<VariableUsageDomain>> segmentsContainingGreater =
        getSegmentsContainingExpr(greater);
    List<ArraySegment<VariableUsageDomain>> segmentsContainingSmaller =
        getSegmentsContainingExpr(smaller);
    // CHeck, if both expressions are present in exactly one segment bound
    if (segmentsContainingGreater.isEmpty() || segmentsContainingSmaller.isEmpty()) {
      // Nothing to change
      return state;
    } else if (segmentsContainingGreater.size() > 1 || segmentsContainingSmaller.size() > 1) {
      logger.log(
          Level.FINE,
          PREFIX
              + "THe segmentation is invalid, since the expression that should be reassigned is present twice."
              + "Hence, the error symbol is returned. Current State is: "
              + this.state.toDOTLabel()
              + " for the expression :"
              + greater.toASTString()
              + " >= "
              + smaller.toASTString());
      return new ErrorSegmentation<>();
    } else {
      // check if the two segmetns are ordered correctly!
      int posSmaller = state.getSegments().indexOf(segmentsContainingSmaller.get(0));
      int posGreater = state.getSegments().indexOf(segmentsContainingGreater.get(0));
      if (posSmaller > posGreater) {
        if (isVarType(smaller)) {
          return this.updateEquals(smaller, greater, CBinaryExpression.BinaryOperator.EQUALS);

        } else if (isVarType(greater)) {
          return this.updateEquals(greater, smaller, CBinaryExpression.BinaryOperator.EQUALS);
        } else {
          return state;
        }
      }
    }
    return state;
  }

  private boolean isVarType(CExpression expr) {
    return expr instanceof CIdExpression;
  }

  private List<ArraySegment<VariableUsageDomain>> getSegmentsContainingExpr(CExpression pOp2) {
    return state.getSegments()
        .parallelStream()
        .filter(s -> s.getSegmentBound().contains(pOp2))
        .collect(Collectors.toList());
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain> validate(
      ArraySegmentationState<VariableUsageDomain> pState,
      CIdExpression pVar,
      CExpression pOp2,
      BinaryOperator pOperator) {
    return SegmentationReachabilityChecker.checkReachability(pState, pVar, pOp2, pOperator, logger, visitor);
  }

}
