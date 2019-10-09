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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAddressOfLabelExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CCastExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CTypeIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cfa.types.c.CBasicType;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.EmptyVariableUsageElement;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageDomain;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ErrorSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.FinalSegSymbol;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UnreachableArraySegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UsageAnalysisCPA;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UsageAnalysisTransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.util.TransformationHelper;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

public class StatementTrasformer {

  private TransformationHelper helper;
  private LogManager logger;
  ExpressionSimplificationVisitor visitor;
  UsageTransformer usageTransformer;

  public StatementTrasformer(
      LogManager pLogger,
      ExpressionSimplificationVisitor pVisitor,
      UsageTransformer pUsageTransformer) {
    this.helper = new TransformationHelper(pLogger);
    this.logger = pLogger;
    this.visitor = pVisitor;
    this.usageTransformer = pUsageTransformer;
  }

  public @Nullable ArraySegmentationState<VariableUsageDomain>
      transform(ArraySegmentationState<VariableUsageDomain> state, CStatement pStatement)
          throws CPATransferException {
    if (state == null) {
      return state;
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (UsageAnalysisTransferRelation.isCornerCase(state)) {
      return state;
    }
    // Check, if the RHS contains any usage of the array
    state = usageTransformer.use(pStatement, state);

    // Check, if the LHS is a variable, else return
    if (pStatement instanceof CExpressionAssignmentStatement
        && ((CExpressionAssignmentStatement) pStatement)
            .getLeftHandSide() instanceof CIdExpression) {
      CExpressionAssignmentStatement stmt = (CExpressionAssignmentStatement) pStatement;
      CIdExpression var = (CIdExpression) stmt.getLeftHandSide();

      // Check, if the RHS contains the Var (reassignment)
      if (isReplacement(stmt.getRightHandSide(), var)) {
        // Case 1
        return replace(var, stmt.getRightHandSide(), state);
      } else {
        // Case 2
        return reassign(var, stmt.getRightHandSide(), state);
      }

    } // Handle FunctionCalls
    else if (pStatement instanceof CFunctionCallAssignmentStatement) {
      CFunctionCallAssignmentStatement call = (CFunctionCallAssignmentStatement) pStatement;
      // If a variable is assigned the return value of a function call, we loose all information
      // about
      // the variable.
      // Only in case if the variable is SIZE, we can reuse the assumption that all variables in the
      // segment are smaller to SIZE
      if (call.getLeftHandSide() instanceof CIdExpression
          && ((CIdExpression) call.getLeftHandSide()).getName()
              .equalsIgnoreCase(UsageAnalysisCPA.VARMANE_FOR_ARRAY_LENGTH)) {
        // First, remove the expression and than add it to the end
        state = helper.cleanExprFromSegBounds((CIdExpression) call.getLeftHandSide(), state);
        if (null != state) {
          // Check, if the current last segment contains any analysis information, if not, add _|_?
          // to it. Anyway, mark it as potentially empty

          List<ArraySegment<VariableUsageDomain>> segments = state.getSegments();
          int posCurrenLast = segments.size() - 1;
          if (segments.get(posCurrenLast)
              .getAnalysisInformation() instanceof EmptyVariableUsageElement) {
            segments.get(posCurrenLast).setAnalysisInformation(state.gettBottom());
          }
          segments.get(posCurrenLast).setPotentiallyEmpty(true);
          ArrayList<AExpression> bounds = new ArrayList<>();
          bounds.add(call.getLeftHandSide());
          ArraySegment<VariableUsageDomain> lastSegment =
              new ArraySegment<>(
                  bounds,
                  VariableUsageDomain.getEmptyElement(),
                  false,
                  new FinalSegSymbol<>(VariableUsageDomain.getEmptyElement()));
          state.addSegment(lastSegment, state.getSegments().get(state.getSegments().size() - 1));

          return state;
        } else {
          throw new CPATransferException("Could not cleanup the segment bound" + state.toString());

        }
      } else if (call.getLeftHandSide() instanceof CIdExpression) {
        // Remove all occurrences of the variable

        state = helper.cleanExprFromSegBounds((CIdExpression) call.getLeftHandSide(), state);
        if (null != state) {
          return state;
        } else {
          throw new CPATransferException("Could not cleanup the segment bound");
        }
      }

    }
    return state;
  }

  public ArraySegmentationState<VariableUsageDomain>
      reassign(
          CIdExpression pVar,
          CExpression pRightHandSide,
          ArraySegmentationState<VariableUsageDomain> state) {
    CExpression canoncialForm = getCanonicalForm(pRightHandSide);
    List<ArraySegment<VariableUsageDomain>> exprList = new ArrayList<>();
    // FIXME: FIX this to correctly detect values
    for (ArraySegment<VariableUsageDomain> s : state.getSegments()) {
      for (AExpression e : s.getSegmentBound()) {
        if (e.equals(canoncialForm)) {
          exprList.add(s);
        }
      }
    }
    if (exprList.size() > 1) {
      logger.log(
          Level.FINE,
          UsageAnalysisTransferRelation.PREFIX
              + "THe segmentation is invalid, since the expression that should be reassigned is present twice."
              + "Hence, the error symbol is returned. Current State is: "
              + state.toDOTLabel()
              + " for the expression :"
              + pVar.toASTString()
              + " := "
              + pRightHandSide.toASTString());
      return new ErrorSegmentation<>();
    } else if (exprList.size() == 1) {
      // Here, we are changing the ordering ( in the original transfer relation, the elements are
      // added firstly, than the others are removed. Anyway, changing these two steps leads to the
      // Exact same results!
      state = helper.cleanExprFromSegBounds(pVar, state);
      if (null == state) {
        logger.log(
            Level.FINE,
            UsageAnalysisTransferRelation.PREFIX
                + "The cleanup for the segmentation "
                + state.toDOTLabel()
                + " and expression "
                + pVar.toASTString()
                + " has failed. The error label is returned");
        return new ErrorSegmentation<>();
      }
      // Add pVar to pRightHandSide
      exprList.get(0).addSegmentBound(pVar);
      return state;
    } else {
      // The expression pRightHandSide is not present, hence check, where to split the segment
      // bounds. We are using the following assumptions:
      // 1. The variable pVar is smaller or equal to all expression in the last segment bound
      // 2. The expression pRightHandSide evaluates to a integer!
      // 3. The first segment contains the integer value 0!

      // TODO: Remove strong assumption, that pRightHandSide evaluates to integer
      if (canoncialForm instanceof CIntegerLiteralExpression) {

        state = helper.cleanExprFromSegBounds(pVar, state);
        if (null == state) {

          logger.log(
              Level.FINE,
              UsageAnalysisTransferRelation.PREFIX
                  + "The cleanup for the segmentation "
                  + " and expression "
                  + pVar.toASTString()
                  + " has failed. The error label is returned");
          return new ErrorSegmentation<>();
        }

        // Get the greatest element strictly smaller than pRightHandSide
        // Since by assumption only one variable is tracked, all other expressions evaluate either
        // to an integer value, contains the variable pVar or are the last element!
        BigInteger valueOfExpr = ((CIntegerLiteralExpression) canoncialForm).getValue();

        // We can start at the second element, since by assumption 0 is always present and hence e >
        // 0
        boolean isAdded = false;
        for (int i = 1; i < state.getSegments().size(); i++) {
          ArraySegment<VariableUsageDomain> s = state.getSegments().get(i);
          BigInteger curValue = s.evaluateToInteger(visitor);
          if (curValue.compareTo(valueOfExpr) > 0) {
            // This is the first segment that is greater than the one needs to be added, hence add
            // it between the previous and this segment
            ArraySegment<VariableUsageDomain> prevSeg = state.getSegments().get(i - 1);
            List<AExpression> segBounds = new ArrayList<>();
            segBounds.add(pVar);
            segBounds.add(pRightHandSide);
            ArraySegment<VariableUsageDomain> newSeg =
                new ArraySegment<>(
                    segBounds,
                    prevSeg.getAnalysisInformation(),
                    prevSeg.isPotentiallyEmpty(),
                    s);
            state.addSegment(newSeg, prevSeg);
            isAdded = true;
          }
        }
        // taking the assumption into account, that the variable pVar is smaller or equal to all
        // expression in the last segment bound, we can add it before the last segment!
        // We need to assume that there are at least two segments present. IN case that only a
        // single segment is present, nothing can be done!

        if (!isAdded && state.getSegments().size() > 1) {
          ArraySegment<VariableUsageDomain> prevSeg =
              state.getSegments().get(state.getSegments().size() - 2);
          List<AExpression> segBounds = new ArrayList<>();
          segBounds.add(pVar);
          segBounds.add(pRightHandSide);
          ArraySegment<VariableUsageDomain> newSeg =
              new ArraySegment<>(
                  segBounds,
                  prevSeg.getAnalysisInformation(),
                  prevSeg.isPotentiallyEmpty(),
                  state.getSegments().get(state.getSegments().size() - 1));
          state.addSegment(newSeg, prevSeg);
        } else {
          // At this point, we know that: 1. 0 = SIZE, and the variable pVar := x , x \in N & x > 0.
          // If x would have been equal to 0, then pVar would have been added. Hence, the assumption
          // pVar <= SIZE is violated and the unreachable Segment is returned!
          return new UnreachableArraySegmentation<>();
        }
      } else {

        // TODO: Avoid this case
        return state;
      }

    }
    return state;
  }

  /**
   * Replace the variable pVar in all segment bounds with the inverse of pRightHandSide (meaning if
   * RHS = i+1 --> replaced with i-1 and vice versa)
   *
   * @param pVar
   * @param pRightHandSide
   * @param state
   * @return
   */
  private ArraySegmentationState<VariableUsageDomain>
      replace(
          CIdExpression pVar,
          CExpression pRightHandSide,
          @Nullable ArraySegmentationState<VariableUsageDomain> state) {
    CExpression reversedExpr = reverseIfNeccessary(pRightHandSide);
    CExpression canoncialForm = getCanonicalForm(reversedExpr);
    for (int i = 0; i < state.getSegments().size(); i++) {
      ArraySegment<VariableUsageDomain> s = state.getSegments().get(i);
      s.replaceVar(pVar, canoncialForm, visitor);
    }
    return state;
  }

  private CExpression reverseIfNeccessary(CExpression pRightHandSide) {
    if (pRightHandSide instanceof CBinaryExpression) {
      CBinaryExpression binary = (CBinaryExpression) pRightHandSide;
      switch (binary.getOperator()) {
        case PLUS:
          return new CBinaryExpression(
              binary.getFileLocation(),
              binary.getExpressionType(),
              binary.getCalculationType(),
              binary.getOperand1(),
              binary.getOperand2(),
              CBinaryExpression.BinaryOperator.MINUS);
        case MINUS:
          return new CBinaryExpression(
              binary.getFileLocation(),
              binary.getExpressionType(),
              binary.getCalculationType(),
              binary.getOperand1(),
              binary.getOperand2(),
              CBinaryExpression.BinaryOperator.PLUS);
        default:
          return binary;
      }
    }
    return pRightHandSide;
  }

  private boolean isReplacement(CExpression pRHS, CIdExpression pVar) {
    if (pRHS instanceof CIdExpression && pRHS.equals(pVar)) {
      return true;
    } else if (pRHS instanceof CBinaryExpression) {
      CBinaryExpression expr = (CBinaryExpression) pRHS;
      return isReplacement(expr.getOperand1(), pVar) || isReplacement(expr.getOperand2(), pVar);
    }
    return false;
  }

  private CExpression getCanonicalForm(CExpression pExpr) {
    CExpression returnExpr = pExpr;

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
    if (returnExpr instanceof CIntegerLiteralExpression) {
      CType type = ((CIntegerLiteralExpression) returnExpr).getExpressionType();
      if (type instanceof CSimpleType) {
        CSimpleType simpleType = (CSimpleType) type;
        if (simpleType.getType().equals(CBasicType.INT)) {
          CSimpleType newSimpleType =
              new CSimpleType(
                  false,
                  false,
                  CBasicType.INT,
                  false,
                  false,
                  false,
                  false,
                  false,
                  false,
                  false);
          return CIntegerLiteralExpression
              .createDummyLiteral(((CIntegerLiteralExpression) returnExpr).asLong(), newSimpleType);
        }
      }
    }

    return returnExpr;
  }

}
