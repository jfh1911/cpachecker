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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAddressOfLabelExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CCastExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpressionAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CInitializerExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CTypeIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
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
import org.sosy_lab.cpachecker.cfa.types.c.CBasicType;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.EmptyVariableUsageElement;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageDomain;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageType;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.util.EnhancedExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;

public class UsageAnalysisTransferRelation extends
    ForwardingTransferRelation<ArraySegmentationState<VariableUsageDomain>, ArraySegmentationState<VariableUsageDomain>, Precision> {

  private final LogManagerWithoutDuplicates logger;
  private final MachineModel machineModel;
  private static final String PREFIX = "USAGE_ANALYSIS:";

  public UsageAnalysisTransferRelation(
      LogManagerWithoutDuplicates pLogger,
      MachineModel pMachineModel) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain>
      handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
          throws CPATransferException {
    if (super.state == null) {
      return state;
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return super.state;
    }

    // Check if a variable is assigned
    if (pDecl instanceof CVariableDeclaration
        && ((CVariableDeclaration) pDecl).getInitializer() instanceof CInitializerExpression) {
      CVariableDeclaration varDecl = (CVariableDeclaration) pDecl;
      // Now ensure that the variable needs to be checked (is a array variable
      return this.reassign(
          new CIdExpression(pDecl.getFileLocation(), pDecl),
          ((CInitializerExpression) varDecl.getInitializer()).getExpression());
    }
    return state;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain> handleBlankEdge(BlankEdge pCfaEdge) {
    // TODO: Verify that this is the correct behavior
    return state;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain> handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {// TODO: Verify that this is the correct behavior
    return state;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain> handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    return state;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain>
      handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge) throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    return state;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain>
      handleReturnStatementEdge(CReturnStatementEdge pCfaEdge) throws CPATransferException {
    // TODO: Verify that this is the correct behavior
    return state;
  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain>
      handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
          throws CPATransferException {
    if (super.state == null) {
      return state;
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return super.state;
    }

    // Check, if the RHS contains any usage of the array
    state = use(pStatement);

    // Check, if the LHS is a variable, else return
    if (pStatement instanceof CExpressionAssignmentStatement
        && ((CExpressionAssignmentStatement) pStatement)
            .getLeftHandSide() instanceof CIdExpression) {
      CExpressionAssignmentStatement stmt = (CExpressionAssignmentStatement) pStatement;
      CIdExpression var = (CIdExpression) stmt.getLeftHandSide();

      // Check, if the RHS contains the Var (reassignment)
      if (isReplacement(stmt.getRightHandSide(), var)) {
        // Case 1
        return replace(var, stmt.getRightHandSide());
      } else {
        // Case 2
        return reassign(var, stmt.getRightHandSide());
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
        if (cleanExprFromSegBounds((CIdExpression) call.getLeftHandSide())) {
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
          throw new CPATransferException(
              "Could not cleanup the segment bound" + this.state.toString());

        }
      } else if (call.getLeftHandSide() instanceof CIdExpression) {
        // Remove all occurrences of the variable
        if (cleanExprFromSegBounds((CIdExpression) call.getLeftHandSide())) {
          return state;
        } else {
          throw new CPATransferException(
              "Could not cleanup the segment bound" + this.state.toString());
        }
      }

    }

    return state;

  }

  @Override
  protected ArraySegmentationState<VariableUsageDomain>
      handleAssumption(CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
          throws CPATransferException {
    if (super.state == null) {
      return state;
    }
    // Check, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return super.state;
    }
    // Check, if any variable is used
    Collection<CArraySubscriptExpression> uses = this.getUses(pExpression);
    if (!uses.isEmpty()) {
      state = explUse(new ArrayList<>(uses));
    }

    // Check again, if a corner-case applies and the state can be returned directly:
    else if (isCornerCase(super.getState())) {
      return super.state;
    }

    // Case 3: Update(e,d)
    if (pExpression instanceof CBinaryExpression) {
      UpdateTransformer u = new UpdateTransformer(state, logger);
      return u.update((CBinaryExpression) pExpression);
    } else {
      return state;
    }
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain> use(CStatement pStatement) {
    List<CArraySubscriptExpression> arrayUses = getUses(pStatement);
    return explUse(arrayUses);
  }

  private @Nullable ArraySegmentationState<VariableUsageDomain>
      explUse(List<CArraySubscriptExpression> pArrayUses) {
    CBinaryExpressionBuilder builder = new CBinaryExpressionBuilder(this.machineModel, this.logger);
    for (CArraySubscriptExpression use : pArrayUses) {
      // Check, if the expression used to access the array element is present in the current state
      CExpression subscriptExpr = use.getSubscriptExpression();
      int pos = state.getSegBoundContainingExpr(subscriptExpr);
      if (pos < 0) {
        logger.log(
            Level.FINE, PREFIX+
            "Cannot create a usage sincethe variable "
                + subscriptExpr.toASTString()
                + " is not present in the segmentation, hence the error symbol is returned. Current State is: "
                + this.state.toDOTLabel()
                + " for the expression :"
                + pArrayUses.toString());
        return new ErrorSegmentation<>();
      } else {
        // Create a new segment after the segment containing the expression to access the array
        // elements and mark this as used
        ArraySegment<VariableUsageDomain> leftBound = state.getSegments().get(pos);
        ExpressionSimplificationVisitor visitor =
            new EnhancedExpressionSimplificationVisitor(machineModel, logger);
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
              Level.FINE, PREFIX+
              "Cannot create a usage due to internal problems, hence the error symbol is returned. Current State is: "
                  + this.state.toDOTLabel()
                  + " for the expression :"
                  + pArrayUses.toString());
          return new ErrorSegmentation<>();
        }
        if (!leftBound.getNextSegment().getSegmentBound().contains(exprPlus1)) {
          // Add the segment bound
          List<AExpression> bounds = new ArrayList<>();
          bounds.add(exprPlus1);
          ArraySegment<VariableUsageDomain> newSeg =
              new ArraySegment<>(bounds, leftBound.getAnalysisInformation(), true, null);
          state.addSegment(newSeg, leftBound);
        }
        leftBound.setAnalysisInformation(new VariableUsageDomain(VariableUsageType.USED));
        leftBound.setPotentiallyEmpty(false);
      }

    }
    return state;
  }

  private ArraySegmentationState<VariableUsageDomain>
      reassign(CIdExpression pVar, CExpression pRightHandSide) {
    ArraySegmentationState<VariableUsageDomain> clonedState = this.state.clone();

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
          Level.FINE, PREFIX+
          "THe segmentation is invalid, since the expression that should be reassigned is present twice."
              + "Hence, the error symbol is returned. Current State is: "
              + this.state.toDOTLabel()
              + " for the expression :"
              + pVar.toASTString()
              + " := "
              + pRightHandSide.toASTString());
      return new ErrorSegmentation<>();
    } else if (exprList.size() == 1) {
      // Here, we are changing the ordering ( in the original transfer relation, the elements are
      // added firstly, than the others are removed. Anyway, changing these two steps leads to the
      // Exact same results!
      if (!cleanExprFromSegBounds(pVar)) {
        logger.log(
            Level.FINE, PREFIX+
            "The cleanup for the segmentation "
                + state.toDOTLabel() + " and expression " + pVar.toASTString()
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

        if (!cleanExprFromSegBounds(pVar)) {

          logger.log(
              Level.FINE, PREFIX+
              "The cleanup for the segmentation "
                  + state.toDOTLabel() + " and expression " + pVar.toASTString()
                  + " has failed. The error label is returned");
          return new ErrorSegmentation<>();
        }

        // Get the greatest element strictly smaller than pRightHandSide
        // Since by assumption only one variable is tracked, all other expressions evaluate either
        // to an integer value, contains the variable pVar or are the last element!
        BigInteger valueOfExpr = ((CIntegerLiteralExpression) canoncialForm).getValue();
        ExpressionSimplificationVisitor visitor =
            new EnhancedExpressionSimplificationVisitor(machineModel, logger);
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
        return clonedState;
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
   * @return
   */
  private ArraySegmentationState<VariableUsageDomain>
      replace(CIdExpression pVar, CExpression pRightHandSide) {
    CExpression reversedExpr = reverseIfNeccessary(pRightHandSide);
    CExpression canoncialForm = getCanonicalForm(reversedExpr);
    for (int i = 0; i < state.getSegments().size(); i++) {
      ArraySegment<VariableUsageDomain> s = state.getSegments().get(i);
      s.replaceVar(
          pVar,
          canoncialForm,
          new EnhancedExpressionSimplificationVisitor(machineModel, logger));
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

  private CExpression getCanonicalForm(CExpression pExpr) {
    CExpression returnExpr = pExpr;
    ExpressionSimplificationVisitor visitor =
        new ExpressionSimplificationVisitor(machineModel, logger);
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

  /**
   *
   * removes all expressions from the segment bound containing the expression pVar
   *
   * @param pVar to be removed
   * @return true, if the segments containing pVar are cleaned, false if any error occurred
   */
  private boolean cleanExprFromSegBounds(CIdExpression pVar) {
    state.getSegments().forEach(s -> s.removeExprContainingSubExpr(pVar));
    try {
      state.mergeSegmentsWithEmptySegmentBounds();
    } catch (CPAException | InterruptedException e) {
      logger.log(
          Level.SEVERE,
          "An error occured while removing the expression"
              + pVar.toASTString()
              + " from "
              + this.state.toDOTLabel()
              + e.getStackTrace().toString());
      // TODO Enhance error handling
      return false;
    }
    // Remove the '?' at the last segment if present
    if (state.getSegments().isEmpty()) {
      // All segment bounds were removed, report a failure
      logger.log(
          Level.FINE, PREFIX+
          "The segmentation has become empty, this is invalid after removing the expression"
              + pVar.toASTString()
              + ". Hence, the error symbol is returned");
      return false;
    }
    state.getSegments().get(state.getSegments().size() - 1).setPotentiallyEmpty(false);
    return true;
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

  private boolean isCornerCase(ArraySegmentationState<VariableUsageDomain> s) {
    return s instanceof ErrorSegmentation || s instanceof UnreachableArraySegmentation;
  }

  private List<CArraySubscriptExpression> getUses(CStatement pStatement) {
    List<CArraySubscriptExpression> uses = new ArrayList<>();
    if (pStatement instanceof CAssignment) {
      uses.addAll(getUses(((CAssignment) pStatement).getLeftHandSide()));
      uses.addAll(getUses(((CAssignment) pStatement).getRightHandSide()));
    } else if (pStatement instanceof CFunctionCall) {
      uses.addAll(getUses(((CFunctionCall) pStatement).getFunctionCallExpression()));
    }
    return uses;
  }

  private Collection<CArraySubscriptExpression> getUses(CRightHandSide pExpr) {
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
