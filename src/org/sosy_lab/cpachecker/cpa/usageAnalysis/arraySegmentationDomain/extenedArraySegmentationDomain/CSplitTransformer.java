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
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CBasicType;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ExtendedCompletLatticeAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.UnreachableSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.formula.FormulaState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.util.EnhancedCExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.Triple;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.SolverException;

public class CSplitTransformer<T extends ExtendedCompletLatticeAbstractState<T>> {

  EnhancedCExpressionSimplificationVisitor visitor;
  CBinaryExpressionBuilder builder;
  final static BinaryOperator OPERATOR_FIRST_SEGMENTATION = BinaryOperator.LESS_THAN;
  final static BinaryOperator OPERATOR_SECOND_SEGMENTATION = BinaryOperator.EQUALS;
  final static BinaryOperator OPERATOR_THIRD_SEGMENTATION = BinaryOperator.GREATER_THAN;

  private LogManager logger;

  public CSplitTransformer(
      EnhancedCExpressionSimplificationVisitor pVisitor,
      CBinaryExpressionBuilder pBuilder,
      LogManager pLogger) {
    super();
    visitor = pVisitor;
    builder = pBuilder;
    logger = pLogger;
  }

  public @Nullable ExtendedArraySegmentationState<T> splitLessThan(
      CIdExpression pVar,
      CExpression pExpr,
      @Nullable ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge)
      throws SolverException, InterruptedException, UnrecognizedCodeException {
    Solver solver = pState.getPathFormula().getPr().getSolver();
    CExpression pEx = visitor.visit(pExpr);
    pEx = convertSignedIntToInt(pEx);
    // TODO: Maybe use solver aswell

    // Firstly, check if the transformation can be applied. Therefore, check if the second operator
    // only contains constants and the array size var
    if (isApplicable(pEx, pState.getSizeVar())) {
      int posOfVar = pState.getSegBoundContainingExpr(pVar);
      if (posOfVar != -1) {
        ArraySegment<T> segmentContainingI = pState.getSegments().get(posOfVar);

        // Next, check if the segment bound containing the variable pVar does contain only other
        // expressions e_x, such that e_x != pEx may hold (checked if their equality is
        // unsatisfiable
        // FIXME: Add this check
        // if(segmentContainingI.getSegmentBound().stream().anyMatch(e -> (! pVar.equals(e) ) &&
        // solver.isUnsat()))

        // Split the segmentation is there are more than one expression present in the segmentation
        // containing the variable
        ArraySegmentationState<T> state;
        if (segmentContainingI.getSegmentBound().size() > 1) {
          Optional<ArraySegmentationState<T>> stateOpt =
              splitSegmentBound(posOfVar, pVar, pEx, pState, pCfaEdge);
          if (stateOpt.isPresent()) {
            state = stateOpt.get();
          } else {
            return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
          }
        } else {
          state = pState;
        }

        // Determine segmentation containing var:
        int indexOfpVarNew = state.getSegBoundContainingExpr(pVar);
        ArraySegment<T> containingVar = state.getSegments().get(indexOfpVarNew);

        // Determine, if the ordering is fixed:
        if (orderingIsFixed(pVar, pExpr, state, pCfaEdge)) {
          // Add the segmentation containing pEx between i and eg:
          ArraySegment<T> newSeg = getNewSegment(pEx, segmentContainingI, containingVar);
          state.addSegment(newSeg, state.getSegments().get(indexOfpVarNew - 1));
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(state), logger);
        }

        // Since the ordering is not fixed, we need to split the segmentation:
        ArraySegmentationState<T> first = state.clone();
        ArraySegmentationState<T> third = state.clone();

        // Create first:

        first.setSplitCondition(
            builder.buildBinaryExpression(
                pEx,
                (CExpression) state.getSizeVar(),
                OPERATOR_FIRST_SEGMENTATION));
        ArraySegment<T> newSeg = getNewSegment(pEx, segmentContainingI, containingVar);
        // Add first, such that: {es} p_k ?_k -> {es}p_k ?_k {i} p_k {EX}
        first.addSegment(newSeg, containingVar);

        // Check if path-formula and Ex < arrLen is sat:
        Optional<Boolean> resOfCheck =
            isUnsat(
                state,
                pEx,
                pCfaEdge,
                solver,
                OPERATOR_FIRST_SEGMENTATION,
                (CExpression) state.getSizeVar());
        if (!resOfCheck.isPresent()) {
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
        }
        if (resOfCheck.get()) {
          first = new UnreachableSegmentation<>(first);
        }

        // Create second, (that is d where E is added to the last segment or unreachableSeg)
        Optional<ArraySegmentationState<T>> second =
            getSecond(pCfaEdge, solver, pEx, state, state.clone());
        if (!second.isPresent()) {
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
        }

        // Create third (that is either d or unreachableSeg)
        third.setSplitCondition(
            builder.buildBinaryExpression(
                pEx,
                (CExpression) state.getSizeVar(),
                OPERATOR_THIRD_SEGMENTATION));

        // Check if path-formula and Ex > arrLen is sat:
        resOfCheck =
            isUnsat(
                state,
                pEx,
                pCfaEdge,
                solver,
                OPERATOR_THIRD_SEGMENTATION,
                (CExpression) state.getSizeVar());
        if (!resOfCheck.isPresent()) {
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
        }
        if (resOfCheck.get()) {
          third = new UnreachableSegmentation<>(third);
        }
        return new ExtendedArraySegmentationState<>(
            Lists.newArrayList(first, second.get(), third),
            logger);
      }
    }
    return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
  }

  public @Nullable ExtendedArraySegmentationState<T> splitGreaterThan(
      CIdExpression pVar,
      CExpression pExpr,
      @Nullable ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge)
      throws SolverException, InterruptedException, UnrecognizedCodeException {

    Solver solver = pState.getPathFormula().getPr().getSolver();
    // Build e+1 needed for the rest of the method
    CExpression pEx =
        visitor.visit(
            builder
                .buildBinaryExpression(pExpr, CIntegerLiteralExpression.ONE, BinaryOperator.PLUS));
    pEx = convertSignedIntToInt(pEx);
    // TODO: Maybe use solver aswell

    // Firstly, check if the transformation can be applied. Therefore, check if the second operator
    // only contains constants and the array size var
    if (isApplicable(pEx, pState.getSizeVar())) {
      int posOfVar = pState.getSegBoundContainingExpr(pVar);
      if (posOfVar != -1) {
        ArraySegment<T> segmentContainingI = pState.getSegments().get(posOfVar);

        // Next, check if the segment bound containing the variable pVar does contain only other
        // expressions e_x, such that e_x != pEx may hold (checked if their equality is
        // unsatisfiable
        // FIXME: Add this check
        // if(segmentContainingI.getSegmentBound().stream().anyMatch(e -> (! pVar.equals(e) ) &&
        // solver.isUnsat()))

        // Split the segmentation is there are more than one expression present in the segmentation
        // containing the variable
        ArraySegmentationState<T> state;
        if (segmentContainingI.getSegmentBound().size() > 1) {
          Optional<ArraySegmentationState<T>> stateOpt =
              splitSegmentBound(posOfVar, pVar, pEx, pState, pCfaEdge);
          if (stateOpt.isPresent()) {
            state = stateOpt.get();
          } else {
            return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
          }
          segmentContainingI = pState.getSegments().get(posOfVar);
        } else {
          state = pState;
        }

        // Determine, if the ordering is fixed:
        if (orderingIsFixed(pVar, pExpr, state, pCfaEdge)) {
          // Add the segmentation containing pEx between es and i:

          ArraySegment<T> newSeg =
              new ArraySegment<>(
                  Lists.newArrayList(pEx),
                  segmentContainingI.getAnalysisInformation(),
                  true,
                  null,
                  segmentContainingI.getLanguage());
          state.addSegment(newSeg, state.getSegments().get(state.getSegBoundContainingExpr(pVar)));
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(state), logger);
        }

        // Since the ordering is not fixed, we need to split the segmentation:
        ArraySegmentationState<T> first = state.clone();
        ArraySegmentationState<T> third = new UnreachableSegmentation<>(state.clone());

        // Create first:
        first.setSplitCondition(
            builder.buildBinaryExpression(
                pEx,
                (CExpression) state.getSizeVar(),
                OPERATOR_FIRST_SEGMENTATION));
        // Add first, such that: {es} p_k ?_k {i} -> {es}p_k ?_k {EX}p_k ? {i}
        ArraySegment<T> newSeg =
            new ArraySegment<>(
                Lists.newArrayList(pEx),
                segmentContainingI.getAnalysisInformation(),
                true,
                null,
                segmentContainingI.getLanguage());

        first
            .addSegment(newSeg, first.getSegments().get(first.getSegBoundContainingExpr(pVar) - 1));

        // Check if path-formula and Ex <= arrLen is sat:
        // Check if path-formula and Ex < arrLen is sat:
        Optional<Boolean> resOfCheck =
            isUnsat(
                state,
                pEx,
                pCfaEdge,
                solver,
                OPERATOR_FIRST_SEGMENTATION,
                (CExpression) state.getSizeVar());
        if (!resOfCheck.isPresent()) {
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
        }
        if (resOfCheck.get()) {
          first = new UnreachableSegmentation<>(first);
        }

        // Create second, (that is d where E is added to the last segment or unreachableSeg)
        Optional<ArraySegmentationState<T>> second =
            getSecond(pCfaEdge, solver, pEx, state, state.clone());
        if (!second.isPresent()) {
          return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
        }

        // Create third (with condition Ex > arrLen
        third.setSplitCondition(
            builder.buildBinaryExpression(
                pEx,
                (CExpression) state.getSizeVar(),
                OPERATOR_THIRD_SEGMENTATION));

        return new ExtendedArraySegmentationState<>(
            Lists.newArrayList(first, second.get(), third),
            logger);
      }
    }
    return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);
  }

  private Optional<ArraySegmentationState<T>> getSecond(
      CFAEdge pCfaEdge,
      Solver solver,
      CExpression pEx,
      ArraySegmentationState<T> state,
      ArraySegmentationState<T> second)
      throws UnrecognizedCodeException {
    Optional<Boolean> resOfCheck;
    ArraySegment<T> secondLastSegment = second.getSegments().get(second.getSegments().size() - 1);
    secondLastSegment.addSegmentBound(pEx);
    second.setSplitCondition(
        builder.buildBinaryExpression(
            pEx,
            (CExpression) state.getSizeVar(),
            OPERATOR_SECOND_SEGMENTATION));
    // Check if path-formula and Ex = arrLen is sat:
    resOfCheck =
        isUnsat(
            state,
            pEx,
            pCfaEdge,
            solver,
            OPERATOR_SECOND_SEGMENTATION,
            (CExpression) state.getSizeVar());
    if (!resOfCheck.isPresent()) {
      return Optional.empty();
    }
    if (resOfCheck.get()) {
      second = new UnreachableSegmentation<>(second);
    }
    return Optional.of(second);
  }

  private ArraySegment<T> getNewSegment(
      CExpression pEx,
      ArraySegment<T> segmentContainingI,
      ArraySegment<T> containingVar) {
    return new ArraySegment<>(
        Lists.newArrayList(pEx),
        containingVar.getAnalysisInformation(),
        true,
        null,
        segmentContainingI.getLanguage());
  }

  private boolean orderingIsFixed(
      CIdExpression pVar,
      CExpression pExpr,
      ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge) {
    // Check if segment left of (i) is e_s and right of i is e_g
    boolean leftIsEs = false, rightIsEg = false;

    int segOfVar = pState.getSegBoundContainingExpr(pVar);
    if (segOfVar > 0 && segOfVar < pState.getSegments().size() + 1) {
      ArraySegment<T> leftOfVar = pState.getSegments().get(segOfVar - 1);
      ArraySegment<T> rightOfVar = pState.getSegments().get(segOfVar + 1);
      Solver solver = pState.getPathFormula().getPr().getSolver();

      // Check if any expression e in leftOfVar implies that: e <= pExpr;
      for (AExpression e : leftOfVar.getSegmentBound()) {
        Optional<Boolean> resOfCheck =
            isUnsat(pState, (CExpression) e, pCfaEdge, solver, BinaryOperator.LESS_EQUAL, pExpr);
        if (!resOfCheck.isPresent()) {
          return false;
        }
        if (resOfCheck.get()) {
          leftIsEs = true;
          break;
        }
      }

      // Check if any expression e in leftOfVar implies that: e <= pExpr;
      for (AExpression e : rightOfVar.getSegmentBound()) {
        Optional<Boolean> resOfCheck =
            isUnsat(pState, (CExpression) e, pCfaEdge, solver, BinaryOperator.GREATER_EQUAL, pExpr);
        if (!resOfCheck.isPresent()) {
          return false;
        }
        if (resOfCheck.get()) {
          rightIsEg = true;
          break;
        }
      }

    }
    return leftIsEs && rightIsEg;
  }

  private Optional<Boolean> isUnsat(
      ArraySegmentationState<T> pState,
      CExpression pEx,
      CFAEdge pCfaEdge,
      Solver solver,
      BinaryOperator pOperator,
      CExpression pRhs) {
    FormulaState f = pState.getPathFormula();
    Optional<BooleanFormula> equation;
    try {
      equation = getEquation(pEx, pRhs, pOperator, f, pCfaEdge);

      if (equation.isPresent()) {
        BooleanFormula ELessEqualSizeVar =
            f.getPr()
                .getFormulaManager()
                .makeEqual(f.getPathFormula().getFormula(), equation.get());
        return Optional.of(solver.isUnsat(ELessEqualSizeVar));
      }
    } catch (UnrecognizedCodeException | SolverException | InterruptedException e) {
      return Optional.empty();
    }

    return Optional.empty();
  }

  private Optional<BooleanFormula> getEquation(
      CExpression pEx,
      CExpression pSizeVar,
      BinaryOperator pOperator,
      FormulaState pF,
      CFAEdge pCfaEdge)
      throws UnrecognizedCodeException {
    return getEquation(
        pEx,
        pSizeVar,
        pOperator,
        pF.getPathFormula().getSsa(),
        pF.getPr().getFormulaManager(),
        pF.getPr().getConverter(),
        pF.getPathFormula(),
        pCfaEdge);
  }

  private CExpression convertSignedIntToInt(CExpression pEx) {
    if (pEx instanceof CIntegerLiteralExpression) {
      CIntegerLiteralExpression l = (CIntegerLiteralExpression) pEx;
      if (l.getExpressionType() instanceof CSimpleType) {
        CSimpleType type =
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
        return new CIntegerLiteralExpression(l.getFileLocation(), type, l.getValue());
      }

    }
    return pEx;
  }

  private Optional<ArraySegmentationState<T>> splitSegmentBound(
      int pPosOfVar,
      CExpression pVar,
      CExpression pEx,
      @Nullable ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge) {

    // Check, if a constant e_j is present
    CIntegerLiteralExpression constValue = null;
    ArraySegment<T> segOfVar = pState.getSegments().get(pPosOfVar);
    for (AExpression b : segOfVar.getSegmentBound()) {
      if (b instanceof CIntegerLiteralExpression) {
        constValue = (CIntegerLiteralExpression) b;
        break;
      }
    }
    int comparison = 0;

    if (constValue != null && pEx instanceof CIntegerLiteralExpression) {
      comparison = constValue.getValue().compareTo(((CIntegerLiteralExpression) pEx).getValue());
    } else {

      // check, if the path formula induces that an expression e is present, that is
      // greater equal or less equal than pEx
      Solver solver = pState.getPathFormula().getPr().getSolver();
      for (AExpression e : segOfVar.getSegmentBound()) {
        Optional<Boolean> resOfCheck =
            isUnsat(pState, (CExpression) e, pCfaEdge, solver, BinaryOperator.LESS_THAN, pEx);
        if (resOfCheck.isPresent() && resOfCheck.get()) {
          comparison = -1;
        }
        resOfCheck =
            isUnsat(pState, (CExpression) e, pCfaEdge, solver, BinaryOperator.GREATER_THAN, pEx);
        if (resOfCheck.isPresent() && resOfCheck.get()) {
          comparison = 1;
        }
      }

    }
    if (comparison < 0) {
      // The constant is smaller than pEx, continue with {e_j,..} p_j ? {i} p_j ?_j ...

      List<AExpression> otherExpr = new ArrayList<>(segOfVar.getSegmentBound());
      otherExpr.remove(pVar);

      // remove var from seOfVar
      List<AExpression> newSegBounds = new ArrayList<>(segOfVar.getSegmentBound());
      newSegBounds.remove(pVar);
      segOfVar.setSegmentBound(newSegBounds);

      // Create a new segment {e_j,...} p_j?
      ArraySegment<T> newSeg =
          new ArraySegment<>(
              Lists.newArrayList(pVar),
              segOfVar.getAnalysisInformation(),
              true,
              null,
              segOfVar.getLanguage());
      pState.addSegment(newSeg, segOfVar);
      return Optional.of(pState);
    } else if (comparison > 0) {
      // The constant is smaller than pEx, continue with {i} p_j ? {e_j,..} p_j ?_j ...
      // remove other from seOfVar

      List<AExpression> otherExpr = new ArrayList<>(segOfVar.getSegmentBound());
      otherExpr.remove(pVar);

      List<AExpression> newSegBounds = new ArrayList<>(segOfVar.getSegmentBound());
      newSegBounds.removeAll(otherExpr);
      segOfVar.setSegmentBound(newSegBounds);

      // Create a new segment {e_j,...} p_j?
      ArraySegment<T> newSeg =
          new ArraySegment<>(
              otherExpr,
              segOfVar.getAnalysisInformation(),
              true,
              null,
              segOfVar.getLanguage());
      pState.addSegment(newSeg, segOfVar);
      return Optional.of(pState);
    }

    return Optional.empty();
  }

  private boolean isApplicable(CExpression pExpr, AExpression pSizeVar) {
    if (pExpr instanceof CBinaryExpression) {
      return isApplicable(((CBinaryExpression) pExpr).getOperand1(), pSizeVar)
          && isApplicable(((CBinaryExpression) pExpr).getOperand2(), pSizeVar);
    } else {
      return pExpr instanceof CIntegerLiteralExpression || pSizeVar.equals(pExpr);
    }
  }

  /**
   * Computes the cross-product of all pBinaryOp expressions of all expressions present in the
   * segment, whereas the first segments' expressions are used on the LHS and the second once on the
   * RHS bounds in sb1 < sb2
   *
   * @param pSB1 used on LHS
   * @param pSB2 used on RHS
   * @param pBinaryOp the operator
   * @param pSsa current SSA transformation
   * @param pConverter to convert the expressions
   * @param pManager of the path formula
   * @param pBinExprBuilder to build expressions
   * @param pFormula the path formula
   * @param pEdge for logging
   * @return cross product of e1 pBinaryOp e2, where e1 \in pSB1 and e2 in pSB2
   * @throws UnrecognizedCodeException if converting fails
   */
  private Optional<BooleanFormula> getEquation(
      CExpression e1,
      CExpression e2,
      BinaryOperator pBinaryOp,
      SSAMap pSsa,
      FormulaManagerView pManager,
      CtoFormulaConverter pConverter,
      PathFormula pFormula,
      CFAEdge pEdge)
      throws UnrecognizedCodeException {
    CBinaryExpression expr = builder.buildBinaryExpression(e1, e2, pBinaryOp);
    Formula ifThenElseFormula = pConverter.buildTermFromPathFormula(pFormula, expr, pEdge);
    Optional<Triple<BooleanFormula, Formula, Formula>> booleanFormulaOptional =
        pManager.splitIfThenElse(ifThenElseFormula);
    if (booleanFormulaOptional.isPresent()) {
      BooleanFormula smallerExpr = (booleanFormulaOptional.get().getFirst());
      return Optional.of(smallerExpr);
    }
    return Optional.empty();

  }

  public boolean wouldBeSplitt(
      CExpression pVar,
      CExpression pExpr,
      BinaryOperator pBinaryOp,
      @Nullable ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge)
      throws UnrecognizedCodeException {
    // Find a more efficient implementation for that avoiding computing the split twice
    Solver solver = pState.getPathFormula().getPr().getSolver();
    CExpression pEx;
    if (pBinaryOp.equals(BinaryOperator.LESS_EQUAL)
        || pBinaryOp.equals(BinaryOperator.GREATER_THAN)) {
      // Increment the second operator by one
      pEx =
          visitor.visit(
              builder.buildBinaryExpression(
                  pExpr,
                  CIntegerLiteralExpression.ONE,
                  BinaryOperator.PLUS));
      pEx = convertSignedIntToInt(pEx);
    } else {
      pEx = pExpr;
    }

    // Firstly, check if the transformation can be applied. Therefore, check if the second
    // operator
    // only contains constants and the array size var
    if (isApplicable(pEx, pState.getSizeVar())) {
      int posOfVar = pState.getSegBoundContainingExpr(pVar);
      if (posOfVar != -1) {
        ArraySegment<T> segmentContainingI = pState.getSegments().get(posOfVar);

        // Next, check if the segment bound containing the variable pVar does contain only other
        // expressions e_x, such that e_x != pEx may hold (checked if their equality is
        // unsatisfiable
        // FIXME: Add this check
        // if(segmentContainingI.getSegmentBound().stream().anyMatch(e -> (! pVar.equals(e) ) &&
        // solver.isUnsat()))

        // Split the segmentation is there are more than one expression present in the
        // segmentation
        // containing the variable
        ArraySegmentationState<T> state;
        if (segmentContainingI.getSegmentBound().size() > 1) {
          Optional<ArraySegmentationState<T>> stateOpt =
              splitSegmentBound(posOfVar, pVar, pEx, pState, pCfaEdge);
          return stateOpt.isPresent();
        } else {
          state = pState;
        }
      }
    }
    return false;
  }
}
