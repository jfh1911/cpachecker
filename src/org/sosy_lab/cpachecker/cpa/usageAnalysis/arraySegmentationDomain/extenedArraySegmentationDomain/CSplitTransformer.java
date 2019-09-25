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
          state = splitSegmentBound(posOfVar, pVar, pEx, pState);
        } else {
          state = pState;
        }
        // TODO: Determine, if the ordering is fixed:
        // for (int i = posOfVar; i < state.getSegments().size(); i++) {
        // ArraySegment<T> current = state.getSegments().get(i);
        // for(AExpression e : current.getSegmentBound()) {
        // }
        // }

        // Since the ordering is not fixed, we need to split the segmentation:
        ArraySegmentationState<T> first = state.clone();
        ArraySegmentationState<T> second = new UnreachableSegmentation<>(state.clone());

        // Create first:
        first.setSplitCondition(
            builder.buildBinaryExpression(
                pEx,
                (CExpression) state.getSizeVar(),
                BinaryOperator.LESS_EQUAL));
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
        FormulaState f = state.getPathFormula();
        Optional<BooleanFormula> equation =
            getEquation(
                pEx,
                (CExpression) state.getSizeVar(),
                BinaryOperator.LESS_EQUAL,
                f.getPathFormula().getSsa(),
                f.getPr().getFormulaManager(),
                f.getPr().getConverter(),
                f.getPathFormula(),
                pCfaEdge);
        if (equation.isPresent()) {
          BooleanFormula ELessEqualSizeVar =
              f.getPr()
                  .getFormulaManager()
                  .makeEqual(f.getPathFormula().getFormula(), equation.get());
          if (solver.isUnsat(ELessEqualSizeVar)) {
            first = new UnreachableSegmentation<>(first);
          }

          // Create second
          second.setSplitCondition(
              builder.buildBinaryExpression(
                  pEx,
                  (CExpression) state.getSizeVar(),
                  BinaryOperator.GREATER_THAN));

            return new ExtendedArraySegmentationState<>(Lists.newArrayList(first, second), logger);
          }
        }

      }

    return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);

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

  public @Nullable ExtendedArraySegmentationState<T> splitLessThan(
      CIdExpression pVar,
      CExpression pExpr,
      @Nullable ArraySegmentationState<T> pState,
      CFAEdge pCfaEdge)
      throws SolverException, InterruptedException, UnrecognizedCodeException {
    Solver solver = pState.getPathFormula().getPr().getSolver();
    CExpression pEx = visitor.visit(pExpr);
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
          state = splitSegmentBound(posOfVar, pVar, pEx, pState);
        } else {
          state = pState;
        }
        // TODO: Determine, if the ordering is fixed:
        // for (int i = posOfVar; i < state.getSegments().size(); i++) {
        // ArraySegment<T> current = state.getSegments().get(i);
        // for(AExpression e : current.getSegmentBound()) {
        // }
        // }

        // Since the ordering is not fixed, we need to split the segmentation:
        ArraySegmentationState<T> first = state.clone();
        ArraySegmentationState<T> second = state.clone();

        // Determine segmentation containing var:
        ArraySegment<T> containingVar =
            state.getSegments().get(state.getSegBoundContainingExpr(pVar));

        // Create first:
        first.setSplitCondition(
            builder.buildBinaryExpression(
                pEx,
                (CExpression) state.getSizeVar(),
                BinaryOperator.LESS_EQUAL));
        ArraySegment<T> newSeg =
            new ArraySegment<>(
                Lists.newArrayList(pEx),
                containingVar.getAnalysisInformation(),
                true,
                null,
                segmentContainingI.getLanguage());
        // Add first, such that: {es} p_k ?_k -> {es}p_k ?_k {i} p_k {EX}
        first.addSegment(newSeg, containingVar);

        // Check if path-formula and Ex <= arrLen is sat:
        FormulaState f = state.getPathFormula();
        Optional<BooleanFormula> equation =
            getEquation(
                pEx,
                (CExpression) state.getSizeVar(),
                BinaryOperator.LESS_EQUAL,
                f.getPathFormula().getSsa(),
                f.getPr().getFormulaManager(),
                f.getPr().getConverter(),
                f.getPathFormula(),
                pCfaEdge);
        if (equation.isPresent()) {
          BooleanFormula ELessEqualSizeVar =
              f.getPr()
                  .getFormulaManager()
                  .makeEqual(f.getPathFormula().getFormula(), equation.get());
          if (solver.isUnsat(ELessEqualSizeVar)) {
            first = new UnreachableSegmentation<>(first);
          }


          // Create second (that is either d or unreachableSeg)
          second.setSplitCondition(
              builder.buildBinaryExpression(
                  pEx,
                  (CExpression) state.getSizeVar(),
                  BinaryOperator.GREATER_THAN));

          // Check if path-formula and Ex > arrLen is sat:
          f = state.getPathFormula();
          equation =
              getEquation(
                  pEx,
                  (CExpression) state.getSizeVar(),
                  BinaryOperator.GREATER_THAN,
                  f.getPathFormula().getSsa(),
                  f.getPr().getFormulaManager(),
                  f.getPr().getConverter(),
                  f.getPathFormula(),
                  pCfaEdge);
          if (equation.isPresent()) {
            BooleanFormula EGreaterSizeVar =
                f.getPr()
                    .getFormulaManager()
                    .makeEqual(f.getPathFormula().getFormula(), equation.get());
            if (solver.isUnsat(EGreaterSizeVar)) {
              second = new UnreachableSegmentation<>(first);
            }

            return new ExtendedArraySegmentationState<>(Lists.newArrayList(first, second), logger);
          }
        }
      }
    }
    return new ExtendedArraySegmentationState<>(Lists.newArrayList(pState), logger);

  }

  private ArraySegmentationState<T> splitSegmentBound(
      int pPosOfVar,
      CIdExpression pVar,
      CExpression pEx,
      @Nullable ArraySegmentationState<T> pState) {

    // Check, if a constant e_j is present
    CIntegerLiteralExpression constValue = null;
    ArraySegment<T> segOfVar = pState.getSegments().get(pPosOfVar);
    for (AExpression b : segOfVar.getSegmentBound()) {
      if (b instanceof CIntegerLiteralExpression) {
        constValue = (CIntegerLiteralExpression) b;
        break;
      }
    }
    if (constValue != null && pEx instanceof CIntegerLiteralExpression) {
      List<AExpression> otherExpr = new ArrayList<>(segOfVar.getSegmentBound());
      otherExpr.remove(pVar);
      if (constValue.getValue().compareTo(((CIntegerLiteralExpression) pEx).getValue()) < 0) {
        // The constant is smaller than pEx, continue with {e_j,..} p_j ? {i} p_j ?_j ...

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
        return pState;
      } else if (constValue.getValue()
          .compareTo(((CIntegerLiteralExpression) pEx).getValue()) > 0) {
        // The constant is smaller than pEx, continue with {i} p_j ? {e_j,..} p_j ?_j ...
        // remove other from seOfVar
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
        return pState;
      }
      // TODO: Extend for size var
    }

    return pState;
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

}
