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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.transfer;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ErrorSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ExtendedCompletLatticeAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.UnreachableSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.formula.FormulaState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.util.EnhancedCExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.Triple;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.SolverException;

public class CSegmentationStrengthener<T extends ExtendedCompletLatticeAbstractState<T>> {

  private MachineModel machineModel;
  private LogManagerWithoutDuplicates logger;
  private CBinaryExpressionBuilder binExprBuilder;
  private CUpdateTransformer<T> updateTransformer;
  private ExpressionSimplificationVisitor visitor;

  public CSegmentationStrengthener(
      MachineModel pMachineModel,
      LogManagerWithoutDuplicates pLogger,
      CUpdateTransformer<T> pUpdateTransformer) {
    super();
    machineModel = pMachineModel;
    logger = pLogger;
    updateTransformer = pUpdateTransformer;
    binExprBuilder = new CBinaryExpressionBuilder(machineModel, logger);
    visitor = new EnhancedCExpressionSimplificationVisitor(machineModel, logger);
  }

  public ArraySegmentationState<T> strengthen(
      ArraySegmentationState<T> pSegmentation,
      FormulaState pFormulaState,
      PathFormula pPathFormula,
      CFAEdge pCfaEdge)
      throws InterruptedException, UnrecognizedCodeException {

    // Firstly, check for corner cases Unreachable and Error segment
    if (pSegmentation instanceof UnreachableSegmentation
        || pSegmentation instanceof ErrorSegmentation) {
      return pSegmentation;
    }

    // For logging:
    ArraySegmentationState<T> copy = pSegmentation.clone();

    // There is a formula to strengthen the segmentation, hence continue;
    // Check, if the formula has any information about the variables present in the formula
    SSAMap ssa = pFormulaState.getPathFormula().getSsa();
    FormulaManagerView manager = pFormulaState.getPr().getFormulaManager();
    CtoFormulaConverter converter = pFormulaState.getPr().getConverter();

    pSegmentation =
        strengthenWithSmallerAndSmallerEqual(
            pSegmentation,
            pFormulaState,
            pCfaEdge,
            ssa,
            manager,
            converter);

    // Again, check for corner cases Unreachable and Error segment
    if (pSegmentation instanceof UnreachableSegmentation
        || pSegmentation instanceof ErrorSegmentation) {
      return pSegmentation;
    }

    // This is a rather radical approach, needs to be verified on a theoretical point
    // We are now checking, if the array may be empty. If yes, we conjunct the path formula with the
    // clause (SIZE != 0) and see, if we can infer a more precise result. Since we made the
    // Assumption that the array segmentation belongs to an empty array, we set the flag
    // "mayBeEmpty"
    ArraySegmentationState<T> copyAfterFirstiteration = pSegmentation.clone();
    try {
      Optional<BooleanFormula> bfGEQ =
          getBooleanFormula(
              (CExpression) pSegmentation.getSizeVar(),
              CIntegerLiteralExpression.ZERO,
              BinaryOperator.GREATER_EQUAL,
              converter,
              pPathFormula,
              pCfaEdge,
              manager);
      Optional<BooleanFormula> bfEQ =
          getBooleanFormula(
              (CExpression) pSegmentation.getSizeVar(),
              CIntegerLiteralExpression.ZERO,
              BinaryOperator.EQUALS,
              converter,
              pPathFormula,
              pCfaEdge,
              manager);
      if (bfEQ.isPresent() && bfGEQ.isPresent()) {
        if (pFormulaState.getPr()
            .getSolver()
            .implies(pFormulaState.getPathFormula().getFormula(), bfGEQ.get())) {

          BooleanFormula pf =
              manager.getBooleanFormulaManager()
                  .and(
                      pPathFormula.getFormula(),
                      manager.getBooleanFormulaManager().not(bfEQ.get()));
          FormulaState updatedFormulaState =
              new FormulaState(
                  new PathFormula(
                      pf,
                      ssa,
                      pPathFormula.getPointerTargetSet(),
                      pPathFormula.getLength() + 1),
                  pFormulaState.getPr());
          updatedFormulaState.whilebefore = pFormulaState.whilebefore;
          updatedFormulaState.formulabefore1 = pFormulaState.formulabefore1;

          pSegmentation =
              strengthenWithSmallerAndSmallerEqual(
                  pSegmentation,
                  updatedFormulaState,
                  pCfaEdge,
                  ssa,
                  manager,
                  converter);
          if (!copyAfterFirstiteration.equals(pSegmentation)) {
            pSegmentation.setCanBeEmpty(true);
          }

        }
      }
    } catch (SolverException e) {
      logger.log(
          Level.FINE,
          "An solver error occured while strengthening the current segmentation: "
              + pSegmentation.toString()
              + e.toString());
    }
    if (!copy.equals(pSegmentation)) {
      logger
          .log(Level.FINE, "Strengthend the array segmentation" + copy + " to:  " + pSegmentation);
    }
    return pSegmentation;
  }

  private Optional<BooleanFormula> getBooleanFormula(
      CExpression pExpr1,
      CExpression pExpr2,
      BinaryOperator pOp,
      CtoFormulaConverter converter,
      PathFormula pPathFormula,
      CFAEdge pCfaEdge,
      FormulaManagerView manager) {

    CBinaryExpression sizeGEqZero;
    try {
      sizeGEqZero = binExprBuilder.buildBinaryExpression(pExpr1, pExpr2, pOp);

      Formula ifThenElseFormulaGEQ =
          converter.buildTermFromPathFormula(pPathFormula, sizeGEqZero, pCfaEdge);
      Optional<Triple<BooleanFormula, Formula, Formula>> bfGEQOptional =
          manager.splitIfThenElse(ifThenElseFormulaGEQ);
      if (bfGEQOptional.isPresent()) {
        return Optional.of(bfGEQOptional.get().getFirst());
      }
    } catch (UnrecognizedCodeException e) {
      e.printStackTrace();
      return Optional.empty();
    } catch (Throwable e) {
      System.out.println();
    }
    return Optional.empty();

  }

  private ArraySegmentationState<T> strengthenWithSmallerAndSmallerEqual(
      ArraySegmentationState<T> pSegmentation,
      FormulaState pFormulaState,
      CFAEdge pCfaEdge,
      SSAMap ssa,
      FormulaManagerView manager,
      CtoFormulaConverter converter)
      throws UnrecognizedCodeException, InterruptedException {
    // Iterate through all segmentations and check , if two consecutive segment bounds can be made
    // more precise by removing ?
    for (int i = 0; i < pSegmentation.getSegments().size() - 1; i++) {
      List<Pair<BooleanFormula, CBinaryExpression>> equations =
          getEquations(
              pSegmentation.getSegments().get(i).getSegmentBound(),
              pSegmentation.getSegments().get(i + 1).getSegmentBound(),
              BinaryOperator.LESS_THAN,
              ssa,
              manager,
              converter,
              binExprBuilder,
              pFormulaState.getPathFormula(),
              pCfaEdge);
      equations.addAll(
          getEquations(
              pSegmentation.getSegments().get(i + 1).getSegmentBound(),
              pSegmentation.getSegments().get(i).getSegmentBound(),
              BinaryOperator.LESS_EQUAL,
              ssa,
              manager,
              converter,
              binExprBuilder,
              pFormulaState.getPathFormula(),
              pCfaEdge));

      for (Pair<BooleanFormula, CBinaryExpression> eq : equations) {
        try {
          if (pFormulaState.getPr()
              .getSolver()
              .implies(pFormulaState.getPathFormula().getFormula(), eq.getFirst())) {
            pSegmentation =
                this.updateTransformer.update(eq.getSecond(), true, pSegmentation);
          }
        } catch (SolverException e) {
          logger.log(
              Level.FINE,
              "An solver error occured while strengthening the current segmentation: "
                  + pSegmentation.toString()
                  + e.toString());
        } catch (CPATransferException e) {
          logger.log(
              Level.FINE,
              "An transformation error occured while strengthening the current segmentation: "
                  + pSegmentation.toString()
                  + e.toString());
        }
      }
    }
    return pSegmentation;
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
  private List<Pair<BooleanFormula, CBinaryExpression>> getEquations(
      List<AExpression> pSB1,
      List<AExpression> pSB2,
      BinaryOperator pBinaryOp,
      SSAMap pSsa,
      FormulaManagerView pManager,
      CtoFormulaConverter pConverter,
      CBinaryExpressionBuilder pBinExprBuilder,
      PathFormula pFormula,
      CFAEdge pEdge)
      throws UnrecognizedCodeException {
    List<Pair<BooleanFormula, CBinaryExpression>> res = new ArrayList<>();
    for (int i = 0; i < pSB1.size(); i++) {
      CExpression e1 = (CExpression) pSB1.get(i);
      for (int j = 0; j < pSB2.size(); j++) {
        CExpression e2 = (CExpression) pSB2.get(j);
        CBinaryExpression smaller;

        // TODO: To improve performance, one can check, if the expressions e1 and e2 are present in
        // the current pathFormula
        smaller = pBinExprBuilder.buildBinaryExpression(e1, e2, pBinaryOp);
        Formula ifThenElseFormula = pConverter.buildTermFromPathFormula(pFormula, smaller, pEdge);
        Optional<Triple<BooleanFormula, Formula, Formula>> booleanFormulaOptional =
            pManager.splitIfThenElse(ifThenElseFormula);
        if (booleanFormulaOptional.isPresent()) {
          BooleanFormula smallerExpr = (booleanFormulaOptional.get().getFirst());
          res.add(Pair.of(smallerExpr, smaller));
        }

      }

    }
    return res;
  }

}
