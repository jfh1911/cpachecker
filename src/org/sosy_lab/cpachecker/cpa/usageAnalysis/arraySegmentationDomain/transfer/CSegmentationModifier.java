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
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ExtendedCompletLatticeAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.FinalSegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.util.ArrayModificationException;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.UsageAnalysisTransferRelation;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;

public class CSegmentationModifier<T extends ExtendedCompletLatticeAbstractState<T>> {

  private LogManager logger;
  private MachineModel machineModel;
  private ExpressionSimplificationVisitor visitor;
  private CBinaryExpressionBuilder builder;

  public CSegmentationModifier(
      LogManager pLogger,
      MachineModel pMachineModel,
      ExpressionSimplificationVisitor pVisitor) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
    visitor = pVisitor;
    builder = new CBinaryExpressionBuilder(machineModel, logger);
  }

  public ArraySegmentationState<T> storeAnalysisInformationAtIndex(
      ArraySegmentationState<T> state,
      CExpression pIndex,
      T pAnalysisInfo,
      boolean pNewSegmentIsPotentiallyEmpty)
      throws ArrayModificationException {

    // Check, if the expression used to access the array element is present in the current state
    int pos = state.getSegBoundContainingExpr(pIndex);
    if (pos < 0) {
      String errorMsg =
          UsageAnalysisTransferRelation.PREFIX
              + "Cannot create a usage sincethe variable "
              + pIndex.toASTString()
              + " is not present in the segmentation, hence the error symbol is returned. Current State is: "
              + state.toDOTLabel();
      logger.log(Level.FINE, errorMsg);
      throw new ArrayModificationException(errorMsg);
    } else {
      // Create a new segment after the segment containing the expression to access the array
      // elements and mark this as used
      ArraySegment<T> leftBound = state.getSegments().get(pos);
      CExpression exprPlus1;
      try {
        exprPlus1 =
            visitor.visit(
                builder.buildBinaryExpression(
                    pIndex,
                    CIntegerLiteralExpression.ONE,
                    CBinaryExpression.BinaryOperator.PLUS));
      } catch (UnrecognizedCodeException e) {
        e.printStackTrace();
        String errorMsg =
            UsageAnalysisTransferRelation.PREFIX
                + "Cannot create a usage due to internal problems, hence the error symbol is returned. Current State is: "
                + state.toDOTLabel()
                + " for the index :"
                + pIndex.toString();
        logger.log(Level.FINE, errorMsg);
        throw new ArrayModificationException(errorMsg, e);
      }
      if (leftBound.getNextSegment() instanceof FinalSegment) {
        throw new ArrayModificationException(
            "Cannot add information for an index nt present in the array range!");
      }
      if (!leftBound.getNextSegment().getSegmentBound().contains(exprPlus1)) {
        // Add the segment bound
        List<AExpression> bounds = new ArrayList<>();
        bounds.add(exprPlus1);
        ArraySegment<T> newSeg =
            new ArraySegment<>(
                bounds,
                leftBound.getAnalysisInformation(),
                true,
                null,
                state.getLanguage());
        state.addSegment(newSeg, leftBound);
      }
      return storeAnalysisInformationAtIndexWithoutAddingBounds(
          state,
          pIndex,
          pAnalysisInfo,
          pNewSegmentIsPotentiallyEmpty);
    }
  }

  public ArraySegmentationState<T> storeAnalysisInformationAtIndexWithoutAddingBounds(
      ArraySegmentationState<T> state,
      CExpression pIndex,
      T pAnalysisInfo,
      boolean pNewSegmentIsPotentiallyEmpty)
      throws ArrayModificationException {
    // Check, if the expression used to access the array element is present in the current state
    // Check, if index+1 is the following segment of the one containing pIndex

    CExpression exprPlus1;
    try {
      exprPlus1 =
          visitor.visit(
              builder.buildBinaryExpression(
                  pIndex,
                  CIntegerLiteralExpression.ONE,
                  CBinaryExpression.BinaryOperator.PLUS));
    } catch (UnrecognizedCodeException e) {
      e.printStackTrace();
      String errorMsg =
          UsageAnalysisTransferRelation.PREFIX
              + "Cannot create a usage due to internal problems, hence the error symbol is returned. Current State is: "
              + state.toDOTLabel()
              + " for the index :"
              + pIndex.toString();
      logger.log(Level.FINE, errorMsg);
      throw new ArrayModificationException(errorMsg, e);
    }
    int pos = state.getSegBoundContainingExpr(pIndex);
    int posNext = state.getSegBoundContainingExpr(exprPlus1);

    if (pos < 0 || pos != posNext - 1) {
      String errorMsg =
          UsageAnalysisTransferRelation.PREFIX
              + "Cannot create a usage since the variable "
              + pIndex.toASTString()
              + " or "
              + pIndex.toASTString()
              + "+1 is not present in the segmentation, hence the error symbol is returned. Current State is: "
              + state.toDOTLabel();
      logger.log(Level.FINE, errorMsg);
      throw new ArrayModificationException(errorMsg);
    } else {

      ArraySegment<T> leftBound = state.getSegments().get(pos);
      leftBound.setAnalysisInformation(pAnalysisInfo);
      leftBound.setPotentiallyEmpty(pNewSegmentIsPotentiallyEmpty);

      return state;
    }

  }
}
