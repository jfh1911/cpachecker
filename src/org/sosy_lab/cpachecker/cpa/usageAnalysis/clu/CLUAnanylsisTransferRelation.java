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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.clu;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.location.LocationStateFactory;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.transfer.SegmentationTransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.UsageAnalysisTransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageState;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

public class CLUAnanylsisTransferRelation extends
    ForwardingTransferRelation<CLUAnalysisState<VariableUsageState>, CLUAnalysisState<VariableUsageState>, Precision> {

  private final LogManagerWithoutDuplicates logger;
  private final MachineModel machineModel;

  private static final String PREFIX = "CLU_ANALYSIS:";
  private final SegmentationTransferRelation<VariableUsageState> usageTransfer;
  private LocationStateFactory locFactory;

  public CLUAnanylsisTransferRelation(
      LogManagerWithoutDuplicates pLogger,
      MachineModel pMachineModel,
      LocationStateFactory pLocFactory) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
    usageTransfer =
        new SegmentationTransferRelation<>(
            new UsageAnalysisTransferRelation(pLogger, pMachineModel),
            pLogger,
            pMachineModel,
            "CLU");
    this.locFactory = pLocFactory;
  }

  @Override
  protected CLUAnalysisState<VariableUsageState>
      handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageState> handleBlankEdge(BlankEdge pCfaEdge) {
    try {
      return delegateEdgeHandling(pCfaEdge);
    } catch (CPATransferException e) {
      // TODO Enhance error Handling
      throw new IllegalArgumentException(e);
    }
  }

  @Override
  protected CLUAnalysisState<VariableUsageState> handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageState> handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageState>
      handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge) throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageState>
      handleReturnStatementEdge(CReturnStatementEdge pCfaEdge) throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageState>
      handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageState>
      handleAssumption(CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);

  }

  /**
   * Applies the transfer functions of the included analysis to a copy of the current state
   *
   * @param pCfaEdge the current edge
   * @return the element obtained by the transfer functions
   * @throws CPATransferException if any transfer function throws one or more than one result is
   *         returned
   */
  private CLUAnalysisState<VariableUsageState> delegateEdgeHandling(AbstractCFAEdge pCfaEdge)
      throws CPATransferException {
    if (super.state == null) {
      return state;
    }
    // Clone the state
    Collection<ArraySegmentationState<VariableUsageState>> arraySegmentation =
        usageTransfer.getAbstractSuccessorsForEdge(
            state.getArraySegmentation().clone(),
            getPrecision(),
            pCfaEdge);
    // Check if a single result is returned
    if (arraySegmentation.size() != 1) {
      throw new CPATransferException(
          PREFIX
              + "The UsageAnalysis transfer function could not determine a single sucessor, hence computation is abported");
    }
    List<ArraySegmentationState<VariableUsageState>> transformedSeg =
        new ArrayList<>(arraySegmentation);
    // Determine the correct successor of the the current location

    return new CLUAnalysisState<>(
        locFactory.getState(pCfaEdge.getSuccessor()),
        transformedSeg.get(0),
        this.logger);
  }
}
