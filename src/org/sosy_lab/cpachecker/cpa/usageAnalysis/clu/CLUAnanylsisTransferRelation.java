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
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageDomain;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UsageAnalysisTransferRelation;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

public class CLUAnanylsisTransferRelation extends
    ForwardingTransferRelation<CLUAnalysisState<VariableUsageDomain>, CLUAnalysisState<VariableUsageDomain>, Precision> {

  private final LogManagerWithoutDuplicates logger;
  private final MachineModel machineModel;

  private static final String PREFIX = "CLU_ANALYSIS:";
  private final UsageAnalysisTransferRelation usageTransfer;
  private LocationStateFactory locFactory;

  public CLUAnanylsisTransferRelation(
      LogManagerWithoutDuplicates pLogger,
      MachineModel pMachineModel,
      LocationStateFactory pLocFactory) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
    usageTransfer = new UsageAnalysisTransferRelation(logger, machineModel);
    this.locFactory = pLocFactory;
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain>
      handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain> handleBlankEdge(BlankEdge pCfaEdge) {
    try {
      return delegateEdgeHandling(pCfaEdge);
    } catch (CPATransferException e) {
      // TODO Enhance error Handling
      throw new IllegalArgumentException(e);
    }
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain> handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain> handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain>
      handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge) throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain>
      handleReturnStatementEdge(CReturnStatementEdge pCfaEdge) throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain>
      handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUAnalysisState<VariableUsageDomain>
      handleAssumption(CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);

  }

  private CLUAnalysisState<VariableUsageDomain> delegateEdgeHandling(AbstractCFAEdge pCfaEdge)
      throws CPATransferException {
    if (super.state == null) {
      return state;
    }
    Collection<ArraySegmentationState<VariableUsageDomain>> arraySegmentation =
        usageTransfer
            .getAbstractSuccessorsForEdge(state.getArraySegmentation(), getPrecision(), pCfaEdge);
    // Check if a single reslt is returned
    if (arraySegmentation.size() != 1) {
      throw new CPATransferException(
          PREFIX
              + "The UsageAnalysis transfer function could not determine a single sucessor, hence computation is abported");
    }
    List<ArraySegmentationState<VariableUsageDomain>> transformedSeg =
        new ArrayList<>(arraySegmentation);
    // Determine the correct successor of the the current location

    return new CLUAnalysisState<>(
        locFactory.getState(pCfaEdge.getSuccessor()),
        transformedSeg.get(0),
        this.logger);
  }
}
