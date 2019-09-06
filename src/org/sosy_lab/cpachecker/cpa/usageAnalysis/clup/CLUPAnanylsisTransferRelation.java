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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.clup;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.location.LocationStateFactory;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.UnreachableSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.formula.FormulaRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.formula.FormulaState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.transfer.CSegmentationTransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.UsageAnalysisTransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageState;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

public class CLUPAnanylsisTransferRelation extends
    ForwardingTransferRelation<CLUPAnalysisState<VariableUsageState>, CLUPAnalysisState<VariableUsageState>, Precision> {

  private final LogManagerWithoutDuplicates logger;
  private final MachineModel machineModel;

  private static final String PREFIX = "CLU_ANALYSIS:";
  private final CSegmentationTransferRelation<VariableUsageState> usageTransfer;
  private final FormulaRelation formulaTransfer;
  private LocationStateFactory locFactory;

  public CLUPAnanylsisTransferRelation(
      LogManagerWithoutDuplicates pLogger,
      MachineModel pMachineModel,
      LocationStateFactory pLocFactory,
      FormulaRelation pFormulaTransfer) {
    super();
    logger = pLogger;
    machineModel = pMachineModel;
    usageTransfer =
        new CSegmentationTransferRelation<>(
            new UsageAnalysisTransferRelation(pLogger, pMachineModel),
            pLogger,
            pMachineModel,
            "CLU");
    formulaTransfer = pFormulaTransfer;
    this.locFactory = pLocFactory;
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState>
      handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState> handleBlankEdge(BlankEdge pCfaEdge) {
    try {
      return delegateEdgeHandling(pCfaEdge);
    } catch (CPATransferException e) {
      // TODO Enhance error Handling
      throw new IllegalArgumentException(e);
    }
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState> handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState> handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState>
      handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge) throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState>
      handleReturnStatementEdge(CReturnStatementEdge pCfaEdge) throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState>
      handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);
  }

  @Override
  protected CLUPAnalysisState<VariableUsageState>
      handleAssumption(CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
          throws CPATransferException {
    return delegateEdgeHandling(pCfaEdge);

  }

  /**
   * Applies the transfer functions of the included analysis to a copy of the current state
   *
   * @param pCfaEdge the current edge @return the element obtained by the transfer functions @throws
   *        CPATransferException if any transfer function throws one or more than one result is
   *        returned @throws
   */
  private CLUPAnalysisState<VariableUsageState> delegateEdgeHandling(AbstractCFAEdge pCfaEdge)
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

    // Apply the transfer function for formulae on the cloned state
    Collection<? extends AbstractState> transformedFormulas;
    transformedFormulas =
        this.formulaTransfer
            .getAbstractSuccessorsForEdge(state.getPathFormula().clone(), getPrecision(), pCfaEdge);
    // Check if a single result is returned
    List<? extends AbstractState> formulaList = new ArrayList<AbstractState>(transformedFormulas);
    if (transformedFormulas.size() != 1 || !(formulaList.get(0) instanceof FormulaState)) {
      throw new CPATransferException(
          PREFIX
              + "The simplified Predicate Analysis transfer function could not determine a single sucessor, hence computation is abported");
    }

    return new CLUPAnalysisState<>(
        locFactory.getState(pCfaEdge.getSuccessor()),
        transformedSeg.get(0),
        (FormulaState) formulaList.get(0),
        this.logger);
  }

  @SuppressWarnings("unchecked")
  @Override
  public Collection<? extends AbstractState> strengthen(
      AbstractState pState,
      Iterable<AbstractState> pOtherStates,
      @Nullable CFAEdge pCfaEdge,
      Precision pPrecision)
      throws CPATransferException, InterruptedException {

    if (pState instanceof CLUPAnalysisState) {
      CLUPAnalysisState<VariableUsageState> s = (CLUPAnalysisState<VariableUsageState>) pState;
      Collection<? extends AbstractState> strengthenFormula =
          this.formulaTransfer.strengthen(
              s.getPathFormula(),
              pOtherStates,
              pCfaEdge,
              pPrecision);
      if (strengthenFormula.isEmpty()) {
        // The path formula indicates, that the current path is not reachable, since the path
        // formula is UNSAT
        // Hence, we can return the unreachable Array Segmentation [x]

        // TODO: USe something like false (e.g.
        // formulaTransfer.getFormulaManager().getBooleanFormulaManager().makeFalse()),)
        return Collections.singleton(
            new CLUPAnalysisState<VariableUsageState>(
                s.getLocation(),
                new UnreachableSegmentation<VariableUsageState>(
                    logger,
                    s.getArraySegmentation().getCPAName(),
                    s.getArraySegmentation().getPropertyPredicate(),
                    s.getArraySegmentation().gettEmptyElement()),
                s.getPathFormula(),
                logger));
      }

      // The path is reachable. Then, apply the strengthening to the inner ArraySegmentationState

      ArrayList<AbstractState> others = new ArrayList<>();
      pOtherStates.forEach(st -> others.add(st));
      others.add(s.getPathFormula());

      @SuppressWarnings("unchecked")
      Collection<ArraySegmentationState<VariableUsageState>> strengthenSegmentations =
          this.usageTransfer.strengthen(
              ((CLUPAnalysisState<VariableUsageState>) pState).getArraySegmentation().clone(),
              others,
              pCfaEdge,
              pPrecision);
      if (strengthenSegmentations.isEmpty()) {
        return Collections.singleton(pState);

      } else

      {
        ArraySegmentationState<VariableUsageState> newSegmentation =
            Collections.enumeration(strengthenSegmentations).nextElement();
        return Collections.singleton(
            new CLUPAnalysisState<VariableUsageState>(
                s.getLocation(),
                newSegmentation,
                s.getPathFormula(),
                logger));
      }

    }
    return super.strengthen(pState, pOtherStates, pCfaEdge, pPrecision);
  }


}
