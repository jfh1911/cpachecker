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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.extenedArraySegmentationDomain.usage;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.simplification.ExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ErrorSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageType;

public class UsageTransformer {

  private MachineModel machineModel;
  private LogManager logger;
  private ExpressionSimplificationVisitor visitor;

  public UsageTransformer(
      MachineModel pMachineModel,
      LogManager pLogger,
      ExpressionSimplificationVisitor pVisitor) {
    super();
    machineModel = pMachineModel;
    logger = pLogger;
    visitor = pVisitor;
  }

  public @Nullable ArraySegmentationState<VariableUsageState>
      use(
          CStatement pStatement,
          ArraySegmentationState<VariableUsageState> state,
          CFAEdge pCfaEdge) {
    List<CArraySubscriptExpression> arrayUses = getUses(pStatement);
    return explUse(arrayUses, state, pCfaEdge);
  }

  public @Nullable ArraySegmentationState<VariableUsageState> explUse(
      Collection<CArraySubscriptExpression> pUses,
      ArraySegmentationState<VariableUsageState> state,
      CFAEdge pCfaEdge) {
    for (CArraySubscriptExpression use : pUses) {

      CExpression subscriptExpr = use.getSubscriptExpression();
      if (!state.storeAnalysisInformationAtIndex(
          subscriptExpr,
          new VariableUsageState(VariableUsageType.USED),
          false,
          machineModel,
          visitor,
          pCfaEdge)) {
        return new ErrorSegmentation<>(state);
      }
    }
    return state;
  }

  public List<CArraySubscriptExpression> getUses(CStatement pStatement) {
    List<CArraySubscriptExpression> uses = new ArrayList<>();
    if (pStatement instanceof CAssignment) {
      // The LHS is not considered, since it is not an usage (only reassignment)
      // uses.addAll(getUses(((CAssignment) pStatement).getLeftHandSide()));
      uses.addAll(getUses(((CAssignment) pStatement).getRightHandSide()));
    } else if (pStatement instanceof CFunctionCall) {
      uses.addAll(getUses(((CFunctionCall) pStatement).getFunctionCallExpression()));
    }
    return uses;
  }

  public Collection<CArraySubscriptExpression> getUses(CRightHandSide pExpr) {
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
