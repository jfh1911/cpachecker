/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.extinvgen;

import java.util.Map;
import java.util.Objects;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ExpressionTreeReportingState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTrees;

public class SeaHornInvToArgState
    implements ExpressionTreeReportingState, LatticeAbstractState<SeaHornInvToArgState> {

  private Map<CFANode, ExpressionTree<AExpression>> globalInvMap;
  private ExpressionTree<AExpression> defaultValue;
  private CFANode location;

  public SeaHornInvToArgState(
      Map<CFANode, ExpressionTree<AExpression>> pGlobalInvMap,
      ExpressionTree<AExpression> pDefaultValue,
      CFANode pLocation) {
    globalInvMap = pGlobalInvMap;
    defaultValue = pDefaultValue;
    location = pLocation;
  }

  @Override
  public ExpressionTree<Object>
      getFormulaApproximation(FunctionEntryNode pFunctionScope, CFANode pLocation) {
    return ExpressionTrees.cast(globalInvMap.getOrDefault(pLocation, defaultValue));
  }

  @Override
  public SeaHornInvToArgState join(SeaHornInvToArgState pOther)
      throws CPAException, InterruptedException {
    return pOther;
  }

  @Override
  public boolean isLessOrEqual(SeaHornInvToArgState pOther)
      throws CPAException, InterruptedException {
    return true;
  }

  @Override
  public int hashCode() {
    return Objects.hash(defaultValue, globalInvMap, location);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (!(obj instanceof SeaHornInvToArgState)) {
      return false;
    }
    SeaHornInvToArgState other = (SeaHornInvToArgState) obj;
    return Objects.equals(location, other.location);
  }

}
