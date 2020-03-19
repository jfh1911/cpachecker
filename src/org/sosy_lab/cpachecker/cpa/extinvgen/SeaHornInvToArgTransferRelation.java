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

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;

public class SeaHornInvToArgTransferRelation implements TransferRelation {
  Map<CFANode, ExpressionTree<AExpression>> generatedInvariants;
  private ExpressionTree<AExpression> defaultValue;

  public SeaHornInvToArgTransferRelation(
      Map<CFANode, ExpressionTree<AExpression>> pGeneratedInvariants,
      ExpressionTree<AExpression> pDefaultValue) {
    generatedInvariants = pGeneratedInvariants;
    defaultValue = pDefaultValue;
  }

  @Override
  public Collection<? extends AbstractState>
      getAbstractSuccessors(AbstractState pState, Precision pPrecision)
          throws CPATransferException, InterruptedException {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  public Collection<? extends AbstractState>
      getAbstractSuccessorsForEdge(AbstractState pState, Precision pPrecision, CFAEdge pCfaEdge)
          throws CPATransferException, InterruptedException {
    return Collections
        .singleton(
            new SeaHornInvToArgState(generatedInvariants, defaultValue, pCfaEdge.getSuccessor()));
  }

}
