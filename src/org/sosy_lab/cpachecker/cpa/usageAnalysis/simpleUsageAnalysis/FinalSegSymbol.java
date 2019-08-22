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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis;

import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;

/**
 * A Segment that is by default empty, to indicate that the segment pointing to this is the last
 * segment (avoiding null as value)
 */
public class FinalSegSymbol<T extends LatticeAbstractState<T>> extends ArraySegment<T> {


  private static final long serialVersionUID = -5615014169972238864L;

  public FinalSegSymbol(T emptyElement) {
    super(null, emptyElement, true, null);
  }

  @Override
  public String toString() {
    return "<<EOF>>";
  }

  @Override
  public void setAnalysisInformation(T pAnalysisInformation) {
    // TODO Auto-generated method stub
    super.setAnalysisInformation(pAnalysisInformation);
  }

}
