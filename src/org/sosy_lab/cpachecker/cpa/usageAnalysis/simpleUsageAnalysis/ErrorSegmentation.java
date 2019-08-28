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

import java.util.ArrayList;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class ErrorSegmentation<T extends LatticeAbstractState<T>> extends
    ArraySegmentationState<T> {

  public ErrorSegmentation() {
    // This is bad stlye, but whenever the error or unreachable segment is used, the information are
    // not needed
    // TODO infer a more elegant way
    super(new ArrayList<>(), null, null, null, null, null, null, null);
  }

  private static final long serialVersionUID = -3937221925009806448L;

  @Override
  public boolean isLessOrEqual(ArraySegmentationState<T> pOther)
      throws CPAException, InterruptedException {
    // Only if they are equal, this is true, else false, since this is the top element of the
    // lattice
    return pOther instanceof ErrorSegmentation;

  }

  @Override
  public ArraySegmentationState<T> join(ArraySegmentationState<T> pOther)
      throws CPAException, InterruptedException {
    // Since this is the top element of the lattice, we can simply return it
    return this;
  }

  @Override
  public String toString() {
    return Character.toString((char) 9632);
  }

  @Override
  public ArraySegmentationState<T> clone() {
    return this;
  }

}
