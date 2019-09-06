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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain;

import java.util.ArrayList;
import java.util.function.Predicate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class UnreachableSegmentation<T extends ExtendedCompletLatticeAbstractState<T>>
    extends ArraySegmentationState<T> {

  public UnreachableSegmentation(
      LogManager pLogger,
      String pCpaName,
      Predicate<ArraySegmentationState<T>> pPropertyPredicate,
      T pEmptyElement) {
    // This is bad stlye, but whenever the error or unreachable segment is used, the information are
    // not needed
    // TODO infer a more elegant way
    super(
        new ArrayList<>(),
        pEmptyElement,
        null,
        null,
        null,
        null,
        false,
        pCpaName,
        pPropertyPredicate,
        pLogger);
  }

  private static final long serialVersionUID = -3937221925009806448L;

  @Override
  public boolean isLessOrEqual(ArraySegmentationState<T> pOther)
      throws CPAException, InterruptedException {
    return true;
  }

  @Override
  public ArraySegmentationState<T> join(ArraySegmentationState<T> pOther)
      throws CPAException, InterruptedException {
    return pOther;
  }

  @Override
  public String toString() {
    return "[x]";
  }

  @Override
  public ArraySegmentationState<T> clone() {
    return this;
  }

}
