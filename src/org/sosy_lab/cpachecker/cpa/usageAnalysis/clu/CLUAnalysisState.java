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

import java.io.Serializable;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Graphable;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.ArraySegmentationState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class CLUAnalysisState<T extends LatticeAbstractState<T>>
    implements Serializable, LatticeAbstractState<CLUAnalysisState<T>>, AbstractState, Graphable {

  private static final long serialVersionUID = 7499975316022760688L;
  private final LocationState location;
  private final ArraySegmentationState<VariableUsageState> arraySegmentation;
  private LogManager logger;

  public CLUAnalysisState(
      LocationState pLocation,
      ArraySegmentationState<VariableUsageState> pArraySegmentation,
      LogManager pLogger) {
    super();
    location = pLocation;
    arraySegmentation = pArraySegmentation;
    this.logger = pLogger;
  }

  @Override
  public CLUAnalysisState<T> join(CLUAnalysisState<T> pOther)
      throws CPAException, InterruptedException {

    if (!pOther.getClass().equals(this.getClass())) {
      throw new CPAException("The join cannot be applied for two differently initalized generics");
    }
    if (pOther.equals(this)) {
      return pOther;
    } else if (this.location.equals(pOther.getLocation())) {
      CLUAnalysisState<T> returnElement;
      String mergeLogInfo =
          "Computing merge(" + this.toDOTLabel() + " , " + pOther.toDOTLabel() + ") --> ";

      ArraySegmentationState<VariableUsageState> joinSegmentation =
          this.arraySegmentation.join(pOther.getArraySegmentation().clone());
      if (joinSegmentation.equals(pOther.getArraySegmentation())) {
        returnElement = pOther;
      } else {
        returnElement = new CLUAnalysisState<>(this.location, joinSegmentation, this.logger);
      }

      logger.log(Level.FINE, mergeLogInfo + returnElement.toDOTLabel());
      return returnElement;

    } else {
      return pOther;
    }

  }

  @Override
  public boolean isLessOrEqual(CLUAnalysisState<T> pOther)
      throws CPAException, InterruptedException {
    // It only make sense to compare CLUAnalysisStates belonging to the same location, hence return
    // false, if the locations differ;
    if (!this.location.getLocationNode().equals(pOther.getLocation().getLocationNode())) {
      return false;
    } else {
      return this.arraySegmentation.isLessOrEqual(pOther.getArraySegmentation());
    }
  }

  @Override
  public CLUAnalysisState<T> clone() {
    return new CLUAnalysisState<>(this.location, this.arraySegmentation.clone(), logger);
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((arraySegmentation == null) ? 0 : arraySegmentation.hashCode());
    result = prime * result + ((location == null) ? 0 : location.hashCode());
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    CLUAnalysisState other = (CLUAnalysisState) obj;
    if (arraySegmentation == null) {
      if (other.arraySegmentation != null) {
        return false;
      }
    } else if (!arraySegmentation.equals(other.arraySegmentation)) {
      return false;
    }
    if (location == null) {
      if (other.location != null) {
        return false;
      }
    } else if (!location.getLocationNode().equals(other.location.getLocationNode())) {
      return false;
    }
    return true;
  }

  public LocationState getLocation() {
    return location;
  }

  public ArraySegmentationState<VariableUsageState> getArraySegmentation() {
    return arraySegmentation;
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    builder.append(location.getLocationNode().getNodeNumber() + "|-->");
    builder.append(this.arraySegmentation.toDOTLabel());
    return builder.toString();

  }

  @Override
  public String toDOTLabel() {
    return this.toString();
  }

  @Override
  public boolean shouldBeHighlighted() {
    return false;
  }

}
