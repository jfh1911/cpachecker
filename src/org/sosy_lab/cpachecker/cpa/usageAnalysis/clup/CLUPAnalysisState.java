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

import java.io.Serializable;
import java.util.Objects;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractQueryableState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Graphable;
import org.sosy_lab.cpachecker.cpa.arraySegmentation.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.arraySegmentation.formula.FormulaState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.InvalidQueryException;

public class CLUPAnalysisState<T extends LatticeAbstractState<T>>
    implements Serializable, LatticeAbstractState<CLUPAnalysisState<T>>, AbstractState, Graphable,
    AbstractQueryableState {

  private static final long serialVersionUID = 7499975316022760688L;
  private final LocationState location;
  private final ArraySegmentationState<VariableUsageState> arraySegmentation;
  private final FormulaState pathFormula;
  private LogManager logger;

  public CLUPAnalysisState(
      LocationState pLocation,
      ArraySegmentationState<VariableUsageState> pArraySegmentation,
      FormulaState pPathFormula,
      LogManager pLogger) {
    super();
    location = pLocation;
    arraySegmentation = pArraySegmentation;
    this.pathFormula = pPathFormula;
    this.logger = pLogger;
  }

  @Override
  public CLUPAnalysisState<T> join(CLUPAnalysisState<T> pOther)
      throws CPAException, InterruptedException {

    if (!pOther.getClass().equals(this.getClass())) {
      throw new CPAException("The join cannot be applied for two differently initalized generics");
    }
    if (pOther.equals(this)) {
      return pOther;
    } else if (this.location.equals(pOther.getLocation())) {
      CLUPAnalysisState<T> returnElement;
      String mergeLogInfo =
          "Computing merge(" + this.toDOTLabel() + " , " + pOther.toDOTLabel() + ") --> ";

      ArraySegmentationState<VariableUsageState> joinSegmentation =
          this.arraySegmentation.join(new ArraySegmentationState<>(pOther.getArraySegmentation()));
      FormulaState joinedFormula = this.pathFormula.join(pOther.getPathFormula());

      if (joinSegmentation.equals(pOther.getArraySegmentation())
          && joinedFormula.equals(pOther.getPathFormula())) {
        returnElement = pOther;
      } else {
        returnElement =
            new CLUPAnalysisState<>(this.location, joinSegmentation, joinedFormula, this.logger);
      }

      logger.log(Level.FINE, mergeLogInfo + returnElement.toDOTLabel());
      return returnElement;

    } else {
      return pOther;
    }

  }

  @Override
  public boolean isLessOrEqual(CLUPAnalysisState<T> pOther)
      throws CPAException, InterruptedException {
    // It only make sense to compare CLUAnalysisStates belonging to the same location, hence return
    // false, if the locations differ;
    if (!this.location.getLocationNode().equals(pOther.getLocation().getLocationNode())) {
      return false;
    } else {
      return this.arraySegmentation.isLessOrEqual(pOther.getArraySegmentation())
          && this.pathFormula.isLessOrEqual(pOther.getPathFormula());
    }
  }

  @Override
  public CLUPAnalysisState<T> clone() {
    return new CLUPAnalysisState<>(
        this.location,
        new ArraySegmentationState<>(this.arraySegmentation),
        pathFormula.clone(),
        logger);
  }

  @Override
  public int hashCode() {
    return Objects.hash(arraySegmentation, location, logger, pathFormula);
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
    CLUPAnalysisState other = (CLUPAnalysisState) obj;
    return Objects.equals(arraySegmentation, other.arraySegmentation)
        && Objects.equals(location.getLocationNode(), other.location.getLocationNode())
        && Objects.equals(logger, other.logger)
        && Objects.equals(pathFormula, other.pathFormula);
  }

  public LocationState getLocation() {
    return location;
  }

  public ArraySegmentationState<VariableUsageState> getArraySegmentation() {
    return arraySegmentation;
  }

  public FormulaState getPathFormula() {
    return pathFormula;
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    builder.append(location.getLocationNode().getNodeNumber() + "|-->");
    builder.append(this.arraySegmentation.toDOTLabel());
    builder.append(this.pathFormula.toDOTLabel());
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

  @Override
  public String getCPAName() {
    return "UsageAnalysisCPA";
  }

  @Override
  public boolean checkProperty(String pProperty) throws InvalidQueryException {
    return this.arraySegmentation.checkProperty(pProperty);
  }

}
