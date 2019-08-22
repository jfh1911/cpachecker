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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.compositPredicate;

import java.io.Serializable;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Graphable;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageDomain;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.usageDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class ComposedUsagePredicateAnalysisState
    implements Serializable, LatticeAbstractState<ComposedUsagePredicateAnalysisState>,
    AbstractState, Graphable {

  private static final long serialVersionUID = 5104530752877695093L;

  private ArraySegmentationState<VariableUsageDomain> segmentation;
  private LocationState location;
  private PredicateAbstractState predicates;


  public ComposedUsagePredicateAnalysisState(
      ArraySegmentationState<VariableUsageDomain> pSegmentation,
      LocationState pLocation,
      PredicateAbstractState pPredicates) {
    super();
    segmentation = pSegmentation;
    location = pLocation;
    predicates = pPredicates;
  }

  public ComposedUsagePredicateAnalysisState() {
    // TODO Auto-generated constructor stub
  }

  @Override
  public String toDOTLabel() {
    return "["
        + location.toString()
        + " - "
        + segmentation.toDOTLabel()
        + " - "
        + predicates.toString();
  }

  @Override
  public boolean shouldBeHighlighted() {
    return this.segmentation.shouldBeHighlighted();
  }

  @Override
  public ComposedUsagePredicateAnalysisState join(ComposedUsagePredicateAnalysisState pOther)
      throws CPAException, InterruptedException {
if (this.location.equals(pOther.getLocation())) {
  return new ComposedUsagePredicateAnalysisState(this.segmentation.join(pOther.getSegmentation(), this.location, this.predicates.setMergedInto(pOther.predicates))
}
  }

  @Override
  public boolean isLessOrEqual(ComposedUsagePredicateAnalysisState pOther)
      throws CPAException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }

  public ArraySegmentationState<VariableUsageDomain> getSegmentation() {
    return segmentation;
  }

  public void setSegmentation(ArraySegmentationState<VariableUsageDomain> pSegmentation) {
    segmentation = pSegmentation;
  }

  public LocationState getLocation() {
    return location;
  }

  public void setLocation(LocationState pLocation) {
    location = pLocation;
  }

  public PredicateAbstractState getPredicates() {
    return predicates;
  }

  public void setPredicates(PredicateAbstractState pPredicates) {
    predicates = pPredicates;
  }

}
