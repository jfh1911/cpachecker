// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import java.io.Serializable;
import java.util.List;
import java.util.Objects;

public class SharmaInterpolationTaskList implements Serializable{

  private static final long serialVersionUID = 7154327625010347694L;
  List<InterpolationTaskExchangeObject> interpolationQueries;

  public SharmaInterpolationTaskList(List<InterpolationTaskExchangeObject> pInterpolationQueries) {
    super();
    interpolationQueries = pInterpolationQueries;
  }

  public List<InterpolationTaskExchangeObject> getInterpolationQueries() {
    return interpolationQueries;
  }

  public void setInterpolationQueries(List<InterpolationTaskExchangeObject> pInterpolationQueries) {
    interpolationQueries = pInterpolationQueries;
  }

  @Override
  public int hashCode() {
    return Objects.hash(interpolationQueries);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof SharmaInterpolationTaskList)) {
      return false;
    }
    SharmaInterpolationTaskList other = (SharmaInterpolationTaskList) obj;
    return Objects.equals(interpolationQueries, other.interpolationQueries);
  }
}
