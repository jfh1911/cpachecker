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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation;

import java.io.Serializable;
import java.util.function.BinaryOperator;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class VariableUsageState implements LatticeAbstractState<VariableUsageState>, Serializable {

  private static final long serialVersionUID = -3799697790388179030L;
  private VariableUsageType type;

  public VariableUsageState(VariableUsageType pType) {
    super();
    type = pType;
  }

  /**
   * The join function looks as follows: this / pOther | U N U | U U N | U N
   */
  @Override
  public VariableUsageState join(VariableUsageState pOther)
      throws CPAException, InterruptedException {
    if (type.equals(VariableUsageType.USED)) {
      return this;
    } else {
      return pOther;
    }
  }

  /**
   * The meet function looks as follows: this / pOther | U N U | U N N | N N
   *
   * @throws CPAException
   */
  public VariableUsageState meet(VariableUsageState pOther) throws CPAException {
    if (type.equals(VariableUsageType.NOT_USED)) {
      return this;
    } else {
      return pOther;
    }
  }

  /**
   * The meet function looks as follows:
   * this / pOther    | U N
   *                U | U N
   *                N | N N
   */
 public static  BinaryOperator<VariableUsageState> getMeetOperator(){
  return new BinaryOperator<VariableUsageState>() {

    @Override
    public VariableUsageState apply(VariableUsageState pT, VariableUsageState pU) {
      if (pT.getType().equals(VariableUsageType.NOT_USED)) {
        return new VariableUsageState(VariableUsageType.NOT_USED);
      }
    else {
      return new VariableUsageState(pU.getType());
    }
      }
    };

 }

  /**
   * _|_ = N <= U = T
   */
  @Override
  public boolean isLessOrEqual(VariableUsageState pOther)
      throws CPAException, InterruptedException {
    if (type.equals(VariableUsageType.USED)
        && pOther.getType().equals(VariableUsageType.NOT_USED)) {
      return false;
    }
        return true;
  }

  public static VariableUsageType getBottomElement() {
    return VariableUsageType.NOT_USED;
  }

  public static VariableUsageState getBottom() {
    return new VariableUsageState(getBottomElement());
  }

  public static VariableUsageState getTop() {
    return new VariableUsageState(getTopElement());
  }

  public static VariableUsageType getTopElement() {
    return VariableUsageType.USED;
  }

  public VariableUsageType getType() {
    return type;
  }

  public void setType(VariableUsageType pType) {
    type = pType;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((type == null) ? 0 : type.hashCode());
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
    VariableUsageState other = (VariableUsageState) obj;
    if (type != other.type) {
      return false;
    }
    return true;
  }

  @Override
  public String toString() {
    if (this.type.equals(VariableUsageType.USED)) {
      return "U";
    } else if (this.type.equals(VariableUsageType.NOT_USED)) {
      return "N";
    }
    return "";
  }

  public static VariableUsageType getEmptyElementType() {
    return VariableUsageType.EMPTY;
  }

  public static VariableUsageState getEmptyElement() {
    return new EmptyVariableUsageElement();
  }

}
