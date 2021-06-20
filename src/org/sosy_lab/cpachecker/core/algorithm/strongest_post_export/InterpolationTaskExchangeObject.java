// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import java.io.Serializable;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;

public class InterpolationTaskExchangeObject implements Serializable {

  private static final long serialVersionUID = -7646232966427949805L;
  String formulaForA;
  SSAMap ssaMapForA;
  String formulaForB;
  SSAMap ssaMapForB;

  public InterpolationTaskExchangeObject(
      String pFormulaForA, SSAMap pSsaMapForA, String pFormulaForB, SSAMap pSsaMapForB) {
    super();
    formulaForA = pFormulaForA;
    ssaMapForA = pSsaMapForA;
    formulaForB = pFormulaForB;
    ssaMapForB = pSsaMapForB;
  }

  public static long getSerialversionuid() {
    return serialVersionUID;
  }

  public String getFormulaForA() {
    return formulaForA;
  }

  public SSAMap getSsaMapForA() {
    return ssaMapForA;
  }

  public String getFormulaForB() {
    return formulaForB;
  }

  public SSAMap getSsaMapForB() {
    return ssaMapForB;
  }
}
