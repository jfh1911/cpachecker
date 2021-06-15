// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import java.io.Serializable;
import java.util.Objects;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;

/**
 * THis class is sued to be exhanged via a json format. Hence, it only contains simple datatypes
 * (strings for formulas and variables)
 */
public class TerminationConditionExchangeObj implements Serializable {

  private final String assertion;
  private final String path2Assertion;
  private final SSAMap ssa4Path2Assertion;
  private final SSAMap ssa4Assertion;

  public TerminationConditionExchangeObj(
      String pPath2Assertion,
      String pAssertion,
      SSAMap pSsa4Path2Assertion,
      SSAMap pSsa4Assertion) {
    super();
    assertion = pAssertion;
    path2Assertion = pPath2Assertion;
    ssa4Path2Assertion = pSsa4Path2Assertion;
    ssa4Assertion = pSsa4Assertion;
  }

  private static final long serialVersionUID = -2430230516652717410L;

  public String getAssertion() {
    return assertion;
  }

  public String getPath2Assertion() {
    return path2Assertion;
  }

  public SSAMap getSsa4Path2Assertion() {
    return ssa4Path2Assertion;
  }

  public SSAMap getSsa4Assertion() {
    return ssa4Assertion;
  }

  public static long getSerialversionuid() {
    return serialVersionUID;
  }

  @Override
  public int hashCode() {
    return Objects.hash(assertion, path2Assertion, ssa4Assertion, ssa4Path2Assertion);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof TerminationConditionExchangeObj)) {
      return false;
    }
    TerminationConditionExchangeObj other = (TerminationConditionExchangeObj) obj;
    return Objects.equals(assertion, other.assertion)
        && Objects.equals(path2Assertion, other.path2Assertion)
        && Objects.equals(ssa4Assertion, other.ssa4Assertion)
        && Objects.equals(ssa4Path2Assertion, other.ssa4Path2Assertion);
  }

  @Override
  public String toString() {
    return "TerminationConditionExchangeObj [assertion="
        + assertion
        + ", path2Assertion="
        + path2Assertion
        + ", ssa4Path2Assertion="
        + ssa4Path2Assertion
        + ", ssa4Assertion="
        + ssa4Assertion
        + "]";
  }




}
