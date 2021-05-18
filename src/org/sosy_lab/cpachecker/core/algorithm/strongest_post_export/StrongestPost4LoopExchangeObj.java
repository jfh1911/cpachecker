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
import org.sosy_lab.cpachecker.util.Triple;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;

/**
 * THis class is sued to be exhanged via a json format. Hence, it only contains simple datatypes
 * (strings for formulas and variables)
 */
public class StrongestPost4LoopExchangeObj implements Serializable {

  private final String path2Loophead;
  private final String path1LoopIteration;
  private final String path2ErrorLocation;
  private final SSAMap ssa4Path2LoopHead;
  private final SSAMap ssa4path1LoopIteration;
  private final SSAMap ssa4path2ErrorLocation;
  private final SSAMap ssa4Loophead;
  private final List<Triple<Integer, String, SSAMap>> invariantsPresent;

  public StrongestPost4LoopExchangeObj(
      String pPath2Loophead,
      SSAMap pSsa4Path2LoopHead,
      SSAMap pSsaMapAtLoophead,
      String pPath1LoopIteration,
      SSAMap pSsa4path1LoopIteration,
      String pPath2ErrorLocation,
      SSAMap pSsaM4path2ErrorLocation,
      List<Triple<Integer, String, SSAMap>> pInvariantsPresent) {
    path2Loophead = pPath2Loophead;
    ssa4Path2LoopHead = pSsa4Path2LoopHead;

    path1LoopIteration = pPath1LoopIteration;
    ssa4path1LoopIteration = pSsa4path1LoopIteration;
    path2ErrorLocation = pPath2ErrorLocation;
    ssa4path2ErrorLocation = pSsaM4path2ErrorLocation;
    this.invariantsPresent = pInvariantsPresent;
    this.ssa4Loophead = pSsaMapAtLoophead;
  }

  private static final long serialVersionUID = -2430230516652717470L;



  public String getPath2Loophead() {
    return path2Loophead;
  }

  public String getPath1LoopIteration() {
    return path1LoopIteration;
  }

  public String getPath2ErrorLocation() {
    return path2ErrorLocation;
  }

  public SSAMap getSsa4Loophead() {
    return ssa4Loophead;
  }

  public SSAMap getSsa4Path2LoopHead() {
    return ssa4Path2LoopHead;
  }

  public SSAMap getSsa4path1LoopIteration() {
    return ssa4path1LoopIteration;
  }

  public SSAMap getSsa4path2ErrorLocation() {
    return ssa4path2ErrorLocation;
  }

  public static long getSerialversionuid() {
    return serialVersionUID;
  }

  public List<Triple<Integer, String, SSAMap>> getInvariantsPresent() {
    return invariantsPresent;
  }



  @Override
  public int hashCode() {
    return Objects.hash(
        invariantsPresent,
        path1LoopIteration,
        path2ErrorLocation,
        path2Loophead,
        ssa4Path2LoopHead,
        ssa4Loophead,
        ssa4path1LoopIteration,
        ssa4path2ErrorLocation);
  }




  @Override
  public String toString() {
    return "StrongestPost4LoopExchangeObj [path2Loophead="
        + path2Loophead
        + ", ssa4Path2LoopHead="
        + ssa4Path2LoopHead
        + ",\n\n path1LoopIteration="
        + path1LoopIteration
        + ", ssa4path1LoopIteration="
        + ssa4path1LoopIteration
        + ",\n\n path2ErrorLocation="
        + path2ErrorLocation
        + ", ssa4path2ErrorLocation="
        + ssa4path2ErrorLocation
        + "\n\n, ssa4Loophead="
        + ssa4Loophead
        + ",\n invariantsPresent="
        + invariantsPresent
        + "]\n";
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof StrongestPost4LoopExchangeObj)) {
      return false;
    }
    StrongestPost4LoopExchangeObj other = (StrongestPost4LoopExchangeObj) obj;
    return Objects.equals(invariantsPresent, other.invariantsPresent)
        && Objects.equals(path1LoopIteration, other.path1LoopIteration)
        && Objects.equals(path2ErrorLocation, other.path2ErrorLocation)
        && Objects.equals(path2Loophead, other.path2Loophead)
        && Objects.equals(ssa4Path2LoopHead, other.ssa4Path2LoopHead)
        && Objects.equals(ssa4Loophead, other.ssa4Loophead)
        && Objects.equals(ssa4path1LoopIteration, other.ssa4path1LoopIteration)
        && Objects.equals(ssa4path2ErrorLocation, other.ssa4path2ErrorLocation);
  }
}
