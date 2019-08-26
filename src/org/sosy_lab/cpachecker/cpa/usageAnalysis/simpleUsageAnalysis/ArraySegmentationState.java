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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.java.JBinaryExpression;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Graphable;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;

public class ArraySegmentationState<T extends LatticeAbstractState<T>> implements Serializable,
    LatticeAbstractState<ArraySegmentationState<T>>, AbstractState, Graphable {

  private static final long serialVersionUID = 85908607562101422L;
  private List<ArraySegment<T>> segments;
  private SegmentUnifier<T> unifier;
  protected T tBottom, tTop;
  protected BinaryOperator<T> tMeet;
  protected List<AIdExpression> tLisOfArrayVariables;
  protected AIdExpression tArray;
  private T tEmptyElement;
  private LogManager logger;

  /**
   *
   * @param pSegments
   * @param pTBottom
   * @param pTTop
   * @param pEmptyElement an element that is not part of the lattice. It is used to avoid uses of
   *        null!
   * @param pTMeet
   * @param pLisOfArrayVariables
   * @param pArray
   * @param pLogger
   */
  public ArraySegmentationState(
      List<ArraySegment<T>> pSegments,
      T pTBottom,
      T pTTop,
      T pEmptyElement,
      BinaryOperator<T> pTMeet,
      List<AIdExpression> pLisOfArrayVariables,
      AIdExpression pArray,
      LogManager pLogger) {
    super();
    segments = pSegments;
    // Check if the segment chain is correctly ordered
    for (int i = 0; i < segments.size() - 1; i++) {
      if (!segments.get(i).getNextSegment().equals(segments.get(i + 1))) {
        throw new IllegalArgumentException(
            "The succesor of the " + i + "th element is not correctly set!");
      }
      if (segments.size() > 0
          && !(segments.get(segments.size() - 1).getNextSegment() instanceof FinalSegSymbol)) {
        throw new IllegalArgumentException(
            "The nextElement of the last element does not contain the specific FINAL_SEG_SYMBOL");
      }
    }
    unifier = new SegmentUnifier<>();
    tBottom = pTBottom;
    tTop = pTTop;
    tMeet = pTMeet;
    tEmptyElement = pEmptyElement;
    tLisOfArrayVariables = pLisOfArrayVariables;
    tArray = pArray;
    logger = pLogger;
  }

  @Override
  public ArraySegmentationState<T> join(ArraySegmentationState<T> pOther)
      throws CPAException, InterruptedException {
    if (!pOther.getClass().equals(this.getClass())) {
      throw new CPAException("The join cannot be applied for two differently initalized generics");
    }

    logger
        .log(Level.FINE, "Merging the elements" + this.toDOTLabel() + " - " + pOther.toDOTLabel());
    Pair<ArraySegmentationState<T>, ArraySegmentationState<T>> unifiedSegs =
        unifier.unifyMerge(this, pOther, tBottom, tBottom);

    // Some corner cases for error and unreachable segmentations
    if (unifiedSegs.getFirst() instanceof UnreachableArraySegmentation) {
      return unifiedSegs.getSecond();
    } else if (unifiedSegs.getSecond() instanceof UnreachableArraySegmentation) {
      return unifiedSegs.getFirst();
    } else if (unifiedSegs.getSecond() instanceof ErrorSegmentation) {
      return unifiedSegs.getSecond();
    } else if (unifiedSegs.getFirst() instanceof ErrorSegmentation) {
      return unifiedSegs.getFirst();
    }

    List<ArraySegment<T>> res = new ArrayList<>();
    List<ArraySegment<T>> firstSegs = unifiedSegs.getFirst().getSegments();
    List<ArraySegment<T>> secondSegs = unifiedSegs.getSecond().getSegments();

    if (firstSegs.isEmpty()) {
      throw new CPAException("The unification has fail!");
    }

    ArraySegment<T> firstSeg = firstSegs.get(firstSegs.size() - 1);
    ArraySegment<T> secondSeg = secondSegs.get(secondSegs.size() - 1);

    // Since the list needs to be concatenated, we will start backwards (last element has a specific
    // next element). The last array segment only contains a segment bound, hence the analysis
    // information are set to null (they are null anyway), same for isPotentiallyEmpty (which is
    // false)

    ArraySegment<T> current =
        new ArraySegment<>(
            firstSeg.getSegmentBound(),
            firstSeg.getAnalysisInformation().join(secondSeg.getAnalysisInformation()),
            false,
            new FinalSegSymbol<T>(this.tEmptyElement));
    res.add(0, current);

    for (int i = firstSegs.size() - 2; i >= 0; i--) {
      firstSeg = firstSegs.get(i);
      secondSeg = secondSegs.get(i);

      ArraySegment<T> last = current;
      current =
          new ArraySegment<>(
              firstSeg.getSegmentBound(),
              firstSeg.getAnalysisInformation().join(secondSeg.getAnalysisInformation()),
              firstSeg.isPotentiallyEmpty() | secondSeg.isPotentiallyEmpty(),
              last);
      res.add(0, current);
    }
    return new ArraySegmentationState<>(
        res,
        this.tBottom,
        this.tTop,
        this.tEmptyElement,
        this.tMeet,
        this.tLisOfArrayVariables,
        this.tArray,
        logger);
  }

  @Override
  public boolean isLessOrEqual(ArraySegmentationState<T> pOther)
      throws CPAException, InterruptedException {
    if (!pOther.getClass().equals(this.getClass())) {
      throw new CPAException(
          "The comparison  cannot be applied for two differently initalized generics");
    }

    Pair<ArraySegmentationState<T>, ArraySegmentationState<T>> unifiedSegs =
        unifier.unifyCompare(this, pOther, tBottom, tBottom, tMeet);

    // Come corner cases for error and unreachable segmentations
    if (unifiedSegs.getFirst() instanceof UnreachableArraySegmentation) {
      return true;
    } else if (unifiedSegs.getSecond() instanceof UnreachableArraySegmentation) {
      return false;// since the first is not unreachable
    } else if (unifiedSegs.getSecond() instanceof ErrorSegmentation) {
      return true;
    } else if (unifiedSegs.getFirst() instanceof ErrorSegmentation) {
      return false; // since second is not error
    }

    List<ArraySegment<T>> firstSegs = unifiedSegs.getFirst().getSegments();
    List<ArraySegment<T>> secondSegs = unifiedSegs.getSecond().getSegments();

    if (firstSegs.isEmpty()) {
      throw new CPAException("The unification has fail!");
    }

    for (int i = 0; i < firstSegs.size(); i++) {
      ArraySegment<T> firstSeg = firstSegs.get(i);
      ArraySegment<T> secondSeg = secondSegs.get(i);
      if (!firstSeg.getAnalysisInformation().isLessOrEqual(secondSeg.getAnalysisInformation())) {
        return false;
      }

      // Since ? (=true) < |_| (=false), ?_i !<= ?_i', iff ?_i = false & ß_i' = true
      if (!firstSeg.isPotentiallyEmpty() && secondSeg.isPotentiallyEmpty()) {
        return false;
      }

    }
    return true;
  }

  public boolean addSegment(ArraySegment<T> toAdd, ArraySegment<T> after) {
    if (!segments.contains(after)) {
      return false;
    }
    int posToAdd = segments.indexOf(after) + 1;
    ArraySegment<T> cur = segments.get((posToAdd - 1));
    toAdd.setNextSegment((cur).getNextSegment());
    cur.setNextSegment(toAdd);
    segments.add(posToAdd, toAdd);
    return true;
  }

  /**
   * Computes the set of all expressions, that are present in the segment bounds, where collecting
   * is started at "startOFCollection". THe function is mainly used during unification
   *
   * @param startOfCollection the element to start collection
   * @return all expressions
   */
  public Set<AExpression> getSegmentBounds(ArraySegment<T> startOfCollection) {
    Set<AExpression> result = new HashSet<>();
    if (segments.contains(startOfCollection)) {
      ArraySegment<T> cur = startOfCollection;
      for (int i = segments.indexOf(startOfCollection); i < segments.size(); i++) {
        result.addAll(cur.getSegmentBound());
        cur = cur.getNextSegment();
      }
    }
    return result;
  }

  public ArraySegmentationState<T> strengthn(Collection<AExpression> eColl) {
    for (AExpression e : eColl) {
      if (e instanceof CBinaryExpression || e instanceof JBinaryExpression) {
        this.segments.parallelStream().forEach(s -> s.strengthn(e));
      }
    }
    return this;
  }

  public List<ArraySegment<T>> getSegments() {
    return segments;
  }

  public void setSegments(List<ArraySegment<T>> pSegments) {
    segments = pSegments;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((segments == null) ? 0 : segments.hashCode());
    result = prime * result + ((tBottom == null) ? 0 : tBottom.hashCode());
    result = prime * result + ((tMeet == null) ? 0 : tMeet.hashCode());
    result = prime * result + ((tTop == null) ? 0 : tTop.hashCode());
    return result;
  }

  // Creates a Deep copy of the object. In the lower level (ArraySegment), only the lists but not
  // the list content is modified. This does not cause problems, since the arithmetic expressions
  // are
  // not changed during unify!
  @Override
  public ArraySegmentationState<T> clone() {
    List<ArraySegment<T>> copiedElements = new ArrayList<>(segments.size());
    this.segments.forEach(s -> copiedElements.add(s.clone()));
    return new ArraySegmentationState<>(
        this.unifier.conc(copiedElements, tEmptyElement),
        this.tBottom,
        this.tTop,
        this.tEmptyElement,
        this.tMeet,
        this.tLisOfArrayVariables,
        this.tArray,
        logger);
  }

  /**
   * This implementation checks syntactical equality. For a formal definition see Analyzing Data
   * Usage in Array Programs, page 30 By Jan Haltermann
   */
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
    ArraySegmentationState<T> other = (ArraySegmentationState<T>) obj;
    if (segments == null) {
      if (other.segments != null) {
        return false;
      }
    }
    if (other.getSegments().size() != this.segments.size()) {
      return false;
    } else if (!this.segments.containsAll(other.getSegments())
        || !other.getSegments().containsAll(this.segments)) {
      return false;
    }
    if (tBottom == null) {
      if (other.tBottom != null) {
        return false;
      }
    } else if (!tBottom.equals(other.tBottom)) {
      return false;
    }
    if (tMeet == null) {
      if (other.tMeet != null) {
        return false;
      }
    } else if (!tMeet.equals(other.tMeet)) {
      return false;
    }
    if (tTop == null) {
      if (other.tTop != null) {
        return false;
      }
    } else if (!tTop.equals(other.tTop)) {
      return false;
    }
    return true;
  }

  public T gettBottom() {
    return tBottom;
  }

  public void settBottom(T pTBottom) {
    tBottom = pTBottom;
  }

  public T gettTop() {
    return tTop;
  }

  public void settTop(T pTTop) {
    tTop = pTTop;
  }

  public BinaryOperator<T> gettMeet() {
    return tMeet;
  }

  public void settMeet(BinaryOperator<T> pTMeet) {
    tMeet = pTMeet;
  }

  public List<AIdExpression> gettLisOfArrayVariables() {
    return tLisOfArrayVariables;
  }

  public void settLisOfArrayVariables(List<AIdExpression> pTLisOfArrayVariables) {
    tLisOfArrayVariables = pTLisOfArrayVariables;
  }

  public AIdExpression gettArray() {
    return tArray;
  }

  public void settArray(AIdExpression pTArray) {
    tArray = pTArray;
  }

  public T gettEmptyElement() {
    return tEmptyElement;
  }

  public void settEmptyElement(T pTEmptyElement) {
    tEmptyElement = pTEmptyElement;
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    this.segments.stream().forEachOrdered(s -> builder.append(s.toString()));
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

  /**
   * Iterate through all segments and check, if a segment has no expressions in its bound. in this
   * case, remove the segment bound and merge the information with the prior segment
   *
   * @throws InterruptedException
   * @throws CPAException
   */
  public void mergeSegmentsWithEmptySegmentBounds() throws CPAException, InterruptedException {
    if (this.getSegments().isEmpty()) {
      throw new CPAException(
          "The segmentation "
              + this.toString()
              + " does not conaint a single segmentation, hence the computation is aborted");
    }

    // By assumption, the segmentation contains at least one segment!
    ArraySegment<T> prevSegment = this.segments.get(0);
    List<ArraySegment<T>> newSegments = new ArrayList<>();

    for (int i = 1; i < this.segments.size(); i++) {
      ArraySegment<T> segment = segments.get(i);
      if (segment.getSegmentBound().isEmpty()) {
        prevSegment.setAnalysisInformation(
            prevSegment.getAnalysisInformation().join(segment.getAnalysisInformation()));
        prevSegment
            .setPotentiallyEmpty(prevSegment.isPotentiallyEmpty() || segment.isPotentiallyEmpty());
        prevSegment.setNextSegment(segment.getNextSegment());
      } else {
        // The segment bound is not empty, hence the previous segment can be stored, since it will
        // not be modified anymore
        newSegments.add(prevSegment);
        prevSegment = segment;
      }
    }
    newSegments.add(prevSegment);
    this.segments = newSegments;
  }

  public int getSegBoundContainingExpr(CExpression pSubscriptExpr) {
    for (int i = 0; i < this.segments.size(); i++) {
      if (segments.get(i).getSegmentBound().contains(pSubscriptExpr)) {
        return i;
      }
    }
    return -1;
  }

  public LogManager getLogger() {
    return logger;
  }

}
