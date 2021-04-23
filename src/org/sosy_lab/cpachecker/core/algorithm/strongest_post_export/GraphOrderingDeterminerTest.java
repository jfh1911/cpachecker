// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.graph.GraphBuilder;
import com.google.common.graph.MutableGraph;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class GraphOrderingDeterminerTest {

  /**
   * Build the graph: (drection is down)
   *
   * <p>1 2<br>
   * | / |<br>
   * 3 4<br>
   * \ /<br>
   * 5<br>
   *
   * @throws CPAException if the structure is cyclic
   */
  @Test
  public void test() throws CPAException {

    MutableGraph<Integer> graph = GraphBuilder.directed().build();
    graph.putEdge(1, 3);
    graph.putEdge(2, 3);
    graph.putEdge(2, 4);
    graph.putEdge(3, 5);
    graph.putEdge(4, 5);

    GraphOrderingDeterminer<Integer> determiner = new GraphOrderingDeterminer<>();
    List<Integer> order = determiner.determineOrdering(graph, LogManager.createTestLogManager());
    assertThat(order).containsExactly(1, 2, 3, 4, 5);
    assertThat(order.get(0)).isAnyOf(1, 2);
    assertThat(order.get(1)).isAnyOf(1, 2);
    assertThat(order.get(2)).isAnyOf(3, 4);
    assertThat(order.get(3)).isAnyOf(3, 4);
    assertThat(order.get(4)).isEqualTo(5);
  }
}
