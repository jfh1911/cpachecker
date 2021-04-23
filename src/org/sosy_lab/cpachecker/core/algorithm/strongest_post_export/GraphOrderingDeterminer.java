// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import com.google.common.collect.Lists;
import com.google.common.collect.Queues;
import com.google.common.graph.EndpointPair;
import com.google.common.graph.Graph;
import com.google.common.graph.Graphs;
import com.google.common.graph.Traverser;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public class GraphOrderingDeterminer<T> {
  public List<T> determineOrdering(Graph<T> graph, LogManager logger) throws CPAException {
    Set<T> loopheads = graph.nodes();
    if (Graphs.hasCycle(graph)) {
      logger.log(
          Level.WARNING,
          String.format(
              "The program contains more than one loop. Its loop structure is not acyclic:\n %s \n This is currently not supported, hence aborting!",
              graph.toString()));
      throw new CPAException("Currently, only programs with a single loop are supported!");
    }

    List<T> loopHeadsWithIndeg0 =
        loopheads.stream().filter(node -> graph.inDegree(node) == 0).collect(Collectors.toList());
    if (loopHeadsWithIndeg0.size() == 1) {
      // only a single entry point for the program, we can simply returned BFS
      Traverser<T> traverser = Traverser.forGraph(graph);
      return Lists.newArrayList(traverser.breadthFirst(loopHeadsWithIndeg0.get(0)));
    } else {
      // As we do not have a single loophead, we need to determine an ordering.
      // The algorithm used is the following:
      List<T> markedNodes = new ArrayList<>();
      Map<T, Integer> numberUnmarkedIndeg = new HashMap<>();
      // no edges are is visited
      loopheads.forEach(node -> numberUnmarkedIndeg.put(node, graph.inDegree(node)));
      ArrayDeque<EndpointPair<T>> edgesToPorcess = Queues.newArrayDeque();
      /**
       * Notes: markedNodes are the marked nodes and has the ordering of all nodes
       * numberUnmarkedIndeg saves the number of unmarked inedges per node edgesToProcess contain
       * the edges to be processed
       *
       * <p>Algorithm: 1. Mark all nodes with indeg 0 and add all outedges to queue <br>
       * 2. until queue is empty: Pick an edge A -> B from Queue. If all indeges for B are marked:
       * --> mark B and add all outedges(B) to queue Otherwise: Mark the edge as visited and
       * continue with next
       */

      // Step 1:
      markedNodes.addAll(loopHeadsWithIndeg0);
      loopHeadsWithIndeg0.stream().forEach(n -> edgesToPorcess.addAll(outEdges(graph, n)));
      // Step2:
      while (!edgesToPorcess.isEmpty()) {
        EndpointPair<T> edge = edgesToPorcess.pollFirst();

        T target = edge.nodeV();
        int numUnvisitedEdges = numberUnmarkedIndeg.get(target);
        if (numUnvisitedEdges == 1) {
          numberUnmarkedIndeg.replace(target, 0);
          markedNodes.add(target);
          edgesToPorcess.addAll(outEdges(graph, target));
        } else {
          numberUnmarkedIndeg.replace(target, numUnvisitedEdges - 1);
        }
      }
      return markedNodes;
    }
  }

  private Collection<EndpointPair<T>> outEdges(Graph<T> pGraph, T pNode) {
    return pGraph
        .incidentEdges(pNode)
        .stream()
        .filter(e -> e.nodeU().equals(pNode))
        .collect(Collectors.toList());
  }
}
