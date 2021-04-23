// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import static org.sosy_lab.common.collect.MapsDifference.collectMapsDifferenceTo;

import com.google.common.base.Throwables;
import com.google.common.collect.Lists;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.sosy_lab.common.collect.MapsDifference;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.Triple;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class StrongestPost4Loop {

  private static final String NAMEING_PREFIX = "sp_for_loop_";

  @SuppressWarnings("resource")
  public static void serializeLoop(
      PathFormula initFormula,
      PathFormula preserveFormula,
      Collection<PathFormula> pTerminationConditions,
      FormulaManagerView pFmgr,
      LogManager pLogger,
      CFANode pLoopHead,
      String pOutdirForExport,
      Map<CFANode, PathFormula> pInvariants, Map<CFANode, Integer> nodesToLineNumber) {


    // We build for each set of Path formulae a boolean formula using conjunction
    Pair<BooleanFormula, SSAMap> path2LoooHead =
        Pair.of(initFormula.getFormula(), initFormula.getSsa());
    Pair<BooleanFormula, SSAMap> path1LoopIteration =
        Pair.of(preserveFormula.getFormula(), preserveFormula.getSsa());
    Pair<BooleanFormula, SSAMap> path2ErrorLoc = mergeAndSerialize(pTerminationConditions, pFmgr);
    List<Triple<Integer, String, SSAMap>> invariantsPresent =
        pInvariants
            .entrySet()
            .stream()
            .map(
                e ->
                    Triple.of(
                        nodesToLineNumber.get(e.getKey()),
                        pFmgr.dumpFormula(e.getValue().getFormula()).toString(),
                        e.getValue().getSsa()))
            .collect(Collectors.toList());
    StrongestPost4LoopExchangeObj exObj =
        new StrongestPost4LoopExchangeObj(
            pFmgr.dumpFormula(path2LoooHead.getFirst()).toString(), path2LoooHead.getSecond(),
            pFmgr.dumpFormula(path1LoopIteration.getFirst()).toString(),
                path1LoopIteration.getSecond(),
            pFmgr.dumpFormula(path2ErrorLoc.getFirst()).toString(), path2ErrorLoc.getSecond(), invariantsPresent);
    try {

      FileOutputStream fileOutputStream =
          new FileOutputStream(
              String.format(
                  pOutdirForExport + NAMEING_PREFIX + "%d.txt", nodesToLineNumber.get(pLoopHead)));
      ObjectOutputStream objectOutputStream = new ObjectOutputStream(fileOutputStream);
      objectOutputStream.writeObject(exObj);
      objectOutputStream.flush();
      objectOutputStream.close();
      fileOutputStream.close();
    } catch (IOException e) {
      pLogger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
    }
  }

  @SuppressWarnings("resource")
  public static Map<Integer, StrongestPost4LoopExchangeObj> deserializeAllLoops(
      String pathToExchangeDIr, LogManager pLogger) {

    Map<Integer, StrongestPost4LoopExchangeObj> loops = new HashMap<>();

    try (Stream<Path> stream = Files.list(Paths.get(pathToExchangeDIr))) {
      List<File> filesToLoad =
          stream.filter(Files::isRegularFile).map(Path::toFile).collect(Collectors.toList());

      for (File file : filesToLoad) {
        if (file.getName().startsWith(NAMEING_PREFIX)) {
          FileInputStream fileInputStream = new FileInputStream(file);
          ObjectInputStream objectInputStream = new ObjectInputStream(fileInputStream);
          StrongestPost4LoopExchangeObj l =
              (StrongestPost4LoopExchangeObj) objectInputStream.readObject();
          int linenumber =
              Integer.parseInt(
                  file.getName().substring(NAMEING_PREFIX.length(), file.getName().length() - 4));
          loops.put(linenumber, l);
          fileInputStream.close();
          objectInputStream.close();
        }
      }
    } catch (ClassNotFoundException | IOException e) {
      pLogger.log(Level.WARNING, Throwables.getStackTraceAsString(e));
    }

    return loops;
  }

  public static Pair<BooleanFormula, SSAMap> mergeAndSerialize(
      Collection<PathFormula> pPathFormulae, FormulaManagerView pFmgr) {
    PathFormula merged = merge(pPathFormulae, pFmgr);
    return Pair.of(merged.getFormula(), merged.getSsa());
  }

  public static PathFormula merge(Collection<PathFormula> pPathFormulae, FormulaManagerView pFmgr) {
    BooleanFormula formula2Loop =
        pFmgr
            .getBooleanFormulaManager()
            .and(pPathFormulae.stream().map(p -> p.getFormula()).collect(Collectors.toList()));

    SSAMap map = SSAMap.emptySSAMap();
    final List<MapsDifference.Entry<String, Integer>> symbolDifferences = new ArrayList<>();
    for (SSAMap curMap : pPathFormulae.stream().map(p -> p.getSsa()).collect(Collectors.toList())) {
      map = SSAMap.merge(curMap, map, collectMapsDifferenceTo(symbolDifferences));
    }
    int maxIndexAt = 0;
    ArrayList<PathFormula> tempList = Lists.newArrayList(pPathFormulae);
    for (int i = 1; i < pPathFormulae.size(); i++) {
      if (tempList.get(i).getLength() > tempList.get(maxIndexAt).getLength()) {
        maxIndexAt = i;
      }
    }

    return new PathFormula(
        formula2Loop,
        map,
        tempList.get(maxIndexAt).getPointerTargetSet(),
        tempList.get(maxIndexAt).getLength());
  }





}
