// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import com.google.common.base.Throwables;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.sosy_lab.common.log.LogManager;

public class Interpolation4Loop {

  private static final String NAMEING_PREFIX_Interpolation = "interpol_for_loop_";

  @SuppressWarnings("resource")
  public static Map<Integer, InterpolationTaskExchangeObject> deserializeAllLoops(
      String pathToExchangeDIr, LogManager pLogger) {

    Map<Integer, InterpolationTaskExchangeObject> loops = new HashMap<>();

    try (Stream<Path> stream = Files.list(Paths.get(pathToExchangeDIr))) {
      List<File> filesToLoad =
          stream.filter(Files::isRegularFile).map(Path::toFile).collect(Collectors.toList());

      for (File file : filesToLoad) {
        if (file.getName().startsWith(NAMEING_PREFIX_Interpolation)) {
          FileInputStream fileInputStream = new FileInputStream(file);
          ObjectInputStream objectInputStream = new ObjectInputStream(fileInputStream);
          InterpolationTaskExchangeObject l =
              (InterpolationTaskExchangeObject) objectInputStream.readObject();
          int linenumber =
              Integer.parseInt(
                  file.getName()
                      .substring(
                          NAMEING_PREFIX_Interpolation.length(), file.getName().length() - 4));
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
}
