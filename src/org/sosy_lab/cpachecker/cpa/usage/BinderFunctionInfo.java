/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2012  Dirk Beyer
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
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.usage;

import static com.google.common.collect.FluentIterable.from;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.logging.Level;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cpa.usage.UsageInfo.Access;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.identifiers.AbstractIdentifier;
import org.sosy_lab.cpachecker.util.identifiers.Identifiers;

/** Information about special functions like sdlFirst() and sdlNext(); */
public class BinderFunctionInfo {

  private static class LinkerInfo {
    private final int num;
    private final int dereference;

    LinkerInfo(int p, int d) {
      num = p;
      dereference = d;
    }
  }

  private final ImmutableList<Pair<Access, Integer>> parameterInfo;
  /*
   * 0 - before equal,
   * 1 - first parameter, etc..
   */
  private final Pair<LinkerInfo, LinkerInfo> linkInfo;

  @SuppressWarnings("deprecation")
  BinderFunctionInfo(String name, Configuration pConfig, LogManager pLogger) {
    try {
      String line = pConfig.getProperty(name + ".pInfo");
      Preconditions.checkNotNull(line);
      line = line.replaceAll("\\s", "");

      parameterInfo =
          from(Splitter.on(",").splitToList(line))
              .transform(s -> Splitter.on(":").splitToList(s))
              .transform(s -> Pair.of(Access.valueOf(s.get(0).toUpperCase()), getNumOrDefault(s)))
              .toList();

      line = pConfig.getProperty(name + ".linkInfo");

      if (line != null) {
        List<String> options;
        List<String> pOption;
        line = line.replaceAll("\\s", "");
        options = Splitter.on(",").splitToList(line);
        assert options.size() == 2;
        LinkerInfo[] lInfo = new LinkerInfo[2];
        for (int i = 0; i < 2; i++) {
          pOption = Splitter.on(":").splitToList(options.get(i));
          int dereference = getNumOrDefault(pOption);
          lInfo[i] = new LinkerInfo(Integer.parseInt(pOption.get(0)), dereference);
        }
        linkInfo = Pair.of(lInfo[0], lInfo[1]);
      } else {
        linkInfo = null;
      }
    } catch (NumberFormatException e) {
      pLogger.log(Level.WARNING, "No information about parameters in " + name + " function");
      throw e;
    }
  }

  public boolean shouldBeLinked() {
    return linkInfo != null;
  }

  public AbstractIdentifier constructFirstIdentifier(
      final CExpression left, final List<CExpression> params, String currentFunction) {
    return constructIdentifier(linkInfo.getFirst(), left, params, currentFunction);
  }

  public AbstractIdentifier constructSecondIdentifier(
      final CExpression left, final List<CExpression> params, String currentFunction) {
    return constructIdentifier(linkInfo.getSecond(), left, params, currentFunction);
  }

  private AbstractIdentifier constructIdentifier(
      final LinkerInfo info,
      final CExpression left,
      final List<CExpression> params,
      String currentFunction) {

    CExpression expr;

    if (info.num == 0 && left != null) {
      expr = left;
    } else if (info.num > 0) {
      expr = params.get(info.num - 1);
    } else {
      /* f.e. sdlGetFirst(), which is used for deleting element
       * we don't link, but it isn't an error
       */
      return null;
    }
    return Identifiers.createIdentifier(expr, info.dereference, currentFunction);
  }

  public AbstractIdentifier createParamenterIdentifier(
      final CExpression param, int num, String currentFunction) {

    return Identifiers.createIdentifier(param, parameterInfo.get(num).getSecond(), currentFunction);
  }

  public Access getBindedAccess(int num) {
    return parameterInfo.get(num).getFirst();
  }

  private int getNumOrDefault(List<String> list) {
    if (list.size() == 1) {
      return 0;
    } else {
      return Integer.parseInt(list.get(1));
    }
  }
}
