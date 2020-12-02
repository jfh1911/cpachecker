// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.smg.graphs.object.generic;

import org.sosy_lab.cpachecker.cpa.smg.graphs.SMG;

public interface SMGGenericAbstractionCandidate {

  int getScore();

  SMG execute(SMG pSMG);

  boolean isUnknown();
}