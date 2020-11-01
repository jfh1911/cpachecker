// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.valueExport;

import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

public final class ValueAnalysisExportState
    implements AbstractState, LatticeAbstractState<ValueAnalysisExportState> {

  public ValueAnalysisExportState() {}

  @Override
  public ValueAnalysisExportState join(ValueAnalysisExportState pOther)
      throws CPAException, InterruptedException {
    return pOther;
  }

  @Override
  public boolean isLessOrEqual(ValueAnalysisExportState pOther)
      throws CPAException, InterruptedException {
    return true;
  }
}
