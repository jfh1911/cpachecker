// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

public class IfStatement4_true_assert {

  public static void main(String[] args) {
    int n1 = 1;
    int n2 = 1;
    int n3 = 2;

    if (n1 == n2) {
      // branch entered
      if (n1 != n3) {
        // branch entered
        n3 = 1;
      }

      if (n1 == n3) {
        // branch entered
        n1 = n1 + n2 + n3; // n1 = 3
      } else {
        assert (false); // not reached
      }

      if (n1 == n1 + n2) {
        assert (false); // not reached

      } else if (n1 == 2 * n2 + n3) {
        // branch entered
        if ((n3 != n2)) // n3 == n1 = true
        {
          assert (false); // not reached
        }
      }
    }
  }
}
