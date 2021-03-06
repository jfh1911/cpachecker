// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 1 "lock-loop.c"
int L  =    0;
#line 3 "lock-loop.c"
void lock(void) 
{ 

  {
#line 4
  if (L != 0) {
    ERROR: 
    goto ERROR;
  } else {

  }
#line 8
  L = L + 1;
#line 9
  return;
}
}
#line 11 "lock-loop.c"
void unlock(void) 
{ 

  {
#line 12
  if (L != 1) {
    ERROR: 
    goto ERROR;
  } else {

  }
#line 16
  L = L - 1;
#line 17
  return;
}
}
#line 19 "lock-loop.c"
int main(void) 
{ int old ;
  int new ;
  int undet ;

  {
  {
#line 22
  while (1) {
    while_0_continue: /* CIL Label */ ;
    {
#line 23
    lock();
#line 24
    old = new;
    }
#line 25
    if (undet) {
      {
#line 26
      unlock();
#line 27
      new = new + 1;
      }
    } else {

    }
#line 22
    if (new != old) {

    } else {
      goto while_0_break;
    }
  }
  while_0_break: /* CIL Label */ ;
  }
#line 30
  return (0);
}
}
