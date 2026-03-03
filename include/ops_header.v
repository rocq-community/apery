Require Import BinInt.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import tactics rat_of_Z bigopz shift.
Require punk.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
