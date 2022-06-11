From Coq Require Export Arith.
Require Import Program.Wf.

Program Fixpoint trivial_program_fixpoint (n : nat) {measure n}: nat :=
  match n with
    0 => 0
  | m => m
  end.
Check trivial_program_fixpoint.

Obligation Tactic := intros.

Program Fixpoint trivial_program_fixpoint2 (n : nat) {measure n}: nat :=
  match n with
    0 => 0
  | m => m
  end.
Next Obligation.
  intuition. discriminate.
Qed.
Check trivial_program_fixpoint2.
