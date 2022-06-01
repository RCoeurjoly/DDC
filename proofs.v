Check 3.
Check 1+2.
Check True.
Check False.
Check (3=5).
Check (3, 5).
Check ((3=6)/\False).
Check nat:Set.
Check nat:Type.
Check nat -> Prop.
Check 3 <= 5.
  Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
Check (and True).
Check (and True True).
Eval compute in let f := fun x => (x + 1, x) in f 1.
Inductive Correctness : Type :=
  | yes : Correctness
  | no : Correctness
  | trusted : Correctness
| idk : Correctness.
Check yes.
Check no.
Require Import List.
Inductive Node : Type := mkNode
 { node_correctness : Correctness
 ; children : list Node
 }.
Definition node1 := mkNode idk nil.
Definition node2 := mkNode idk nil.
Definition node3 := mkNode idk (node1::node2::nil).
Set Printing Projections.
Fixpoint sum_list l : nat :=
  match l with
    nil => 0
  | n::tl => n + sum_list tl
  end.
Fixpoint weight (node : Node) : nat :=
  match node.(children) with
    nil => 1
  | children => 1 + sum_list (map (fun my_child => weight my_child) (children))
  end.
Eval compute in sum_list (map (fun x => x + 3) (1::2::5::nil)).
Eval compute in weight node1.
