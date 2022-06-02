Set Printing Projections.
Require Import Bool.
Require Import List.
Inductive Correctness : Type :=
  | yes : Correctness
  | no : Correctness
  | trusted : Correctness
| idk : Correctness.
Example yes_is_yes : yes = yes.
Proof. reflexivity.
Qed.
Example no_is_no : no = no.
Proof. reflexivity.
Qed.
Example trusted_is_trusted : trusted = trusted.
Proof. reflexivity.
Qed.
Example idk_is_idk : idk = idk.
Proof. reflexivity.
Qed.

Inductive Node : Type := mkNode
 { correctness : Correctness
 ; children : list Node
 }.
(* Inductive DebuggingTree : Type := *)
(*     right_neutral : forall x, x * 1 = x  *)
Definition node1 := mkNode idk nil.
Definition node2 := mkNode idk nil.
Definition node3 := mkNode trusted (node1::node2::nil).
Eval compute in correctness node3.
Fixpoint sum_list (l : list nat) : nat :=
  match l with
    nil => 0
  | n::tl => n + sum_list tl
  end.
Fixpoint and_list (l : list bool) : bool :=
  match l with
    nil => true
  | n::tl => andb n (and_list tl)
  end.
Eval compute in and_list (true::true::true::nil).
Search bool.
Check 1::nil.
Fixpoint weight (node : Node) : nat :=
  match node.(children) with
    nil => 1
  | children => 1 + sum_list (map (fun child => weight child) (children))
  end.
Lemma commutativity : forall a b:Prop, a/\b -> b/\a.
Proof.
  intros a b H. split. destruct H as [H1 H2]. exact H2. intuition.
  Qed.
Lemma weight_childfree_node_eq_1: forall n:Node, n.(children) = nil -> weight n = 1.
Proof.
  - intros n H. induction n. simpl. assert (children0 = nil). apply H. subst. reflexivity.
Qed.
Lemma weight_ge_1: forall n:Node, weight n > 0.
Proof. intros. induction n. induction children0.
Eval compute in idk = idk.
Fixpoint are_all_idk (node : Node) : bool :=
  match node.(children) with
    nil => eqb (node.(correctness) idk)
  | children => eqb node.(correctness) (andb idk (and_list (map (fun child => are_all_idk child) (children))))
  end.
Check are_all_idk node3.
Eval compute in sum_list (map (fun x => x + 3) (1::2::5::nil)).
Eval compute in weight node3.
