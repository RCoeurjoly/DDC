From Coq Require Export Arith.
Set Implicit Arguments.
Unset Strict Implicit.
Require Coq.extraction.Extraction.
Extraction Language OCaml.
Set Printing Projections.
Require Import Bool.
Require Import List.

Inductive Correctness : Type :=
| yes : Correctness
| no : Correctness
| trusted : Correctness
| idk : Correctness.

Inductive Node : Type := mkNode
                           { correctness : Correctness
                           ; children : list Node
                           }.

Definition node1 := mkNode idk nil.
Definition node2 := mkNode idk nil.
Definition node3 := mkNode trusted (node1::node2::nil).
Eval compute in correctness node3.
Lemma list_sum_ge_0 : forall l : list nat, 0 <= list_sum l.
Proof.
  intros l.
  induction l.
  simpl.
  intuition.
  simpl.
  assert (a >= 0).
  induction a.
  intuition.
  apply le_0_n.
  subst.
  induction a.
  intuition.
  intuition.
Qed.
SearchPattern (Prop).
Fixpoint and_list (l : list Prop) : Prop :=
  match l with
    nil => True
  | hd::tl => and hd (and_list tl)
  end.

Lemma and_list_true_implies_element_in_list_true: forall (A : Type) (l : list A) (element : A) (x : A -> Prop), and_list (map (fun item => x item) l) /\ In element l -> x element.
Proof.
  intros.
  intuition.
  induction l.
  + inversion H1.
  + destruct H1.
    - subst.
      inversion H0.
      exact H.
    - inversion H0. intuition.
Qed.

Eval compute in and_list (True::True::True::nil).
Check 1::nil.

Fixpoint weight (node : Node) : nat :=
  S (list_sum (map (fun child => weight child) (children node))).

Lemma weight_childfree_node_eq_1: forall n:Node, n.(children) = nil -> weight n = (S 0).
Proof.
  intros n H.
  induction n.
  simpl.
  assert (children0 = nil).
  exact H.
  rewrite H0.
  reflexivity.
Qed.

Lemma weight_gt_0: forall n:Node, 0 < weight n.
Proof.
  intros n.
  induction n.
  induction children0.
  + simpl.
    intuition.
  + simpl.
    intuition.
Qed.

Search list.
Require Import Lia.
Search nat.

Lemma node_weight_gt_sum_children_weight: forall n:Node, weight n > list_sum (map (fun child => weight child) (children n)).
Proof.
  intros n.
  induction n.
  simpl.
  induction children0.
  + simpl.
    destruct (zerop 1).
    discriminate.
    exact l.
  + simpl.
    intuition.
Qed.

SearchPattern (_ <= _).
Lemma nat_in_list_le_list_sum: forall (l:list nat) (element: nat), In element l -> element <= list_sum l.
Proof.
  intros l element H.
  induction l.
  + simpl.
    inversion H.
  + simpl.
    destruct H.
    - subst.
      apply Nat.le_add_r.
    - transitivity (list_sum l);auto.
      rewrite Nat.add_comm.
      apply Nat.le_add_r.
Qed.

Lemma child_weight_le_sum_children_weight: forall (l:list Node) (child: Node), In child l -> list_sum (map (fun child => weight child) l) >= weight child.
Proof.
  intros l child H.
  apply nat_in_list_le_list_sum.
  induction l.
  - simpl.
    inversion H.
  - simpl.
    destruct H.
    + subst.
      intuition.
    + subst.
      intuition.
Qed.

SearchPattern (_ < _ + _).
Lemma parent_weight_gt_child_weight: forall parent child:Node, In child (children parent) -> weight child < weight parent.
Proof.
  intros parent child H.
  induction parent.
  simpl.
  induction children0.
  + inversion H.
  + inversion H.
  - rewrite H0.
    intuition.
  - intuition.
    assert (weight child <= list_sum (map (fun child0 : Node => weight child0) children0)).
    apply child_weight_le_sum_children_weight.
    exact H0.
    assert (weight a > 0).
    apply weight_gt_0.
    assert (weight child < (weight a + list_sum (map (fun child0 : Node => weight child0) children0))).
    inversion H2.
    rewrite Nat.add_comm.
    apply Nat.lt_add_pos_r.
    exact H3.
    assert (weight child < S m).
    intuition.
    rewrite Nat.add_comm.
    intuition.
    intuition.
Qed.

Eval compute in idk = idk.
Scheme Equality for Correctness.
Fixpoint are_all_idk (node : Node) : Prop :=
  and (node.(correctness) = idk) (and_list (map (fun child => are_all_idk child) (children node))).
Eval compute in are_all_idk node3.

Lemma are_all_idk_implies_children_all_idk: forall n : Node, are_all_idk n -> and_list (map (fun child => are_all_idk child) (children n)).
Proof.
  intros n H.
  induction n.
  induction children0.
  + inversion H.
    simpl.
    constructor.
  + inversion H.
    simpl.
    split.
  - inversion H.
    apply H3.
  - apply H1.
Qed.

Eval compute in are_all_idk node1.
Definition node4 := mkNode idk (node1::node2::nil).
Eval compute in are_all_idk node4.

Definition is_debugging_tree (node : Node) : Prop :=
  and (node.(correctness) = no) (and_list (map (fun child => are_all_idk child) (children node))).

Lemma is_debugging_tree_true: forall node: Node, is_debugging_tree node -> and (node.(correctness) = no) (and_list (map (fun child => are_all_idk child) (children node))).
Proof.
  intros n H.
  inversion H.
  split.
  + exact H0.
  + exact H1.
Qed.
  (* Extraction pred. *)
(* Extraction is_debugging_tree. *)

Eval compute in is_debugging_tree node1.
Definition node5 := mkNode no (node1::nil).
Eval compute in is_debugging_tree node5.
(* Eval compute in list_sum (map (fun x => x + 3) (1::2::5::nil)). *)
Eval compute in weight node3.
Eval compute in is_debugging_tree node5.


Definition top_down_strategy (n : Node) : (bool * Node) :=
  match correctness n with
    no => match children n with
           nil => (false, mkNode idk nil)
         | _ => (true, hd (mkNode idk nil) (children n))
         end
  | _ => (false, mkNode idk nil)
  end.
(* Extraction top_down_strategy. *)
Eval compute in top_down_strategy node5.
Require Import Coq.Lists.List Coq.Bool.Bool.

Import Coq.Lists.List.ListNotations.

Scheme Equality for list.
Eval compute in Nat.ltb 1 2.
(* Eval compute in list_beq (Nat.leb) (1::nil) (1::nil). *)
(* Eval compute in list_beq (Nat.leb) (1::2::nil) (nil). *)
(* Fixpoint get_largest_nat_in_list_rec (largest : list nat) (l : list nat) : (list nat) := *)
(*   match l with *)
(*     nil => largest *)
(*   | head::tail => if (list_beq (nat) (Nat.leb) largest nil || (Nat.leb (hd 0 largest) head)) then get_largest_nat_in_list_rec (head::nil) tail else get_largest_nat_in_list_rec largest tail *)
(*   end. *)
(* Definition get_largest_nat_in_list (l : list nat) : (list nat) := *)
(*   get_largest_nat_in_list_rec [] l. *)
(* Eval compute in get_largest_nat_in_list_rec nil (0::1::7::8::9::3::4::5::nil). *)
(* Eval compute in get_largest_nat_in_list_rec nil (nil). *)
(* Eval compute in get_largest_nat_in_list (0::1::7::8::9::3::4::5::nil). *)
(* Eval compute in get_largest_nat_in_list (nil). *)
Check andb true.
Check weight .
(* Conseguir un typo Node -> bool *)
(* Eval compute in filter (weight Nat.eqb 2 ) (node1::nil). *)
Definition my_node_list : list Node := node1::node2::node3::node4::node5::nil.
(* Eval compute in filter (Nat.eqb weight list_max (map (fun n => weight n))) my_node_list. *)

Eval compute in list_max (nil).
(* Goal 0 * 0 = 2 -> False. *)
(* Proof. easy. *)
(* Qed. *)

Definition evaluate_node (n : Node) : Correctness :=
  no.
(* Lemma largest_of_list_is_correct: forall l: list nat, l <> nil -> get_largest_nat_in_list l <> nil. *)
(* Proof. intros l H. induction l. intuition. induction a. intuition. exact: (False_ind (0::l = [])). *)
(* Qed. *)
(* Definition get_heaviest_node (l : list Node, n : nat) : (bool * Node) := *)
(*   match l with *)
(*     nil => (false, mkNode idk nil) *)
(*     | *)
(* Definition heaviest_first_strategy (n : {n : Node | eq_true (andb (is_debugging_tree n) (Nat.ltb 0 (length (children n))))}) : Node := *)
(*   (hd (mkNode idk nil) (children (proj1_sig n))). *)
(* Eval compute in top_down_strategy node5. *)
(* Scheme Equality for Node. *)
(* Eval compute in Node_beq (mkNode no nil) (mkNode no nil). *)
Definition get_debugging_tree_from_tree (n : Node) : Node :=
  mkNode no (children n).
Require Import Program.Wf.
Lemma debugging_tree_of_tree_has_same_weight: forall n:Node, weight n = weight (get_debugging_tree_from_tree n).
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
Qed.

Lemma children_of_debugging_tree_remain_unchanged: forall n:Node, children n = children (get_debugging_tree_from_tree n).
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
Qed.

Lemma debugging_tree_root_node_is_incorrect: forall n:Node, correctness (get_debugging_tree_from_tree n) = no.
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
Qed.

Lemma debugging_tree_of_tree_with_all_children_idk_is_debugging_tree: forall n:Node, and_list (map (fun child => are_all_idk child) (children n)) -> is_debugging_tree (get_debugging_tree_from_tree n).
Proof.
  intros n H.
  simpl.
  assert (children n = children (get_debugging_tree_from_tree n)).
  apply children_of_debugging_tree_remain_unchanged.
  assert (correctness (get_debugging_tree_from_tree n) = no).
  apply debugging_tree_root_node_is_incorrect.
  assert (and_list (map (fun child : Node => are_all_idk child) (get_debugging_tree_from_tree n).(children))).
       + rewrite <- H0. exact H.
       + unfold is_debugging_tree. split.
         - exact H1.
         - exact H2.
Qed.
Require Import Lia.

Lemma debugging_tree_of_idk_tree_is_debugging_tree: forall n:Node, are_all_idk n -> is_debugging_tree (get_debugging_tree_from_tree n).
Proof.
  intros n H.
  unfold is_debugging_tree.
  split.
  + apply debugging_tree_root_node_is_incorrect.
  + assert (and_list (map (fun child : Node => are_all_idk child) n.(children))).
    apply are_all_idk_implies_children_all_idk.
  - exact H.
  - assert (children n = children (get_debugging_tree_from_tree n)).
    apply children_of_debugging_tree_remain_unchanged.
    rewrite <- H1.
    exact H0.
Qed.

Obligation Tactic := intros.

Program Fixpoint generic_debugging_algorithm (n : Node) {measure (weight n)}: Node :=
  match children n with
    nil => n
  | head::tail => generic_debugging_algorithm (get_debugging_tree_from_tree head)
  end.
Next Obligation.
  assert (In head (children n)).
  + induction (children n).
    - inversion Heq_anonymous.
    - simpl.
      left.
      injection Heq_anonymous.
      intuition.
  + assert (weight head = weight (get_debugging_tree_from_tree head)).
    - apply debugging_tree_of_tree_has_same_weight.
    - rewrite <- H0.
      apply parent_weight_gt_child_weight.
      exact H.
Qed.
Next Obligation.
  intuition.
Qed.

Obligation Tactic := intros.
Obligation Tactic := Tactics.program_simpl.
Program Fixpoint generic_debugging_algorithm_dp (n : {n: Node | is_debugging_tree n}) {measure (weight n)}: Node :=
  match children n with
    nil => n
  | head::tail => generic_debugging_algorithm_dp (get_debugging_tree_from_tree head)
  end.
Obligations of generic_debugging_algorithm_dp.
Next Obligation.
  inversion H.
  assert (are_all_idk head).
  + assert (In head (children n)).
  - induction (children n).
    inversion Heq_anonymous.
    simpl.
    left.
    injection Heq_anonymous.
    intuition.
  - apply H1.
      apply Heq_anonymous.
  intuition.
  assert (correctness head = idk).
  +
  intuition.
  assert (is_debugging_tree (n)).
  apply H.
  + split.
  - apply is_debugging_tree_true.
    intuition.
  apply debu
  apply debugging_tree_of_idk_tree_is_debugging_tree.
  assert (is_debugging_tree (n)).
  Check n.
  assert (and_list (map (fun child : Node => are_all_idk child) (proj1_sig n).(children))).
  apply generic_debugging_algorithm_dp.
  inversion n.
  assert  (are_all_idk head).
  assert (are_all_idk head).
  assert (In head (children n)).
  + induction (children n).
    - inversion Heq_anonymous.
    - simpl.
      left.
      injection Heq_anonymous.
      intuition.
  + assert (weight head = weight (get_debugging_tree_from_tree head)).
    - apply debugging_tree_of_tree_has_same_weight.
    - rewrite <- H0.
      apply parent_weight_gt_child_weight.
      exact H.
Qed.
Next Obligation.
  intuition.
Qed.



Obligation Tactic := Tactics.program_simpl.

Lemma generic_debugging_algorithm_returns_incorrect_childfree_node_when_given_debugging_tree: forall n:Node, is_debugging_tree n -> correctness (generic_debugging_algorithm n) = no.
Proof.
  intros n H.
  induction n.
  induction children0.
  - cbv. intuition. simpl.

Lemma generic_debugging_algorithm_returns_childfree_node: forall n:Node, children (generic_debugging_algorithm n) = nil.
Proof.
  intros n.
  induction n.
  induction children0.
  + simpl generic_debugging_algorithm. Tactics.program_simpl. simpl. intuition. auto. eauto.
