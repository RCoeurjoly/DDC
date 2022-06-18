From Coq Require Export Arith.
Set Implicit Arguments.
Unset Strict Implicit.
Require Coq.extraction.Extraction.
Extraction Language OCaml.
Set Printing Projections.
Require Import Bool.
Require Import List.
Require Import String.

Inductive Correctness : Type :=
| yes : Correctness
| no : Correctness
| trusted : Correctness
| idk : Correctness.

Inductive ComparableNode : Type :=
  mkComparableNode
    {
      ComparableNodeContent : string
    ; ComparableNodeChildren : list ComparableNode
    }.

Inductive Node : Type :=
  mkNode
    {
      content : string
    ;correctness : Correctness
    ; children : list Node
    }.

Fixpoint get_comparable_node_from_node (n: Node) : ComparableNode :=
  mkComparableNode (content n) (map (fun child => get_comparable_node_from_node child) (children n)).

Lemma comparable_node_content_eq_to_node_content : forall n:Node, content n = ComparableNodeContent (get_comparable_node_from_node n).
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
Qed.

Fixpoint or_list (l : list Prop) : Prop :=
  match l with
    nil => False
  | hd::tl => or hd (or_list tl)
  end.

Fixpoint is_node_in_tree (c : string) (m : Node) : Prop :=
  or (c = content m) (or_list (map (fun child => is_node_in_tree c child) (children m))).

Lemma nodes_with_same_content : forall n1 n2 tree: Node, content n1 = content n2 /\ is_node_in_tree (content n1) tree -> is_node_in_tree (content n2) tree.
Proof.
  intros n1 n2 tree H.
  intuition.
  rewrite <- H0.
  exact H1.
Qed.

Lemma node_is_in_itself : forall n : Node, is_node_in_tree (content n) n.
Proof.
  intros n.
  induction n.
  simpl.
  left.
  + reflexivity.
Qed.

Lemma head_of_non_empty_children_is_in_parent : forall parent child : Node, (children parent) <> nil /\ hd (mkNode "I don't exist"%string idk nil) (children parent) = child -> is_node_in_tree (content child) parent.
Proof.
  intros parent child H.
  induction parent.
  simpl.
  intuition.
  right.
  induction children0.
  + simpl.
    intuition.
  + assert (a = child).
    intuition.
    simpl.
    left.
    rewrite H.
    apply node_is_in_itself.
Qed.

Lemma child_node_is_in_parent : forall parent child : Node, In child (children parent) -> is_node_in_tree (content child) parent.
Proof.
  intros parent child H.
  induction parent.
  simpl.
  right.
  induction children0.
  + inversion H.
  + assert (In child
        {|
          content := content0;
          correctness := correctness0;
          children := a :: children0
        |}.(children) -> child = a \/ (In child
        {|
          content := content0;
          correctness := correctness0;
          children := children0
        |}.(children))).
    simpl.
    intuition.
    intuition.
    rewrite <- H0.
    simpl.
    left.
    apply node_is_in_itself.
    simpl.
    right.
    exact H1.
Qed.

Definition node1 := mkNode "node1"%string idk nil.
Definition node2 := mkNode "node2"%string idk nil.
Definition node3 := mkNode "node3"%string trusted (node1::node2::nil).
Eval compute in get_comparable_node_from_node node1 = get_comparable_node_from_node node1.
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

Fixpoint weight (node : Node) : nat :=
  match children node with
    nil => 1
  | children => S (list_sum (map (fun child => weight child) (children)))
  end.

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

Fixpoint are_all_idk (node : Node) : Prop :=
  and (node.(correctness) = idk) (and_list (map (fun child => are_all_idk child) (children node))).

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
Definition node4 := mkNode "node4"%string idk (node1::node2::nil).
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
Definition node5 := mkNode "node5"%string no (node1::nil).
Eval compute in is_debugging_tree node5.
(* Eval compute in list_sum (map (fun x => x + 3) (1::2::5::nil)). *)
Eval compute in weight node3.
Eval compute in is_debugging_tree node5.


(* Definition top_down_strategy (n : Node) : (bool * Node) := *)
(*   match correctness n with *)
(*     no => match children n with *)
(*            nil => (false, mkNode idk nil) *)
(*          | _ => (true, hd (mkNode idk nil) (children n)) *)
(*          end *)
(*   | _ => (false, mkNode idk nil) *)
(*   end. *)
(* Extraction top_down_strategy. *)
(* Eval compute in top_down_strategy node5. *)
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
  mkNode (content n) no (children n).
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
SearchPattern (_ = _ -> _ = _).

Lemma comparable_node_of_debugging_tree_of_tree_is_comparable_node: forall n:Node, get_comparable_node_from_node (get_debugging_tree_from_tree n) = get_comparable_node_from_node n.
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
Qed.

Lemma debugging_tree_of_tree_is_in_tree: forall n:Node, is_node_in_tree (content (get_debugging_tree_from_tree n)) n.
Proof.
  intros n.
  induction n.
  simpl.
  left.
  reflexivity.
Qed.


Lemma content_debugging_tree_eq_content_tree: forall n:Node, content (get_debugging_tree_from_tree n) = content n.
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
Qed.

Lemma children_head_of_debugging_tree_are_all_idk: forall (n head:Node) (tail: list Node), children n = head::tail /\ is_debugging_tree n -> are_all_idk head.
Proof.
  intros n head tail H.
  inversion H.
  inversion H1.
  + apply and_list_true_implies_element_in_list_true with (children (n)).
    split.
    - exact H3.
    - induction n.
      induction children0.
      intuition.
      simpl.
      inversion H4.
      simpl.
      left.
      inversion H0.
      reflexivity.
Qed.


Lemma debugging_tree_of_children_head_of_debugging_tree_is_debugging_tree: forall (n head:Node) (tail: list Node), children n = head::tail /\ is_debugging_tree n -> is_debugging_tree (get_debugging_tree_from_tree head).
Proof.
  intros n head tail H.
  inversion H.
  inversion H1.
  assert (are_all_idk head).
  + apply children_head_of_debugging_tree_are_all_idk with n.
    split.
    - exact H3.
    - induction n.
      induction children0.
      intuition.
      simpl.
      inversion H4.
      simpl.
      left.
      inversion H0.
      reflexivity.
  + apply debugging_tree_of_idk_tree_is_debugging_tree.
    exact H4.
Qed.

Obligation Tactic := intros.

Program Fixpoint generic_debugging_algorithm_non_dependently_typed (n : Node) {measure (weight n)}: Node :=
  match children n with
    nil => n
  | head::tail => generic_debugging_algorithm_non_dependently_typed (get_debugging_tree_from_tree head)
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

(* Lemma gda_correct : forall n:Node, is_debugging_tree n -> is_debugging_tree (generic_debugging_algorithm_non_dependently_typed n) /\ children (generic_debugging_algorithm_non_dependently_typed n) = nil /\ is_node_in_tree (content (generic_debugging_algorithm_non_dependently_typed n)) n. *)
(* Proof. *)
(*   intros. *)
(*   intuition. *)
(*   + induction n. *)
(*     induction children0. *)
(*     - simpl. *)
(*     intuition. *)
(*     Tactics.program_simpl. *)
(*     unfold generic_debugging_algorithm_non_dependently_typed. *)
(*     simpl. *)
(*     intuition. *)
Obligation Tactic := intros.
Obligation Tactic := Tactics.program_simpl.


Program Fixpoint generic_debugging_algorithm_dependently_typed (n : {n: Node | is_debugging_tree n}) {measure (weight n)}: {m: Node | is_debugging_tree m /\ children m = nil} :=
  match children n with
    nil => n
  | head::tail => generic_debugging_algorithm_dependently_typed (get_debugging_tree_from_tree head)
  end.
Print generic_debugging_algorithm_dependently_typed_obligation_1.
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
  - apply and_list_true_implies_element_in_list_true with (children n).
    split.
    exact H1.
    exact H2.
    + apply debugging_tree_of_idk_tree_is_debugging_tree.
      exact H2.
Qed.
Obligation Tactic := intros.
Next Obligation.
  assert (In head (children (proj1_sig n))).
  + induction (children (proj1_sig n)).
    - inversion Heq_anonymous.
    - simpl.
      left.
      injection Heq_anonymous.
      intuition.
  + assert (weight head = weight (get_debugging_tree_from_tree head)).
    - apply debugging_tree_of_tree_has_same_weight.
    - simpl.
      assert (match head.(children) with | [] => 1 | n0 :: l => S (weight n0 + list_sum (map (fun child : Node => weight child) l)) end = weight (get_debugging_tree_from_tree head)). intuition. rewrite H1. rewrite <- H0.
      apply parent_weight_gt_child_weight.
      exact H.
Qed.

Obligation Tactic := intros.

Program Fixpoint generic_debugging_algorithm_dp (n : {n: Node | is_debugging_tree n}) {measure (weight n)}: {m: Node | is_node_in_tree (content m) n /\ is_debugging_tree m /\ children m = nil} :=
  match children n with
    nil => n
  | head::tail => generic_debugging_algorithm_dp (get_debugging_tree_from_tree head)
  end.
Obligations of generic_debugging_algorithm_dp.
Solve All Obligations.
Next Obligation.
  simpl.
  Tactics.program_simpl.
  split.
  + apply node_is_in_itself.
  + split.
    - exact H.
    - reflexivity.
Qed.
Obligations of generic_debugging_algorithm_dp.
Next Obligation.
  Tactics.program_simpl.
  inversion H.
  assert (are_all_idk head).
  + assert (In head (children n)).
  - induction (children n).
    inversion Heq_anonymous.
    simpl.
    left.
    injection Heq_anonymous.
    intuition.
  - apply and_list_true_implies_element_in_list_true with (children n).
    split.
    exact H1.
    exact H2.
    + apply debugging_tree_of_idk_tree_is_debugging_tree.
      exact H2.
Qed.
Obligation Tactic := intros.
Obligations of generic_debugging_algorithm_dp.
Next Obligation.
  assert (In head (children (proj1_sig n))).
  + induction (children (proj1_sig n)).
    - inversion Heq_anonymous.
    - simpl.
      left.
      injection Heq_anonymous.
      intuition.
  + assert (weight head = weight (get_debugging_tree_from_tree head)).
    - apply debugging_tree_of_tree_has_same_weight.
    - simpl.
      assert (match head.(children) with | [] => 1 | n0 :: l => S (weight n0 + list_sum (map (fun child : Node => weight child) l)) end = weight (get_debugging_tree_from_tree head)).
      intuition.
      rewrite H1.
      rewrite <- H0.
      apply parent_weight_gt_child_weight.
      exact H.
Qed.
Obligation Tactic := simpl.
Obligations of generic_debugging_algorithm_dp.
Next Obligation.
  simpl.
  split.
  assert (In head (children (proj1_sig n))).
  - induction (children (proj1_sig n)).
    + inversion Heq_anonymous.
    + simpl.
      left.
      injection Heq_anonymous.
      intuition.
  - assert (content (get_debugging_tree_from_tree head) = content head).
    apply content_debugging_tree_eq_content_tree.
    assert (is_node_in_tree (content head) (proj1_sig n)).
    apply child_node_is_in_parent.
    exact H.
    inversion H0.
    assert (content head = content (get_debugging_tree_from_tree head)).
    apply H0.
    simpl.
    assert (are_all_idk head).
    + induction (children (proj1_sig n)).
      inversion Heq_anonymous.
      simpl.
      injection Heq_anonymous.
      intuition.
      apply and_list_true_implies_element_in_list_true with (children (proj1_sig n)).
      split.
Qed.
