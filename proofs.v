(* Add Rec LoadPath "/nix/store/ir85s7vq85gg888j3gkqvba411nxrjxf-coq8.15-alea/lib/coq/8.15+alpha/user-contrib/ALEA/" as ALEA. *)
From Coq Require Export Arith.
(* From ALEA Require Import Ccpo. *)
(* From ALEA Require Import Choice. *)
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
(* Inductive DebuggingTree : Type := *)
(*     right_neutral : forall x, x * 1 = x  *)
Definition node1 := mkNode idk nil.
Definition node2 := mkNode idk nil.
Definition node3 := mkNode trusted (node1::node2::nil).
Eval compute in correctness node3.
(* Lemma list_sum_ge_0 : forall l : list nat, 0 <= list_sum l. *)
(* Proof. intros l. induction l. simpl. intuition. simpl. assert (a >= 0). induction a. intuition. apply le_0_n.  subst. induction a. intuition.  *)
(* Qed. *)
Fixpoint and_list (l : list Prop) : Prop :=
  match l with
    nil => True
  | n::tl => and n (and_list tl)
  end.
Eval compute in and_list (True::True::True::nil).
Check 1::nil.
Fixpoint weight (node : Node) : nat :=
  match node.(children) with
    nil => 1
  | children => S (list_sum (map (fun child => weight child) (children)))
  end.
Lemma commutativity : forall a b:Prop, a/\b -> b/\a.
Proof.
  intros a b H. split. destruct H as [H1 H2]. exact H2. destruct H as [H1 H2]. exact H1.
Qed.

Lemma weight_childfree_node_eq_1: forall n:Node, n.(children) = nil -> weight n = (S 0).
Proof.
  - intros n H. induction n. simpl. assert (children0 = nil). apply H. rewrite H0. reflexivity.
Qed.

Lemma weight_gt_0: forall n:Node, 0 < weight n.
Proof. intros n. induction n. induction children0. simpl. intuition. simpl. intuition.
Qed.
Search list.
Require Import Lia.
Search nat.

Lemma node_weight_gt_sum_children_weight: forall n:Node, weight n > list_sum (map (fun child => weight child) (children n)).
Proof. intros n. induction n. simpl. induction children0.
       + simpl. destruct (zerop 1). discriminate. assumption.
       + simpl. intuition.
Qed.

SearchPattern (_ <= _).
Lemma nat_in_list_le_list_sum: forall (l:list nat) (element: nat), In element l -> element <= list_sum l.
Proof. intros l element H. induction l.
       - simpl. inversion H.
       - simpl. destruct H.
         + subst. apply Nat.le_add_r.
         + transitivity (list_sum l);auto.
           rewrite Nat.add_comm. apply Nat.le_add_r.
Qed.

Lemma child_weight_le_sum_children_weight: forall (l:list Node) (child: Node), In child l -> list_sum (map (fun child => weight child) l) >= weight child.
Proof. intros l child H. apply nat_in_list_le_list_sum. induction l.
       - simpl. inversion H.
       - simpl. destruct H.
         + subst. intuition.
         + subst. intuition.
Qed.
SearchPattern (_ < _ + _).
Lemma parent_weight_gt_child_weight: forall parent child:Node, In child (children parent) -> weight child < weight parent.
Proof. intros parent child H. induction parent. simpl. induction children0.
       + inversion H.
       + inversion H.
         - rewrite H0. intuition.
         -  intuition. assert (weight child <= list_sum (map (fun child0 : Node => weight child0) children0)). apply child_weight_le_sum_children_weight. assumption. intuition. assert (weight a > 0). apply weight_gt_0. assert (weight child < (weight a + list_sum (map (fun child0 : Node => weight child0) children0))). inversion H2. rewrite Nat.add_comm. apply Nat.lt_add_pos_r. assumption. assert (weight child < S m). intuition. rewrite Nat.add_comm. intuition. intuition.
Qed.

Eval compute in idk = idk.
Scheme Equality for Correctness.
Fixpoint are_all_idk (node : Node) : Prop :=
  match node.(children) with
    nil => node.(correctness) = idk
  | children => and (node.(correctness) = idk) (and_list (map (fun child => are_all_idk child) (children)))
  end.

Lemma are_all_idk_implies_children_all_idk: forall n : Node, are_all_idk n -> and_list (map (fun child => are_all_idk child) (children n)).
Proof. intros n H. induction n. induction children0.
       + inversion H. simpl. constructor.
       + inversion H. simpl. split.
       - inversion H. apply H3.
       - apply H1.
Qed.

Eval compute in are_all_idk node1.
Definition node4 := mkNode idk (node1::node2::nil).
Eval compute in are_all_idk node4.
Definition is_debugging_tree (node : Node) : bool :=
  match node.(children) with
    nil => Correctness_beq node.(correctness) no
  | children => andb (Correctness_beq node.(correctness) no) (and_list (map (fun child => are_all_idk child) (children)))
  end.
(* Extraction pred. *)
(* Extraction is_debugging_tree. *)

Eval compute in is_debugging_tree node1.
Definition node5 := mkNode no (node1::nil).
Eval compute in is_debugging_tree node5.
(* Eval compute in list_sum (map (fun x => x + 3) (1::2::5::nil)). *)
Eval compute in weight node3.
Eval compute in is_debugging_tree node5.
Check andb (is_debugging_tree node1) (Nat.ltb 0 (length (children node1))).
Eval compute in andb (is_debugging_tree node1) (Nat.ltb 0 (length (children node1))).
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
Proof. intros n. induction n. simpl. reflexivity.
Qed.
Lemma children_of_debugging_tree_remain_unchanged: forall n:Node, children n = children (get_debugging_tree_from_tree n).
Proof. intros n. induction n. simpl. reflexivity.
Qed.
Lemma debugging_tree_root_node_is_incorrect: forall n:Node, correctness (get_debugging_tree_from_tree n) = no.
Proof. intros n. induction n. simpl. reflexivity.
Qed.

Lemma debugging_tree_of_tree_with_all_children_idk_is_debugging_tree: forall n:Node, eq_true (and_list (map (fun child => are_all_idk child) (children n))) -> eq_true (is_debugging_tree (get_debugging_tree_from_tree n)).
Proof. intros n H. induction n. induction children0.
       + intuition.
       + intuition.
Qed.

Lemma debugging_tree_of_idk_tree_is_debugging_tree: forall n:Node, eq_true (are_all_idk n) -> eq_true (is_debugging_tree (get_debugging_tree_from_tree n)).
Proof. intros n H. assert (correctness (get_debugging_tree_from_tree n) = no). apply debugging_tree_root_node_is_incorrect. assert (eq_true (and_list (map (fun child => are_all_idk child) (children n)))). apply H. induction n. induction children0.
       + intuition.
       + intuition. assert (get_debugging_tree_from_tree {|
correctness := correctness0;
           children := a :: children0
         |}). apply debugging_tree_root_node_is_incorrect.
Qed.

Show Obligation Tactic.
Obligation Tactic := intros.

Program Fixpoint generic_debugging_algorithm (n : Node) {measure (weight n)}: Node :=
  match children n with
    nil => n
  | head::tail => generic_debugging_algorithm (get_debugging_tree_from_tree head)
  end.
Next Obligation.
  assert (In head (children n)). induction (children n). inversion Heq_anonymous.  simpl. left. injection Heq_anonymous. intuition. assert (weight head = weight (get_debugging_tree_from_tree head)). apply debugging_tree_of_tree_has_same_weight. rewrite <- H0. apply parent_weight_gt_child_weight. assumption.
Qed.
Next Obligation.
  intuition.
Qed.
Check generic_debugging_algorithm.
Show Obligation Tactic.
Obligation Tactic := Tactics.program_simpl.
Show Obligation Tactic.

Lemma generic_debugging_algorithm_returns_childfree_node: forall n:Node, children (generic_debugging_algorithm n) = nil.
Proof. intros n. induction n. induction children0.
       + unfold generic_debugging_algorithm. simpl. intuition. auto. eauto.


Lemma generic_debugging_algorithm_returns_incorrect_childfree_node_when_given_debugging_tree: forall n:Node, eq_true (is_debugging_tree n) -> correctness (generic_debugging_algorithm n) = no.
Proof. intros n H. intuition.
       + induction n. induction children0.
         - intuition. simpl.


(* From ALEA Require Import Cover. *)
(* (* From ALEA Require Import Misc. *) *)
(* (* From ALEA Require Import Monads. *) *)
(* (* From ALEA Require Import Probas. *) *)
(* (* From ALEA Require Import Prog. *) *)
(* (* From ALEA Require Import Sets. *) *)
(* (* From ALEA Require Import Uprop. *) *)
(* From ALEA Require Import Utheory. *)
(* Module MyM (Univ : Universe). *)
(*   Module Import Cover := CoverFun Univ. *)
(*   Include Univ. *)
(*   Export RP. *)
(*   Export PP. *)
(*   Set Implicit Arguments. *)
(*   Unset Strict Implicit. *)
(*   Require Coq.extraction.Extraction. *)
(*   Extraction Language OCaml. *)
(*   Set Printing Projections. *)
(*   Require Import Bool. *)
(*   Require Import List. *)
(*   Inductive Correctness : Type := *)
(*   | yes : Correctness *)
(*   | no : Correctness *)
(*   | trusted : Correctness *)
(*   | idk : Correctness. *)
(*   Inductive Node : Type := mkNode *)
(*                              { correctness : Correctness *)
(*                              ; children : list Node *)
(*                              }. *)
(*   (* Inductive DebuggingTree : Type := *) *)
(*   (*     right_neutral : forall x, x * 1 = x  *) *)
(*   Definition node1 := mkNode idk nil. *)
(*   Definition node2 := mkNode idk nil. *)
(*   Definition node3 := mkNode trusted (node1::node2::nil). *)
(*   Eval compute in correctness node3. *)
(*   (* Lemma list_sum_ge_0 : forall l : list nat, 0 <= list_sum l. *) *)
(*   (* Proof. intros l. induction l. simpl. intuition. simpl. assert (a >= 0). induction a. intuition. apply le_0_n.  subst. induction a. intuition.  *) *)
(*   (* Qed. *) *)
(*   Fixpoint and_list (l : list bool) : bool := *)
(*     match l with *)
(*       nil => true *)
(*     | n::tl => andb n (and_list tl) *)
(*     end. *)
(*   Eval compute in and_list (true::true::true::nil). *)
(*   Check 1::nil. *)
(*   Fixpoint weight (node : Node) : nat := *)
(*     match node.(children) with *)
(*       nil => 1 *)
(*     | children => 1 + list_sum (map (fun child => weight child) (children)) *)
(*     end. *)
(*   Lemma commutativity : forall a b:Prop, a/\b -> b/\a. *)
(*   Proof. *)
(*     intros a b H. split. destruct H as [H1 H2]. exact H2. intuition. *)
(*   Qed. *)

(*   Lemma weight_childfree_node_eq_1: forall n:Node, n.(children) = nil -> weight n = (S 0). *)
(*   Proof. *)
(*     - intros n H. induction n. simpl. assert (children0 = nil). apply H. subst. reflexivity. *)
(*   Qed. *)

(*   (* Lemma weight_g_0: forall n:Node, 0 < weight n. *) *)
(*   (* Proof. intros n. induction n. induction children0. simpl. intuition. simpl. intuition. *) *)
(*   (* Qed. *) *)
(*   Eval compute in idk = idk. *)
(*   Scheme Equality for Correctness. *)
(*   Fixpoint are_all_idk (node : Node) : bool := *)
(*     match node.(children) with *)
(*       nil => Correctness_beq node.(correctness) idk *)
(*     | children => andb (Correctness_beq node.(correctness) idk) (and_list (map (fun child => are_all_idk child) (children))) *)
(*     end. *)
(*   Eval compute in are_all_idk node1. *)
(*   Definition node4 := mkNode idk (node1::node2::nil). *)
(*   Eval compute in are_all_idk node4. *)
(*   Definition is_debugging_tree (node : Node) : bool := *)
(*     match node.(children) with *)
(*       nil => Correctness_beq node.(correctness) no *)
(*     | children => andb (Correctness_beq node.(correctness) no) (and_list (map (fun child => are_all_idk child) (children))) *)
(*     end. *)
(*   (* Extraction pred. *) *)
(*   (* Extraction is_debugging_tree. *) *)

(*   Eval compute in is_debugging_tree node1. *)
(*   Definition node5 := mkNode no (node1::nil). *)
(*   Eval compute in is_debugging_tree node5. *)
(*   (* Eval compute in list_sum (map (fun x => x + 3) (1::2::5::nil)). *) *)
(*   Eval compute in weight node3. *)
(*   Eval compute in is_debugging_tree node5. *)
(*   Check andb (is_debugging_tree node1) (Nat.ltb 0 (length (children node1))). *)
(*   Eval compute in andb (is_debugging_tree node1) (Nat.ltb 0 (length (children node1))). *)
(*   Definition top_down_strategy (n : Node) : (bool * Node) := *)
(*     match correctness n with *)
(*       no => match children n with *)
(*              nil => (false, mkNode idk nil) *)
(*            | _ => (true, hd (mkNode idk nil) (children n)) *)
(*            end *)
(*     | _ => (false, mkNode idk nil) *)
(*     end. *)
(*   (* Extraction top_down_strategy. *) *)
(*   Eval compute in top_down_strategy node5. *)
(*   Require Import Coq.Lists.List Coq.Bool.Bool. *)

(*   Import Coq.Lists.List.ListNotations. *)

(*   Scheme Equality for list. *)
(*   Eval compute in Nat.ltb 1 2. *)
(*   (* Eval compute in list_beq (Nat.leb) (1::nil) (1::nil). *) *)
(*   (* Eval compute in list_beq (Nat.leb) (1::2::nil) (nil). *) *)
(*   (* Fixpoint get_largest_nat_in_list_rec (largest : list nat) (l : list nat) : (list nat) := *) *)
(*   (*   match l with *) *)
(*   (*     nil => largest *) *)
(*   (*   | head::tail => if (list_beq (nat) (Nat.leb) largest nil || (Nat.leb (hd 0 largest) head)) then get_largest_nat_in_list_rec (head::nil) tail else get_largest_nat_in_list_rec largest tail *) *)
(*   (*   end. *) *)
(*   (* Definition get_largest_nat_in_list (l : list nat) : (list nat) := *) *)
(*   (*   get_largest_nat_in_list_rec [] l. *) *)
(*   (* Eval compute in get_largest_nat_in_list_rec nil (0::1::7::8::9::3::4::5::nil). *) *)
(*   (* Eval compute in get_largest_nat_in_list_rec nil (nil). *) *)
(*   (* Eval compute in get_largest_nat_in_list (0::1::7::8::9::3::4::5::nil). *) *)
(*   (* Eval compute in get_largest_nat_in_list (nil). *) *)
(*   Check andb true. *)
(*   Check weight . *)
(*   (* Conseguir un typo Node -> bool *) *)
(*   (* Eval compute in filter (weight Nat.eqb 2 ) (node1::nil). *) *)
(*   Definition my_node_list : list Node := node1::node2::node3::node4::node5::nil. *)
(*   (* Eval compute in filter (Nat.eqb weight list_max (map (fun n => weight n))) my_node_list. *) *)

(*   Eval compute in list_max (nil). *)
(*   (* Goal 0 * 0 = 2 -> False. *) *)
(*   (* Proof. easy. *) *)
(*   (* Qed. *) *)

(*   Definition evaluate_node (n : Node) : Correctness := *)
(*     no. *)
(*   (* Lemma largest_of_list_is_correct: forall l: list nat, l <> nil -> get_largest_nat_in_list l <> nil. *) *)
(*   (* Proof. intros l H. induction l. intuition. induction a. intuition. exact: (False_ind (0::l = [])). *) *)
(*   (* Qed. *) *)
(*   (* Definition get_heaviest_node (l : list Node, n : nat) : (bool * Node) := *) *)
(*   (*   match l with *) *)
(*   (*     nil => (false, mkNode idk nil) *) *)
(*   (*     | *) *)
(*   (* Definition heaviest_first_strategy (n : {n : Node | eq_true (andb (is_debugging_tree n) (Nat.ltb 0 (length (children n))))}) : Node := *) *)
(*   (*   (hd (mkNode idk nil) (children (proj1_sig n))). *) *)
(*   (* Eval compute in top_down_strategy node5. *) *)
(*   (* Scheme Equality for Node. *) *)
(*   (* Eval compute in Node_beq (mkNode no nil) (mkNode no nil). *) *)
(*   Definition get_debugging_tree_from_tree (n : Node) : Node := *)
(*     mkNode no (children n). *)

(*   Fixpoint generic_debugging_algorithm (n : Node) : Node := *)
(*     match children (get_debugging_tree_from_tree n) with *)
(*       nil => n *)
(*     | head::tail => generic_debugging_algorithm head *)
(*     end. *)
(*   (* Fixpoint choose A (l : list A) : distr A := *) *)
(*   (*   match l with *) *)
(*   (*     | nil => distr_null A *) *)
(*   (*     | cons hd tl => Mchoice ([1/](length l)) (Munit hd) (choose tl) *) *)
(*   (*   end. *) *)
(*   (* Check is_true. *) *)
(*   (* Lemma example2: forall a b: Prop, a/\b ->b/\a. *) *)
(*   (*   Proof. intros a b H.  *) *)
(*   (* Lemma generic_debugging_algorithm_is_correct : forall n : Node, children (generic_debugging_algorithm n) = nil. *) *)
(*   (* Proof. intros. induction n. induction children0. *) *)
(*   (*        + simpl. reflexivity. *) *)
(*   (*        + simpl. *) *)
(*   (* Definition remove_idk_node (l : list Node) (p : nat) : list Node := *) *)
(*   (*   match l with *) *)
(*   (*     nil => nil *) *)
(*   (*     | _ => *) *)
(*   (*   end. *) *)
(*   (* (* Lemma choose_uniform : forall A (d : A) (l : list A) f, *) *) *)
(*   (* (*   mu (choose l) f == sigma (fun i => ([1/](length l)) * f (nth i l d)) (length l). *) *) *)

(*   (* (* Lemma In_nth : forall A (x:A) l, In x l -> exists i, (i < length l)%nat /\ nth i l x = x. *) *) *)

(*   (* (* Lemma choose_le_Nnth : *) *) *)
(*   (* (*   forall A (l:list A) x f alpha, *) *) *)
(*   (* (*     In x l -> *) *) *)
(*   (* (*     alpha <= f x -> *) *) *)
(*   (* (*     [1/](length l) * alpha <= mu (choose l) f. *) *) *)

(*   (* Section Gamble. *) *)

(*   (* Fixpoint pow2 (n:nat) : nat := *) *)
(*   (*    match n with O => 1%nat | S p => (2 * (pow2 p))%nat end. *) *)

(*   (* Fixpoint play (n:nat) (b:nat) : distr nat := *) *)
(*   (*     match n with *) *)
(*   (*       O => Munit O *) *)
(*   (*     | S p => Mif Flip (Munit ((pow2 n) * b)%nat) (play p (2*b)) *) *)
(*   (*     end. *) *)

(*   (* Lemma pow2not0 : forall n, pow2 n <> O. *) *)
(*   (* induction n; simpl; omega. *) *)
(*   (* Save. *) *)
(*   (* Hint Resolve pow2not0. *) *)


(*   (* Lemma proba_loose : forall n b, ~ b=O -> mu (play n b) (carac_eq O)== [1/2]^n. *) *)
(*   (* induction n; intros. *) *)
(*   (* simpl; auto. *) *)
(*   (* simpl. *) *)
(*   (* replace (pow2 n + (pow2 n + 0))%nat with (pow2 (S n)) by trivial. *) *)
(*   (* rewrite (cover_eq_zero _ (is_eq O)). *) *)
(*   (* repeat Usimpl. *) *)
(*   (* apply IHn. *) *)
(*   (* omega. *) *)
(*   (* apply not_eq_sym. *) *)
(*   (* apply NPeano.Nat.neq_mul_0; auto. *) *)
(*   (* Save. *) *)

(*   (* Lemma proba_win : forall n b, ~ b=O -> mu (play n b) (carac_eq ((pow2 n) * b)%nat)== [1-]([1/2]^n). *) *)
(*   (* induction n; intros. *) *)
(*   (* simpl; repeat Usimpl. *) *)
(*   (* rewrite (cover_eq_zero _ (is_eq (b + 0))); intuition. *) *)
(*   (* simpl. *) *)
(*   (* rewrite (cover_eq_one _ (is_eq (pow2 (S n) * b)%nat)); trivial. *) *)
(*   (* repeat Usimpl. *) *)
(*   (* replace ((pow2 n + (pow2 n + 0)) * b)%nat with (pow2 n * (2*b))%nat. *) *)
(*   (* rewrite IHn. *) *)
(*   (* rewrite <- Uinv_half; repeat Usimpl; auto. *) *)
(*   (* omega. *) *)
(*   (* ring. *) *)
(*   (* Save. *) *)

(*   (* End Gamble. *) *)
(*   Locate distr. *)
(*   Fixpoint lrange n := *)
(*     match n with *)
(*     | O => cons O nil *)
(*     | S m => cons (S m) (lrange m) *)
(*     end. *)
(*   Fixpoint choose A (l : list A) : distr A := *)
(*     match l with *)
(*     | nil => distr_null A *)
(*     | cons hd tl => Mchoice ([1/]1+(length l)) (Munit hd) (choose tl) *)
(*     end. *)

(*   Check choose (lrange (S 0)). *)
(*   Check choose (yes::no::nil). *)
(*   Search distr. *)

(* End MyM. *)
