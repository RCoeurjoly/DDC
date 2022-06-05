Require Coq.extraction.Extraction.
Search list nat.
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
Search le.
Search list.
SearchPattern (_ <= _).
(* Lemma list_sum_ge_0 : forall l : list nat, 0 <= list_sum l. *)
(* Proof. intros l. induction l. simpl. intuition. simpl. assert (a >= 0). induction a. intuition. apply le_0_n.  subst. induction a. intuition.  *)
(* Qed. *)
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
  | children => 1 + list_sum (map (fun child => weight child) (children))
  end.
Lemma commutativity : forall a b:Prop, a/\b -> b/\a.
Proof.
  intros a b H. split. destruct H as [H1 H2]. exact H2. intuition.
  Qed.
Lemma weight_childfree_node_eq_1: forall n:Node, n.(children) = nil -> weight n = 1.
Proof.
  - intros n H. induction n. simpl. assert (children0 = nil). apply H. subst. reflexivity.
Qed.
SearchPattern (_ + _ > _).
Search Gt.
(* Lemma weight_g_0: forall n:Node, 0 < weight n. *)
(* Proof. intros n. induction n. induction children0. simpl. intuition. simpl. intuition. *)
(* Qed. *)
Eval compute in idk = idk.
Search bool.
Scheme Equality for Correctness.
Search Correctness.
Fixpoint are_all_idk (node : Node) : bool :=
  match node.(children) with
    nil => Correctness_beq node.(correctness) idk
  | children => andb (Correctness_beq node.(correctness) idk) (and_list (map (fun child => are_all_idk child) (children)))
  end.
Eval compute in are_all_idk node1.
Definition node4 := mkNode idk (node1::node2::nil).
Eval compute in are_all_idk node4.
Fixpoint is_debugging_tree (node : Node) : bool :=
  match node.(children) with
    nil => Correctness_beq node.(correctness) no
  | children => andb (Correctness_beq node.(correctness) no) (and_list (map (fun child => are_all_idk child) (children)))
  end.
(* Extraction pred. *)
(* Extraction is_debugging_tree. *)

Eval compute in is_debugging_tree node1.
Definition node5 := mkNode no (node1::nil).
Eval compute in is_debugging_tree node5.
Eval compute in list_sum (map (fun x => x + 3) (1::2::5::nil)).
Eval compute in weight node3.
Search list.
Print hd.
Search bool.
Search Prop.
Eval compute in hd 0 (1::nil).

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
Extraction top_down_strategy.
Eval compute in top_down_strategy node5.
Require Import Coq.Lists.List Coq.Bool.Bool.

Import Coq.Lists.List.ListNotations.

Scheme Equality for list.
Eval compute in Nat.ltb 1 2.
SearchPattern (_ < _).

Search Nat.ltb.
Eval compute in list_beq (nat) (Nat.leb) (1::nil) (1::nil).
Eval compute in list_beq (nat) (Nat.leb) (1::2::nil) (nil).
Search Prop.
Fixpoint get_largest_nat_in_list_rec (largest : list nat) (l : list nat) : (list nat) :=
  match l with
    nil => largest
  | head::tail => if (list_beq (nat) (Nat.leb) largest nil || (Nat.leb (hd 0 largest) head)) then get_largest_nat_in_list_rec (head::nil) tail else get_largest_nat_in_list_rec largest tail
  end.
Definition get_largest_nat_in_list (l : list nat) : (list nat) :=
  get_largest_nat_in_list_rec [] l.
Eval compute in get_largest_nat_in_list_rec nil (0::1::7::8::9::3::4::5::nil).
Eval compute in get_largest_nat_in_list_rec nil (nil).
Eval compute in get_largest_nat_in_list (0::1::7::8::9::3::4::5::nil).
Eval compute in get_largest_nat_in_list (nil).
Search list.
Print filter.
Check filter.
Check andb true.
Check weight .
(* Conseguir un typo Node -> bool *)
(* Eval compute in filter (weight Nat.eqb 2 ) (node1::nil). *)
Definition my_node_list : list Node := node1::node2::node3::node4::node5::nil.
(* Eval compute in filter (Nat.eqb weight list_max (map (fun n => weight n))) my_node_list. *)

Eval compute in list_max (nil).
Goal 0 * 0 = 2 -> False.
Proof. easy.
Qed.

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

Fixpoint generic_debugging_algorithm (n : Node) : Node :=
  match children (get_debugging_tree_from_tree n) with
    nil => n
    | head::tail => generic_debugging_algorithm head
  end.
(* Fixpoint choose A (l : list A) : distr A := *)
(*   match l with *)
(*     | nil => distr_null A *)
(*     | cons hd tl => Mchoice ([1/](length l)) (Munit hd) (choose tl) *)
(*   end. *)
(* Check is_true. *)
(* Lemma example2: forall a b: Prop, a/\b ->b/\a. *)
(*   Proof. intros a b H.  *)
(* Lemma generic_debugging_algorithm_is_correct : forall n : Node, children (generic_debugging_algorithm n) = nil. *)
(* Proof. intros. induction n. induction children0. *)
(*        + simpl. reflexivity. *)
(*        + simpl. *)
(* Search list. *)
(* Definition remove_idk_node (l : list Node) (p : nat) : list Node := *)
(*   match l with *)
(*     nil => nil *)
(*     | _ => *)
(*   end. *)
(* (* Lemma choose_uniform : forall A (d : A) (l : list A) f, *) *)
(* (*   mu (choose l) f == sigma (fun i => ([1/](length l)) * f (nth i l d)) (length l). *) *)

(* (* Lemma In_nth : forall A (x:A) l, In x l -> exists i, (i < length l)%nat /\ nth i l x = x. *) *)

(* (* Lemma choose_le_Nnth : *) *)
(* (*   forall A (l:list A) x f alpha, *) *)
(* (*     In x l -> *) *)
(* (*     alpha <= f x -> *) *)
(* (*     [1/](length l) * alpha <= mu (choose l) f. *) *)
