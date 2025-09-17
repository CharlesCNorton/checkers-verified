(* ========================================================================= *)
(* ENGLISH DRAUGHTS (CHECKERS) — FORMAL SPECIFICATION WITH VALIDATION        *)
(* ========================================================================= *)

(* SECTION 1: FOUNDATIONS *)

(* Core Coq imports *)
Require Import Coq.Program.Program.
Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetList.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.micromega.Lia.  (* Replaced omega with lia *)
Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Relations.Relations.
Require Import Coq.ZArith.ZArith.

(* List notations *)
Import ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(* Proof-mode configuration *)
Set Implicit Arguments.
Generalizable All Variables.
Set Universe Polymorphism.

(* Additional useful tactics *)
Ltac inv H := inversion H; clear H; subst.
Ltac break_match := match goal with | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:? end.
Ltac break_if := match goal with | [ |- context[if ?x then _ else _] ] => destruct x eqn:? end.

(* Custom notations - reserve for later use *)
Reserved Notation "⟦ n ⟧" (at level 0).
Reserved Notation "b1 ≈ b2" (at level 70).
Reserved Notation "p ·→ q" (at level 50).

(* ========================================================================= *)
(* SECTION 2: FINITE DOMAIN THEORY                                           *)
(* ========================================================================= *)

(* Type alias for 8-element finite type *)
Definition Fin8 := Fin.t 8.

(* Enumeration of all Fin8 values *)
Definition enum_fin8 : list Fin8 :=
  [F1; FS F1; FS (FS F1); FS (FS (FS F1)); 
   FS (FS (FS (FS F1))); FS (FS (FS (FS (FS F1))));
   FS (FS (FS (FS (FS (FS F1))))); FS (FS (FS (FS (FS (FS (FS F1))))))].

(* Finite typeclass for exhaustive enumeration *)
Class Finite (A : Type) := {
  enum : list A;
  enum_complete : forall x : A, In x enum;
  enum_nodup : NoDup enum
}.

(* Convert Fin8 to nat *)
Definition fin8_to_nat (f : Fin8) : nat := proj1_sig (Fin.to_nat f).

(* Convert bounded nat to Fin8 *)
Definition fin8_of_nat (n : nat) (H : (n < 8)%nat) : Fin8 := Fin.of_nat_lt H.

(* Alternative: using sig type as specified *)
Program Definition nat_of_fin8 (f : Fin8) : { n : nat | (n < 8)%nat } :=
  exist _ (fin8_to_nat f) _.
Next Obligation.
  unfold fin8_to_nat.
  destruct (Fin.to_nat f) as [n H]. simpl. exact H.
Defined.

Definition fin8_of_bounded (nb : { n : nat | (n < 8)%nat }) : Fin8 :=
  match nb with
  | exist _ n H => @Fin.of_nat_lt n 8 H
  end.

(* Integer embeddings for coordinates *)
Definition fileZ (f : Fin8) : Z := Z.of_nat (fin8_to_nat f).
Definition rankZ (r : Fin8) : Z := Z.of_nat (fin8_to_nat r).

(* Decidable equality for Fin.t *)
Instance Fin_eq_dec (n : nat) : EqDec (Fin.t n) eq.
Proof.
  unfold EqDec. intros x y.
  destruct (Fin.eq_dec x y).
  - left. exact e.
  - right. exact n0.
Defined.

(* Helper function to convert Fin8 to nat for case analysis *)
Definition fin8_to_bounded (f : Fin8) : { n : nat | (n < 8)%nat } :=
  nat_of_fin8 f.

(* Helper lemma 1: F1 is in enum_fin8 *)
Lemma F1_in_enum : In F1 enum_fin8.
Proof.
  unfold enum_fin8.
  simpl. left. reflexivity.
Qed.

(* Helper lemma 2: Every Fin8 is one of the 8 constructors *)
Lemma fin8_eq_cases : forall f : Fin8,
  f = F1 \/ f = FS F1 \/ f = FS (FS F1) \/ f = FS (FS (FS F1)) \/
  f = FS (FS (FS (FS F1))) \/ f = FS (FS (FS (FS (FS F1)))) \/
  f = FS (FS (FS (FS (FS (FS F1))))) \/ f = FS (FS (FS (FS (FS (FS (FS F1)))))).
Proof.
  intro f.
  apply Fin.caseS' with (p := f).
  - left. reflexivity.
  - intro f'. apply Fin.caseS' with (p := f').
    + right. left. reflexivity.
    + intro f''. apply Fin.caseS' with (p := f'').
      * right. right. left. reflexivity.
      * intro f3. apply Fin.caseS' with (p := f3).
        -- right. right. right. left. reflexivity.
        -- intro f4. apply Fin.caseS' with (p := f4).
           ++ right. right. right. right. left. reflexivity.
           ++ intro f5. apply Fin.caseS' with (p := f5).
              ** right. right. right. right. right. left. reflexivity.
              ** intro f6. apply Fin.caseS' with (p := f6).
                 --- right. right. right. right. right. right. left. reflexivity.
                 --- intro f7. apply Fin.caseS' with (p := f7).
                     +++ right. right. right. right. right. right. right. reflexivity.
                     +++ intro f8. apply Fin.case0 with (p := f8).
Qed.

(* Helper lemma 3: NoDup of enum_fin8 *)
Lemma enum_fin8_nodup : NoDup enum_fin8.
Proof.
  unfold enum_fin8.
  repeat constructor; simpl; intuition discriminate.
Qed.

(* Helper lemma 4: Complete enumeration of Fin8 *)
Lemma fin8_in_enum : forall f : Fin8, In f enum_fin8.
Proof.
  intro f.
  unfold enum_fin8.
  destruct (fin8_eq_cases f) as [?|[?|[?|[?|[?|[?|[?|?]]]]]]]; subst; simpl;
    repeat (left; reflexivity) || (right; simpl) || auto.
Qed.

(* Lemma for exhaustive case analysis on Fin8 *)
Lemma fin8_cases : forall (P : Fin8 -> Prop),
  P F1 -> P (FS F1) -> P (FS (FS F1)) -> P (FS (FS (FS F1))) ->
  P (FS (FS (FS (FS F1)))) -> P (FS (FS (FS (FS (FS F1))))) ->
  P (FS (FS (FS (FS (FS (FS F1)))))) -> P (FS (FS (FS (FS (FS (FS (FS F1))))))) ->
  forall f, P f.
Proof.
  intros P H0 H1 H2 H3 H4 H5 H6 H7 f.
  destruct (fin8_eq_cases f) as [?|[?|[?|[?|[?|[?|[?|?]]]]]]]; subst; assumption.
Qed.

(* Instance for Finite Fin8 *)
Program Instance Finite_Fin8 : Finite Fin8 := {
  enum := enum_fin8
}.
Next Obligation.
  (* enum_complete *)
  apply fin8_in_enum.
Defined.
Next Obligation.
  (* enum_nodup *)
  apply enum_fin8_nodup.
Defined.

(* Instance for Finite bool *)
Program Instance Finite_bool : Finite bool := {
  enum := [true; false]
}.
Next Obligation.
  (* enum_complete *)
  destruct x; simpl; auto.
Defined.
Next Obligation.
  (* enum_nodup *)
  constructor.
  - simpl. intro H. destruct H as [H|H]; [discriminate H | exact H].
  - constructor.
    + simpl. intro H. destruct H.
    + constructor.
Defined.

(* Bijection properties *)
Lemma fin8_nat_bijection1 : forall f : Fin8,
  fin8_of_bounded (nat_of_fin8 f) = f.
Proof.
  intro f.
  unfold fin8_of_bounded, nat_of_fin8, fin8_of_nat.
  simpl.
  apply Fin.of_nat_to_nat_inv.
Qed.

Lemma fin8_nat_bijection2 : forall (n : nat) (H : (n < 8)%nat),
  proj1_sig (nat_of_fin8 (@fin8_of_nat n H)) = n.
Proof.
  intros n H.
  unfold nat_of_fin8, fin8_of_nat, fin8_to_nat.
  simpl.
  rewrite Fin.to_nat_of_nat.
  reflexivity.
Qed.

(* Validation lemma *)
Lemma all_fin8_in_enumeration : forall (f : Fin8), In f enum_fin8.
Proof.
  intro f.
  apply fin8_in_enum.
Qed.

(* Additional helper: bool decidability *)
Lemma bool_decidable : forall b : bool, {b = true} + {b = false}.
Proof.
  destruct b; [left|right]; reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 3: POSITION ABSTRACTION (DARK-SQUARE SUBSET OF 8×8)              *)
(* ========================================================================= *)

(* Type aliases for clarity *)
Definition Rank := Fin8.
Definition File := Fin8.

(* Predicate to identify dark squares: rank + file must be odd *)
(* In standard checkers, dark squares have (rank + file) mod 2 = 1 *)
Definition dark (r : Rank) (f : File) : bool :=
  Nat.odd (fin8_to_nat r + fin8_to_nat f).

(* Position type: only dark squares are valid positions *)
Record Position := mkPosition {
  pos_rank : Rank;
  pos_file : File;
  pos_dark : dark pos_rank pos_file = true
}.

(* Constructor for positions with validation *)
Definition mk_pos (r : Rank) (f : File) : option Position :=
  match Bool.bool_dec (dark r f) true with
  | left H => Some (mkPosition r f H)
  | right _ => None
  end.

(* Projections *)
Definition rank (p : Position) : Rank := pos_rank p.
Definition file (p : Position) : File := pos_file p.

(* Lemma: dark property is preserved *)
Lemma position_is_dark : forall p : Position,
  dark (rank p) (file p) = true.
Proof.
  intro p. unfold rank, file. apply pos_dark.
Qed.

(* Helper lemma: position equality *)
Lemma position_eq : forall p1 p2 : Position,
  rank p1 = rank p2 -> file p1 = file p2 -> p1 = p2.
Proof.
  intros p1 p2 Hr Hf.
  destruct p1 as [r1 f1 H1].
  destruct p2 as [r2 f2 H2].
  unfold rank in Hr. unfold file in Hf. simpl in Hr. simpl in Hf.
  subst r2. subst f2.
  f_equal.
  apply UIP_dec. apply Bool.bool_dec.
Qed.

(* Helper lemma: mk_pos inversion *)
Lemma mk_pos_some_inv : forall r f p,
  mk_pos r f = Some p -> rank p = r /\ file p = f.
Proof.
  intros r f p H.
  unfold mk_pos in H.
  destruct (Bool.bool_dec (dark r f) true) as [E|E].
  - injection H as <-. split; reflexivity.
  - discriminate.
Qed.

(* Helper lemma: mk_pos creates position with correct properties *)
Lemma mk_pos_correct : forall r f,
  dark r f = true -> exists p, mk_pos r f = Some p /\ rank p = r /\ file p = f.
Proof.
  intros r f H.
  unfold mk_pos.
  destruct (Bool.bool_dec (dark r f) true) as [E|E].
  - exists (mkPosition r f E).
    split; [reflexivity | split; reflexivity].
  - congruence.
Qed.

(* Generate list of dark files for a given rank *)
Definition dark_files_for_rank (r : Rank) : list File :=
  List.filter (fun f => dark r f) enum_fin8.

(* Helper: each rank has exactly 4 dark squares *)
Lemma dark_files_count : forall r : Rank,
  length (dark_files_for_rank r) = 4%nat.
Proof.
  intro r.
  unfold dark_files_for_rank.
  apply fin8_cases with (f := r); reflexivity.
Qed.

(* Helper: Generate positions for a rank preserving order *)
Definition positions_in_rank (r : Rank) : list Position :=
  List.fold_right (fun f acc =>
    match mk_pos r f with
    | Some p => p :: acc
    | None => acc
    end) [] (dark_files_for_rank r).

(* Generate all 32 dark square positions *)
Definition enum_pos : list Position :=
  List.flat_map positions_in_rank enum_fin8.

(* Helper lemma: positions_in_rank contains exactly positions with that rank *)
Lemma positions_in_rank_correct : forall r p,
  In p (positions_in_rank r) <-> (rank p = r /\ dark (rank p) (file p) = true).
Proof.
  intros r p.
  split.
  - intro H.
    unfold positions_in_rank in H.
    induction (dark_files_for_rank r) as [|f fs IH].
    + simpl in H. contradiction.
    + simpl in H.
      destruct (mk_pos r f) eqn:E.
      * destruct H as [H|H].
        -- subst. apply mk_pos_some_inv in E. destruct E. split; [assumption|].
           apply position_is_dark.
        -- apply IH. assumption.
      * apply IH. assumption.
  - intros [Hr Hd].
    unfold positions_in_rank.
    assert (Hf: In (file p) (dark_files_for_rank r)).
    {
      unfold dark_files_for_rank.
      apply filter_In. split.
      - apply fin8_in_enum.
      - rewrite <- Hr. exact Hd.
    }
    clear Hd.
    induction (dark_files_for_rank r) as [|f fs IH].
    + contradiction.
    + simpl in Hf. destruct Hf as [Hf|Hf].
      * subst f. simpl.
        destruct (mk_pos r (file p)) eqn:E.
        -- left.
           apply mk_pos_some_inv in E.
           destruct E as [Hr' Hf'].
           apply position_eq; congruence.
        -- exfalso.
           assert (dark r (file p) = true).
           { rewrite <- Hr. apply position_is_dark. }
           unfold mk_pos in E.
           destruct (Bool.bool_dec (dark r (file p)) true).
           ++ discriminate.
           ++ contradiction.
      * simpl. destruct (mk_pos r f); [right|]; apply IH; assumption.
Qed.

(* Helper lemma: filter preserves NoDup *)
Lemma filter_nodup : forall A (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros A f l Hnd.
  induction Hnd.
  - constructor.
  - simpl. destruct (f x).
    + constructor.
      * intro Hin. apply filter_In in Hin. destruct Hin. contradiction.
      * assumption.
    + assumption.
Qed.

(* Helper for fold_right with option *)
Lemma fold_right_cons_in : forall A B (f : A -> option B) (l : list A) (acc : list B) (b : B),
  In b (fold_right (fun a acc => match f a with Some x => x :: acc | None => acc end) acc l) ->
  (exists a, f a = Some b /\ In a l) \/ In b acc.
Proof.
  induction l as [|h t IH]; intros acc b Hin.
  - right. exact Hin.
  - simpl in Hin.
    destruct (f h) eqn:E.
    + destruct Hin as [Hin|Hin].
      * left. exists h. split; [congruence | left; reflexivity].
      * apply IH in Hin. destruct Hin as [[a [Ha1 Ha2]]|Hin].
        -- left. exists a. split; [assumption | right; assumption].
        -- right. assumption.
    + apply IH in Hin. destruct Hin as [[a [Ha1 Ha2]]|Hin].
      * left. exists a. split; [assumption | right; assumption].
      * right. assumption.
Qed.

(* Helper: positions_in_rank has exactly 4 elements *)
Lemma positions_in_rank_length : forall r,
  length (positions_in_rank r) = 4%nat.
Proof.
  intro r.
  unfold positions_in_rank.
  assert (Hdark: forall f, In f (dark_files_for_rank r) -> dark r f = true).
  {
    intros f Hin.
    unfold dark_files_for_rank in Hin.
    apply filter_In in Hin.
    destruct Hin. assumption.
  }
  assert (H: forall fs,
    (forall f, In f fs -> dark r f = true) ->
    forall acc,
    length (fold_right (fun f acc =>
      match mk_pos r f with
      | Some p => p :: acc
      | None => acc
      end) acc fs) = (length fs + length acc)%nat).
  {
    induction fs as [|f fs IH]; intros Hfs acc.
    - reflexivity.
    - simpl.
      assert (dark r f = true) by (apply Hfs; left; reflexivity).
      unfold mk_pos.
      destruct (Bool.bool_dec (dark r f) true) as [E|E].
      + simpl. rewrite IH.
        * reflexivity.
        * intros. apply Hfs. right. assumption.
      + congruence.
  }
  rewrite H.
  - simpl. rewrite dark_files_count. reflexivity.
  - apply Hdark.
Qed.

(* Completeness of enum_pos *)
Lemma enum_pos_complete : forall p : Position, In p enum_pos.
Proof.
  intro p.
  unfold enum_pos.
  apply in_flat_map.
  exists (rank p).
  split.
  - apply fin8_in_enum.
  - apply positions_in_rank_correct.
    split; [reflexivity | apply position_is_dark].
Qed.

(* Helper: NoDup for positions_in_rank *)
Lemma positions_in_rank_nodup : forall r,
  NoDup (positions_in_rank r).
Proof.
  intro r.
  unfold positions_in_rank.
  assert (H: forall fs acc,
    NoDup acc ->
    (forall p, In p acc -> ~In (file p) fs) ->
    NoDup fs ->
    NoDup (fold_right (fun f acc =>
      match mk_pos r f with
      | Some p => p :: acc
      | None => acc
      end) acc fs)).
  {
    induction fs as [|f fs IH]; intros acc Hacc Hdisj Hfs.
    - assumption.
    - simpl. inv Hfs.
      destruct (mk_pos r f) eqn:E.
      + constructor.
        * intro Hin.
          assert (Hrf: rank p = r /\ file p = f) by (apply mk_pos_some_inv; assumption).
          destruct Hrf as [Hr Hf].
          apply fold_right_cons_in in Hin.
          destruct Hin as [[f' [Heq Hfin]]|Hin].
          -- destruct (mk_pos r f') as [p'|] eqn:E' in Heq.
             ++ injection Heq as <-.
                apply mk_pos_some_inv in E'.
                destruct E' as [_ Hf'].
                subst. contradiction.
             ++ discriminate.
          -- apply (Hdisj p Hin). subst. left. reflexivity.
        * apply IH.
          ++ assumption.
          ++ intros p' Hp'.
             intro Hcontra.
             apply (Hdisj p'); [assumption | right; assumption].
          ++ assumption.
      + apply IH; [assumption| |assumption].
        intros p' Hp' Hcontra.
        apply (Hdisj p'); [assumption | right; assumption].
  }
  apply H.
  - constructor.
  - intros p [].
  - unfold dark_files_for_rank.
    apply filter_nodup. apply enum_fin8_nodup.
Qed.

(* Helper for NoDup_app *)
Lemma NoDup_app : forall A (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|h t IH]; intros l2 H1 H2 Hdisj.
  - exact H2.
  - simpl. inv H1. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * contradiction.
      * apply (Hdisj h); [left; reflexivity | assumption].
    + apply IH; [assumption | assumption |].
      intros x Hx1 Hx2. apply (Hdisj x); [right; assumption | assumption].
Qed.

(* Helper for flat_map NoDup *)
Lemma flat_map_nodup : forall A B (f : A -> list B) (l : list A),
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x y, In x l -> In y l -> x <> y ->
    forall b, In b (f x) -> In b (f y) -> False) ->
  NoDup (flat_map f l).
Proof.
  induction l as [|h t IH]; intros Hl Hf Hdisj.
  - constructor.
  - simpl. inv Hl.
    apply NoDup_app.
    + apply Hf. left. reflexivity.
    + apply IH; [assumption| |].
      * intros x Hx. apply Hf. right. assumption.
      * intros x y Hx Hy Hneq.
        apply (Hdisj x y); [right; assumption | right; assumption | assumption].
    + intros b Hb1 Hb2.
      apply in_flat_map in Hb2.
      destruct Hb2 as [a [Ha1 Ha2]].
      refine (Hdisj h a _ _ _ b Hb1 Ha2).
      * left. reflexivity.
      * right. assumption.
      * intro Heq. subst. contradiction.
Qed.

(* NoDup property for enum_pos *)
Lemma enum_pos_nodup : NoDup enum_pos.
Proof.
  unfold enum_pos.
  apply flat_map_nodup.
  - apply enum_fin8_nodup.
  - intros. apply positions_in_rank_nodup.
  - intros r1 r2 Hr1 Hr2 Hneq p Hp1 Hp2.
    apply positions_in_rank_correct in Hp1.
    apply positions_in_rank_correct in Hp2.
    destruct Hp1 as [H1 _].
    destruct Hp2 as [H2 _].
    congruence.
Qed.


(* Helper for flat_map length *)
Lemma flat_map_length : forall A B (f : A -> list B) (l : list A) (n : nat),
  (forall x, In x l -> length (f x) = n) ->
  length (flat_map f l) = (length l * n)%nat.
Proof.
  induction l as [|h t IH]; intros n Hlen.
  - reflexivity.
  - simpl. rewrite app_length. rewrite Hlen; [|left; reflexivity].
    rewrite (IH n).
    + simpl. rewrite Nat.add_comm. simpl. reflexivity.
    + intros x Hx. apply Hlen. right. assumption.
Qed.

(* Cardinality of enum_pos is 32 *)
Lemma enum_pos_length : length enum_pos = 32%nat.
Proof.
  unfold enum_pos.
  rewrite flat_map_length with (n := 4%nat).
  - simpl. reflexivity.
  - intros. apply positions_in_rank_length.
Qed.

(* Safe coordinate offset operation - complete version *)
Definition off (p : Position) (dr df : Z) : option Position :=
  let r := rankZ (rank p) in
  let f := fileZ (file p) in
  let r' := r + dr in
  let f' := f + df in
  if (0 <=? r') && (r' <? 8) && (0 <=? f') && (f' <? 8) then
    match Z.to_nat r', Z.to_nat f' with
    | r_nat, f_nat =>
      match lt_dec r_nat 8, lt_dec f_nat 8 with
      | left Hr, left Hf => mk_pos (@fin8_of_nat r_nat Hr) (@fin8_of_nat f_nat Hf)
      | _, _ => None
      end
    end
  else None.

(* Instance for Finite Position *)
Program Instance Finite_Position : Finite Position := {
  enum := enum_pos
}.
Next Obligation.
  apply enum_pos_complete.
Defined.
Next Obligation.
  apply enum_pos_nodup.
Defined.
(* ========================================================================= *)
(* SECTION 4: CORE GAME ONTOLOGY                                            *)
(* ========================================================================= *)

Inductive Color :=
| Dark
| Light.

Inductive PieceKind :=
| Man
| King.

Record Piece := mkPiece {
  pc_color : Color;
  pc_kind : PieceKind
}.

Definition opp (c : Color) : Color :=
  match c with
  | Dark => Light
  | Light => Dark
  end.

Lemma opp_involutive : forall c, opp (opp c) = c.
Proof.
  destruct c; reflexivity.
Qed.

Instance Color_eq_dec : EqDec Color eq.
Proof.
  intros x y.
  destruct x, y; (left; reflexivity) || (right; discriminate).
Defined.

Instance PieceKind_eq_dec : EqDec PieceKind eq.
Proof.
  intros x y.
  destruct x, y; (left; reflexivity) || (right; discriminate).
Defined.

Instance Piece_eq_dec : EqDec Piece eq.
Proof.
  intros [xc xk] [yc yk].
  destruct (Color_eq_dec xc yc) as [Hc|Hc],
           (PieceKind_eq_dec xk yk) as [Hk|Hk].
  - rewrite Hc. rewrite Hk. left. reflexivity.
  - rewrite Hc. right. intro Heq. inversion Heq. contradiction.
  - rewrite Hk. right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
Defined.

Program Instance Finite_Color : Finite Color := {
  enum := [Dark; Light]
}.

(* Complete Finite_Color instance *)
Next Obligation.
  destruct x; simpl; auto.
Defined.
Next Obligation.
  repeat constructor; simpl; intuition discriminate.
Defined.

(* Finite instance for PieceKind *)
Program Instance Finite_PieceKind : Finite PieceKind := {
  enum := [Man; King]
}.
Next Obligation.
  destruct x; simpl; auto.
Defined.
Next Obligation.
  repeat constructor; simpl; intuition discriminate.
Defined.

(* Exhaustiveness lemmas for case analysis *)
Lemma Color_cases : forall (P : Color -> Prop),
  P Dark -> P Light -> forall c, P c.
Proof.
  intros P HD HL c.
  destruct c; assumption.
Qed.

Lemma PieceKind_cases : forall (P : PieceKind -> Prop),
  P Man -> P King -> forall k, P k.
Proof.
  intros P HM HK k.
  destruct k; assumption.
Qed.

(* Validation example with exact name from spec *)
Example opposite_color_involutive : forall c, opp (opp c) = c.
Proof.
  apply opp_involutive.
Qed.

(* ========================================================================= *)
(* SECTION 5: BOARD ABSTRACTION                                             *)
(* ========================================================================= *)

(* Board as total map from positions to optional pieces *)
Definition Board := Position -> option Piece.

(* Board extensional equality *)
Definition board_eq (b1 b2 : Board) : Prop :=
  forall p : Position, b1 p = b2 p.

(* Notation for board equality *)
Notation "b1 ≈ b2" := (board_eq b1 b2) (at level 70).

(* Prove that board_eq is an equivalence relation *)
Instance Board_Equivalence : Equivalence board_eq.
Proof.
  constructor.
  - (* reflexive *)
    unfold Reflexive, board_eq. intros b p. reflexivity.
  - (* symmetric *)
    unfold Symmetric, board_eq. intros b1 b2 H p. symmetry. apply H.
  - (* transitive *)
    unfold Transitive, board_eq. intros b1 b2 b3 H12 H23 p.
    rewrite H12. apply H23.
Qed.

(* Setoid instance for board equality *)
Instance Board_Setoid : Setoid Board := {
  equiv := board_eq
}.

(* Decidable equality for Position *)
Instance Position_eq_dec : EqDec Position eq.
Proof.
  intros p1 p2.
  destruct (Fin_eq_dec (rank p1) (rank p2)) as [Hr|Hr],
           (Fin_eq_dec (file p1) (file p2)) as [Hf|Hf].
  - left. apply position_eq; assumption.
  - right. intro H. apply Hf. rewrite <- H. reflexivity.
  - right. intro H. apply Hr. rewrite <- H. reflexivity.
  - right. intro H. apply Hr. rewrite <- H. reflexivity.
Defined.

(* Board update operation *)
Definition board_set (b : Board) (p : Position) (pc : option Piece) : Board :=
  fun p' => if equiv_dec p p' then pc else b p'.

(* Board get operation *)
Definition board_get (b : Board) (p : Position) : option Piece :=
  b p.
  
(* Update property: idempotence *)
Lemma board_set_idempotent : forall b p pc,
  board_set (board_set b p pc) p pc ≈ board_set b p pc.
Proof.
  unfold board_eq, board_set. intros b p pc p'.
  destruct (equiv_dec p p'); reflexivity.
Qed.

(* Update property: commutativity on distinct squares *)
Lemma board_set_commute : forall b p1 p2 pc1 pc2,
  p1 <> p2 ->
  board_set (board_set b p1 pc1) p2 pc2 ≈ board_set (board_set b p2 pc2) p1 pc1.
Proof.
  unfold board_eq, board_set. intros b p1 p2 pc1 pc2 Hneq p.
  destruct (equiv_dec p1 p) as [H1|H1], (equiv_dec p2 p) as [H2|H2]; try reflexivity.
  exfalso. apply Hneq. 
  unfold equiv in H1, H2. simpl in H1, H2.
  congruence.
Qed.

(* Board predicates *)
Definition occupied (b : Board) (p : Position) : bool :=
  match b p with
  | Some _ => true
  | None => false
  end.
  
Definition occupied_by (b : Board) (c : Color) (p : Position) : bool :=
  match b p with
  | Some pc => if Color_eq_dec (pc_color pc) c then true else false
  | None => false
  end.
  
(* Helper to convert index to rank and file *)
Definition index_to_coords (n : nat) : option (Rank * File) :=
  match n with
  | O => None
  | S n' => 
    if Nat.leb (S n') 32 then
      let idx := n' in (* 0-based index *)
      let r := Nat.div idx 4 in
      let f_offset := Nat.mul (Nat.modulo idx 4) 2 in
      let f := if Nat.even r then S f_offset else f_offset in
      match lt_dec r 8, lt_dec f 8 with
      | left Hr, left Hf => Some (@fin8_of_nat r Hr, @fin8_of_nat f Hf)
      | _, _ => None
      end
    else None
  end.
  
(* Convert bounded index (1..32) to Position *)
Definition pos_of_index (n : {x : nat | (1 <= x)%nat /\ (x <= 32)%nat}) : option Position :=
  match index_to_coords (proj1_sig n) with
  | Some (r, f) => mk_pos r f
  | None => None
  end.
  
(* Helper: get square index (1..32) from a Position *)
Definition sq_index (p : Position) : nat :=
  let r := fin8_to_nat (rank p) in
  let f := fin8_to_nat (file p) in
  (* Calculate the index based on standard checkers numbering *)
  let row_base := Nat.mul r 4 in
  let col_offset := Nat.div (if Nat.even r then f else S f) 2 in
  S (row_base + col_offset).
  
(* Initial board setup *)
Definition initial_board : Board :=
  fun p =>
    let idx := sq_index p in
    if Nat.leb idx 12 then
      Some {| pc_color := Dark; pc_kind := Man |}
    else if andb (Nat.leb 21 idx) (Nat.leb idx 32) then
      Some {| pc_color := Light; pc_kind := Man |}
    else
      None.
      
(* Validation example for Section 5 *)
Example board_update_retrieve :
  forall b p pc, board_get (board_set b p (Some pc)) p = Some pc.
Proof.
  intros b p pc.
  unfold board_get, board_set.
  destruct (equiv_dec p p) as [H|H].
  - reflexivity.
  - exfalso. apply H. reflexivity.
Qed.
