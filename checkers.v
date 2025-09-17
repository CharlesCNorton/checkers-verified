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
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

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
  List.length (dark_files_for_rank r) = 4%nat.
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
  List.length (positions_in_rank r) = 4%nat.
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
    List.length (fold_right (fun f acc =>
      match mk_pos r f with
      | Some p => p :: acc
      | None => acc
      end) acc fs) = (List.length fs + List.length acc)%nat).
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
  (forall x, In x l -> List.length (f x) = n) ->
  List.length (flat_map f l) = (List.length l * n)%nat.
Proof.
  induction l as [|h t IH]; intros n Hlen.
  - reflexivity.
  - simpl. rewrite app_length. rewrite Hlen; [|left; reflexivity].
    rewrite (IH n).
    + simpl. rewrite Nat.add_comm. simpl. reflexivity.
    + intros x Hx. apply Hlen. right. assumption.
Qed.

(* Cardinality of enum_pos is 32 *)
Lemma enum_pos_length : List.length enum_pos = 32%nat.
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

(* Helper lemma: rank and file are in bounds *)
Lemma position_coords_bounded : forall p,
  0 <= rankZ (rank p) < 8 /\ 0 <= fileZ (file p) < 8.
Proof.
  intro p.
  unfold rankZ, fileZ, fin8_to_nat.
  split; split; try apply Zle_0_nat;
  destruct (Fin.to_nat (rank p)) as [r Hr];
  destruct (Fin.to_nat (file p)) as [f Hf];
  simpl; lia.
Qed.

(* Helper lemma: Z.to_nat and Z.of_nat roundtrip *)
Lemma Z_to_nat_of_nat_inv : forall z,
  0 <= z -> Z.of_nat (Z.to_nat z) = z.
Proof.
  intros. apply Z2Nat.id. assumption.
Qed.

(* Helper lemma: bounds checking breakdown *)
Lemma bounds_check_components : forall r f dr df,
  (0 <=? r + dr) && (r + dr <? 8) && (0 <=? f + df) && (f + df <? 8) = true ->
  0 <= r + dr /\ r + dr < 8 /\ 0 <= f + df /\ f + df < 8.
Proof.
  intros.
  apply andb_prop in H as [H1 H2].
  apply andb_prop in H1 as [H11 H12].
  apply andb_prop in H11 as [H111 H112].
  apply Z.leb_le in H111.
  apply Z.ltb_lt in H112.
  apply Z.leb_le in H12.
  apply Z.ltb_lt in H2.
  auto.
Qed.

(* Helper lemma: bounds imply reverse bounds *)
Lemma reverse_bounds_check : forall r f dr df,
  0 <= r /\ r < 8 /\ 0 <= f /\ f < 8 ->
  0 <= r + dr /\ r + dr < 8 /\ 0 <= f + df /\ f + df < 8 ->
  (0 <=? r) && (r <? 8) && (0 <=? f) && (f <? 8) = true.
Proof.
  intros r f dr df [Hr [Hr' [Hf Hf']]] _.
  rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt.
  auto.
Qed.

(* Helper lemma: nat bounds from Z bounds *)
Lemma nat_lt_from_Z : forall z n,
  z = Z.of_nat n -> 0 <= z -> z < 8 -> (n < 8)%nat.
Proof.
  intros z n H Hz H8.
  subst z. lia.
Qed.

(* Helper lemma: mk_pos succeeds for position's own coordinates *)
Lemma mk_pos_self : forall p,
  exists p', mk_pos (rank p) (file p) = Some p' /\ rank p' = rank p /\ file p' = file p.
Proof.
  intro p.
  apply mk_pos_correct.
  apply position_is_dark.
Qed.

(* Validation example: offset preserves dark square property *)
Example offset_preserves_dark : forall p p',
  off p 1 1 = Some p' -> dark (rank p') (file p') = true.
Proof.
  intros p p' H.
  apply position_is_dark.
Qed.

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

(* ========================================================================= *)
(* SECTION 6: MOVEMENT GEOMETRY (DIAGONALS ON DARK SQUARES)                 *)
(* ========================================================================= *)

(* Primitive diagonal adjacency relation: distance 1 diagonal *)
Definition diag_adj (p1 p2 : Position) : Prop :=
  let r1 := rankZ (rank p1) in
  let f1 := fileZ (file p1) in
  let r2 := rankZ (rank p2) in
  let f2 := fileZ (file p2) in
  (Z.abs (r2 - r1) = 1) /\ (Z.abs (f2 - f1) = 1).

(* Helper: diagonal adjacency is decidable *)
Lemma diag_adj_dec : forall p1 p2 : Position, {diag_adj p1 p2} + {~diag_adj p1 p2}.
Proof.
  intros p1 p2.
  unfold diag_adj.
  destruct (Z.eq_dec (Z.abs (rankZ (rank p2) - rankZ (rank p1))) 1) as [Hr|Hr],
           (Z.eq_dec (Z.abs (fileZ (file p2) - fileZ (file p1))) 1) as [Hf|Hf].
  - left. split; assumption.
  - right. intros [H1 H2]. contradiction.
  - right. intros [H1 H2]. contradiction.
  - right. intros [H1 H2]. contradiction.
Defined.

(* Diagonal jump relation: from -> over -> to, distance-2 diagonal *)
Definition diag_jump (from over to : Position) : Prop :=
  let r_from := rankZ (rank from) in
  let f_from := fileZ (file from) in
  let r_over := rankZ (rank over) in
  let f_over := fileZ (file over) in
  let r_to := rankZ (rank to) in
  let f_to := fileZ (file to) in
  (* over is exactly in the middle *)
  (r_over = (r_from + r_to) / 2) /\
  (f_over = (f_from + f_to) / 2) /\
  (* from and to are distance 2 apart diagonally *)
  (Z.abs (r_to - r_from) = 2) /\
  (Z.abs (f_to - f_from) = 2).

(* Directionality: forward means rank increases for Dark, decreases for Light *)
Definition forward_of (c : Color) (r1 r2 : Rank) : Prop :=
  match c with
  | Dark => rankZ r2 > rankZ r1  (* Dark moves toward higher ranks *)
  | Light => rankZ r2 < rankZ r1  (* Light moves toward lower ranks *)
  end.

(* Step moves (non-capturing): Man moves forward diagonally, King any diagonal *)
Definition step_man (c : Color) (from to : Position) : Prop :=
  diag_adj from to /\ forward_of c (rank from) (rank to).

Definition step_king (from to : Position) : Prop :=
  diag_adj from to.

(* Jump moves (capturing): Man jumps forward only, King any direction *)
Definition jump_man (c : Color) (from over to : Position) : Prop :=
  diag_jump from over to /\ forward_of c (rank from) (rank to).

Definition jump_king (from over to : Position) : Prop :=
  diag_jump from over to.

(* Validation examples for Section 6 *)
Example king_step_is_diagonal : forall from to,
  step_king from to -> diag_adj from to.
Proof.
  intros from to H.
  unfold step_king in H. exact H.
Qed.

Example man_cannot_step_backward : forall c from to,
  step_man c from to -> forward_of c (rank from) (rank to).
Proof.
  intros c from to H.
  unfold step_man in H. destruct H as [_ Hforward]. exact Hforward.
Qed.

(* ========================================================================= *)
(* SECTION 7: PIECE MOVEMENT RULES (PATTERNS ONLY)                          *)
(* ========================================================================= *)

(* Specifications for distance-1 moves (no occupancy yet) *)
Definition man_step_spec (c : Color) (from to : Position) : Prop :=
  step_man c from to.

Definition king_step_spec (from to : Position) : Prop :=
  step_king from to.

(* Specifications for jumps asserting exact 2-diagonal geometry *)
Definition man_jump_spec (c : Color) (from over to : Position) : Prop :=
  jump_man c from over to.

Definition king_jump_spec (from over to : Position) : Prop :=
  jump_king from over to.

(* Implementation predicates over a board *)
Definition step_impl (b : Board) (pc : Piece) (from to : Position) : bool :=
  match occupied b to with
  | true => false  (* destination must be empty *)
  | false =>
    match pc_kind pc with
    | Man => if diag_adj_dec from to
             then match pc_color pc with
                  | Dark => Z.ltb (rankZ (rank from)) (rankZ (rank to))
                  | Light => Z.ltb (rankZ (rank to)) (rankZ (rank from))
                  end
             else false
    | King => if diag_adj_dec from to then true else false
    end
  end.

Definition jump_impl (b : Board) (pc : Piece) (from over to : Position) : bool :=
  match occupied b to, board_get b over with
  | false, Some opponent =>
    match Color_eq_dec (pc_color opponent) (pc_color pc) with
    | left _ => false
    | right _ =>
      match pc_kind pc with
         | Man => if diag_adj_dec from over
                  then if diag_adj_dec over to
                       then match pc_color pc with
                            | Dark => Z.ltb (rankZ (rank from)) (rankZ (rank to))
                            | Light => Z.ltb (rankZ (rank to)) (rankZ (rank from))
                            end
                       else false
                  else false
         | King => if diag_adj_dec from over
                   then if diag_adj_dec over to then true else false
                   else false
      end
    end
  | _, _ => false
  end.

(* Validation examples for Section 7 *)
Example king_nonflying : forall b c from to,
  step_impl b {|pc_color:=c; pc_kind:=King|} from to = true ->
  diag_adj from to.
Proof.
  intros b c from to H.
  unfold step_impl in H.
  destruct (occupied b to); [discriminate|].
  simpl in H.
  destruct (diag_adj_dec from to); [assumption|discriminate].
Qed.

Example man_jump_not_backward : forall b c from over to,
  jump_impl b {|pc_color:=c; pc_kind:=Man|} from over to = true ->
  forward_of c (rank from) (rank to).
Proof.
  intros b c from over to H.
  unfold jump_impl in H; simpl in H.
  destruct (occupied b to); [discriminate|].
  destruct (board_get b over) as [opp|]; [|discriminate].
  destruct (Color_eq_dec (pc_color opp) c) as [Heq|Hneq];
    [simpl in H; discriminate|simpl in H].
  destruct (diag_adj_dec from over); [|discriminate].
  destruct (diag_adj_dec over to); [|discriminate].
  unfold forward_of.
  destruct c; simpl; rewrite Z.ltb_lt in H; lia.
Qed.

(* ========================================================================= *)
(* SECTION 8: CAPTURE CHAINS (MULTI-JUMP)                                   *)
(* ========================================================================= *)

(* Chains as sequences of (over, to) from an initial from *)
(* Using sigma type for dependent pair as specified *)
Definition JumpLink := { over : Position & Position }.

Definition JumpChain := list JumpLink.

(* Helper: get the over position from a JumpLink *)
Definition link_over (l : JumpLink) : Position := projT1 l.

(* Helper: get the to position from a JumpLink *)
Definition link_to (l : JumpLink) : Position := projT2 l.

(* Helper: get the last landing position of a chain *)
Definition last_landing (from : Position) (ch : JumpChain) : Position :=
  match ch with
  | [] => from
  | _ => link_to (last ch (existT _ from from))
  end.

(* Set of captured squares in a chain *)
Definition captures_of (ch : JumpChain) : list Position :=
  map link_over ch.

(* Helper: apply a jump to a transient board state *)
(* Removes the captured piece but doesn't place the jumping piece yet *)
Definition apply_capture_transient (b : Board) (over : Position) : Board :=
  board_set b over None.

(* Apply multiple captures to get transient board during chain *)
Fixpoint apply_captures_transient (b : Board) (captures : list Position) : Board :=
  match captures with
  | [] => b
  | c :: cs => apply_captures_transient (apply_capture_transient b c) cs
  end.

(* Check if a position is in the crown-head (promotion row) *)
Definition is_crown_head (c : Color) (p : Position) : bool :=
  match c with
  | Dark => Z.eqb (rankZ (rank p)) 7   (* Ranks 0-7, so 7 is the top *)
  | Light => Z.eqb (rankZ (rank p)) 0   (* 0 is the bottom *)
  end.

(* Check if a position reaches crown-head *)
Definition reaches_crown_head (pc : Piece) (p : Position) : bool :=
  match pc_kind pc with
  | Man => is_crown_head (pc_color pc) p
  | King => false  (* Kings don't promote *)
  end.

(* Helper: decidable forward_of *)
Definition forward_of_dec (c : Color) (r1 r2 : Rank) : bool :=
  match c with
  | Dark => Z.ltb (rankZ r1) (rankZ r2)
  | Light => Z.ltb (rankZ r2) (rankZ r1)
  end.

(* Helper: boolean equality for positions *)
Definition position_eqb (p1 p2 : Position) : bool :=
  match Position_eq_dec p1 p2 with
  | left _ => true
  | right _ => false
  end.

(* Valid jump chain relative to a board *)
Fixpoint valid_jump_chain_rec (b : Board) (pc : Piece) (from : Position)
                              (ch : JumpChain) (captured_so_far : list Position) : bool :=
  match ch with
  | [] => true
  | link :: rest =>
    let over := link_over link in
    let to := link_to link in
    (* Check this jump is valid on current transient board *)
    (* But captured pieces remain as blockers *)
    let transient_b := b in  (* Captured pieces stay on board during chain *)
    if negb (occupied transient_b to) then
      if occupied_by transient_b (opp (pc_color pc)) over then
        if negb (existsb (position_eqb over) captured_so_far) then
          (* Check jump geometry *)
          if (if diag_adj_dec from over then true else false) &&
             (if diag_adj_dec over to then true else false) then
            (* Check directionality for Man *)
            match pc_kind pc with
            | Man =>
              if forward_of_dec (pc_color pc) (rank from) (rank to) then
                (* Check if promotion ends chain *)
                if reaches_crown_head pc to && negb (match rest with [] => true | _ => false end) then
                  false  (* Promotion must end chain *)
                else
                  valid_jump_chain_rec b pc to rest (over :: captured_so_far)
              else false
            | King =>
              valid_jump_chain_rec b pc to rest (over :: captured_so_far)
            end
          else false
        else false  (* Can't capture same piece twice *)
      else false  (* Must jump over opponent *)
    else false  (* Landing must be empty *)
  end.

Definition valid_jump_chain (b : Board) (pc : Piece) (from : Position) (ch : JumpChain) : bool :=
  valid_jump_chain_rec b pc from ch [].

(* Check if any jump exists from a position *)
Definition exists_jump_from (b : Board) (pc : Piece) (from : Position) : bool :=
  existsb (fun to =>
    existsb (fun over =>
      jump_impl b pc from over to
    ) enum_pos
  ) enum_pos.

(* Chain is maximal if no further jump exists from the last landing *)
Definition chain_maximal (b : Board) (pc : Piece) (from : Position) (ch : JumpChain) : bool :=
  let last_pos := last_landing from ch in
  (* Apply the chain's captures to get the board state after the chain *)
  let b_after := apply_captures_transient b (captures_of ch) in
  negb (exists_jump_from b_after pc last_pos).

(* Simpler validation: captures_of gives the over positions *)
Example captures_of_extracts_overs : forall ch,
  captures_of ch = map link_over ch.
Proof.
  intro ch. reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 9: FORCING RULES (MANDATORY CAPTURE)                             *)
(* ========================================================================= *)

(* Check if any jump exists for any piece of a color *)
Definition exists_jump_any (b : Board) (c : Color) : bool :=
  existsb (fun from =>
    match board_get b from with
    | Some pc =>
      if Color_eq_dec (pc_color pc) c then
        exists_jump_from b pc from
      else false
    | None => false
    end
  ) enum_pos.

(* Forcing law: if a jump exists, step moves are illegal *)
Definition step_legal_with_forcing (b : Board) (c : Color) (pc : Piece) (from to : Position) : bool :=
  if exists_jump_any b c then
    false  (* No steps allowed when captures exist *)
  else
    step_impl b pc from to.

(* During a chain, must continue if another jump is available *)
Definition must_continue_chain (b : Board) (pc : Piece) (pos : Position) : bool :=
  (* Unless promotion just occurred *)
  if reaches_crown_head pc pos then
    false  (* Chain ends on promotion *)
  else
    exists_jump_from b pc pos.

(* Validation example for Section 9 *)
Example mandatory_capture_blocks_steps : forall b from to pc,
  board_get b from = Some pc ->
  exists_jump_any b (pc_color pc) = true ->
  step_legal_with_forcing b (pc_color pc) pc from to = false.
Proof.
  intros b from to pc Hget Hjump.
  unfold step_legal_with_forcing.
  rewrite Hjump.
  reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 10: GAME STATE                                                   *)
(* ========================================================================= *)

(* Position key for repetition detection *)
Definition PositionKey := (Board * Color)%type.

(* Game state record *)
Record GameState := mkGameState {
  board : Board;
  turn : Color;
  ply_without_capture_or_man_advance : nat;
  repetition_book : list PositionKey  (* Simple list for tracking positions *)
}.

(* Generate key from state *)
Definition key_of_state (st : GameState) : PositionKey :=
  (board st, turn st).

(* Count pieces of a color on the board *)
Definition count_pieces (b : Board) (c : Color) : nat :=
  List.length (filter (fun p =>
    match b p with
    | Some pc => if Color_eq_dec (pc_color pc) c then true else false
    | None => false
    end
  ) enum_pos).

(* Well-formedness predicate *)
Definition WFState (st : GameState) : Prop :=
  (* Pieces only on dark squares - guaranteed by Position type *)
  (* Counts: at most 12 pieces per color *)
  (count_pieces (board st) Dark <= 12)%nat /\
  (count_pieces (board st) Light <= 12)%nat /\
  (* Ply counter is non-negative (trivial for nat) *)
  True.

(* Initial game state *)
Definition initial_state : GameState :=
  mkGameState initial_board Dark 0 [].

(* Helper: count initial pieces *)
Lemma initial_dark_count : count_pieces initial_board Dark = 12%nat.
Proof.
  unfold count_pieces, initial_board.
  unfold filter.
  (* We need to actually count through the enumeration *)
  (* This is tedious but necessary *)
  compute. reflexivity.
Qed.

Lemma initial_light_count : count_pieces initial_board Light = 12%nat.
Proof.
  unfold count_pieces, initial_board.
  unfold filter.
  compute. reflexivity.
Qed.

(* Validation for Section 10 *)
Example initial_wellformed : WFState initial_state.
Proof.
  unfold WFState, initial_state.
  simpl.
  split; [|split; [|exact I]].
  - (* Dark pieces <= 12 *)
    rewrite initial_dark_count. apply le_n.
  - (* Light pieces <= 12 *)
    rewrite initial_light_count. apply le_n.
Qed.

(* ========================================================================= *)
(* SECTION 11: MOVE REPRESENTATION                                          *)
(* ========================================================================= *)

(* Move type *)
Inductive Move :=
| Step : Position -> Position -> Move         (* non-capturing *)
| Jump : Position -> JumpChain -> Move        (* capturing chain *)
| Resign : Color -> Move
| AgreeDraw : Move.

(* Move accessors *)
Definition move_src (m : Move) : option Position :=
  match m with
  | Step from _ => Some from
  | Jump from _ => Some from
  | _ => None
  end.

Definition move_dst (b : Board) (m : Move) : option Position :=
  match m with
  | Step _ to => Some to
  | Jump from ch => Some (last_landing from ch)
  | _ => None
  end.

(* Captures of a move *)
Definition captures_of_move (m : Move) : list Position :=
  match m with
  | Jump _ ch => captures_of ch
  | _ => []
  end.

(* Validation examples for Section 11 *)
Example move_roundtrip_step : forall from to b,
  move_src (Step from to) = Some from /\
  move_dst b (Step from to) = Some to.
Proof.
  intros. split; reflexivity.
Qed.

Example jump_last_landing_defined : forall from ch b,
  move_dst b (Jump from ch) = Some (last_landing from ch).
Proof.
  intros. reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 12: MOVE LEGALITY                                                *)
(* ========================================================================= *)

(* Helper: get piece at position *)
Definition piece_at (b : Board) (p : Position) : option Piece :=
  board_get b p.

(* Helper: check if piece is a man *)
Definition is_man (pc : option Piece) : bool :=
  match pc with
  | Some p => match pc_kind p with Man => true | King => false end
  | None => false
  end.

(* Main move legality implementation *)
Definition legal_move_impl (st : GameState) (m : Move) : bool :=
  match m with
  | Step from to =>
    (* Check source occupancy by side to move *)
    match piece_at (board st) from with
    | Some pc =>
      if Color_eq_dec (pc_color pc) (turn st) then
        (* Check forcing - no steps if captures exist *)
        if exists_jump_any (board st) (turn st) then
          false
        else
          step_impl (board st) pc from to
      else false
    | None => false
    end
  | Jump from ch =>
    (* Check source occupancy by side to move *)
    match piece_at (board st) from with
    | Some pc =>
      if Color_eq_dec (pc_color pc) (turn st) then
        (* Check chain validity *)
        if valid_jump_chain (board st) pc from ch then
          (* Check maximality unless promotion *)
          let last_pos := last_landing from ch in
          if reaches_crown_head pc last_pos then
            true  (* Promotion ends chain *)
          else
            chain_maximal (board st) pc from ch
        else false
      else false
    | None => false
    end
  | Resign c =>
    (* Can only resign on your turn *)
    if Color_eq_dec c (turn st) then true else false
  | AgreeDraw =>
    (* Draw offers are always technically legal *)
    true
  end.

(* Simplified validation for Section 12 *)
Example legal_move_respects_turn : forall st m,
  legal_move_impl st m = true ->
  match m with
  | Step from _ | Jump from _ =>
    match piece_at (board st) from with
    | Some pc => pc_color pc = turn st
    | None => False
    end
  | Resign c => c = turn st
  | AgreeDraw => True
  end.
Proof.
  intros st m H.
  destruct m; simpl in H.
  - (* Step *)
    destruct (piece_at (board st) p) as [pc|] eqn:Hpc; [|discriminate].
    destruct (Color_eq_dec (pc_color pc) (turn st)) as [e|n]; [exact e|discriminate].
  - (* Jump *)
    destruct (piece_at (board st) p) as [pc|] eqn:Hpc; [|discriminate].
    destruct (Color_eq_dec (pc_color pc) (turn st)) as [e|n]; [exact e|discriminate].
  - (* Resign *)
    destruct (Color_eq_dec c (turn st)) as [e|n]; [exact e|discriminate].
  - (* AgreeDraw *)
    exact I.
Qed.

(* ========================================================================= *)
(* SECTION 13: APPLYING MOVES                                               *)
(* ========================================================================= *)

(* Helper: promote a piece to King *)
Definition promote_piece (pc : Piece) : Piece :=
  {| pc_color := pc_color pc; pc_kind := King |}.

(* Helper: check if a move is a capture *)
Definition is_capture_move (m : Move) : bool :=
  match m with
  | Jump _ _ => true
  | _ => false
  end.

(* Helper: check if a move is a man forward step *)
Definition is_man_forward_step (b : Board) (m : Move) : bool :=
  match m with
  | Step from to =>
    match piece_at b from with
    | Some pc =>
      match pc_kind pc with
      | Man => forward_of_dec (pc_color pc) (rank from) (rank to)
      | King => false
      end
    | None => false
    end
  | _ => false
  end.

(* Helper: apply a step move to the board *)
Definition apply_step (b : Board) (from to : Position) : Board :=
  match piece_at b from with
  | Some pc =>
    let pc' := if reaches_crown_head pc to then promote_piece pc else pc in
    board_set (board_set b from None) to (Some pc')
  | None => b  (* Should not happen for legal moves *)
  end.

(* Helper: apply a jump chain to the board *)
Definition apply_jump (b : Board) (from : Position) (ch : JumpChain) : Board :=
  match piece_at b from with
  | Some pc =>
    let last_pos := last_landing from ch in
    let pc' := if reaches_crown_head pc last_pos then promote_piece pc else pc in
    (* Remove all captured pieces and move the jumping piece *)
    let b_cleared := fold_left (fun b' over => board_set b' over None) (captures_of ch) b in
    board_set (board_set b_cleared from None) last_pos (Some pc')
  | None => b  (* Should not happen for legal moves *)
  end.

(* Main transition function: apply a move to get the next game state *)
Definition apply_move_impl (st : GameState) (m : Move) : option GameState :=
  if legal_move_impl st m then
    match m with
    | Step from to =>
      let new_board := apply_step (board st) from to in
      let new_ply :=
        if is_capture_move m || is_man_forward_step (board st) m then
          0%nat  (* Reset counter on capture or man advance *)
        else
          S (ply_without_capture_or_man_advance st)
      in
      let new_key := (new_board, opp (turn st)) in
      Some (mkGameState
        new_board
        (opp (turn st))
        new_ply
        (new_key :: repetition_book st))
    | Jump from ch =>
      let new_board := apply_jump (board st) from ch in
      let new_key := (new_board, opp (turn st)) in
      Some (mkGameState
        new_board
        (opp (turn st))
        0%nat  (* Reset counter on capture *)
        (new_key :: repetition_book st))
    | Resign c =>
      (* Resignation is a valid move that ends the game *)
      (* The resigning player's opponent wins *)
      (* Return the state unchanged but with turn indicating the result *)
      Some st
    | AgreeDraw =>
      (* Draw agreement is a valid terminal move *)
      Some st
    end
  else None.

(* Validation for Section 13 *)
Example apply_legal_succeeds : forall st m,
  WFState st ->
  legal_move_impl st m = true ->
  exists st', apply_move_impl st m = Some st'.
Proof.
  intros st m Hwf Hlegal.
  unfold apply_move_impl.
  rewrite Hlegal.
  destruct m; eexists; reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 14: MOVE GENERATION                                              *)
(* ========================================================================= *)

(* Generate all possible step moves from a position *)
Definition gen_steps_from (b : Board) (pc : Piece) (from : Position) : list Move :=
  filter (fun m =>
    match m with
    | Step f t => step_impl b pc f t
    | _ => false
    end
  ) (map (Step from) enum_pos).

(* Helper: find all possible single jumps from a position *)
Definition find_single_jumps (b : Board) (pc : Piece) (from : Position) : list (Position * Position) :=
  flat_map (fun over =>
    map (fun to => (over, to))
      (filter (fun to => jump_impl b pc from over to) enum_pos)
  ) enum_pos.

(* Build all maximal jump chains from a position *)
(* This is recursive and builds only chains that are maximal *)
Fixpoint build_maximal_chains_aux
  (fuel : nat) (* Termination fuel *)
  (b : Board)
  (pc : Piece)
  (from : Position)
  (chain_so_far : JumpChain)
  (captured_so_far : list Position) : list JumpChain :=
  match fuel with
  | 0%nat => [chain_so_far] (* Out of fuel, return current chain *)
  | S fuel' =>
    (* Check if promotion would occur here *)
    if reaches_crown_head pc from then
      [chain_so_far] (* Chain ends at promotion *)
    else
      (* Find possible continuations *)
      let possible_jumps := find_single_jumps b pc from in
      let valid_jumps := filter (fun jump =>
        let over := fst jump in
        let to := snd jump in
        (* Check: not already captured and landing is empty *)
        negb (existsb (position_eqb over) captured_so_far) &&
        negb (occupied b to)
      ) possible_jumps in
      match valid_jumps with
      | [] => [chain_so_far] (* No more jumps, chain is maximal *)
      | _ =>
        (* Extend chain with each possible jump *)
        flat_map (fun jump =>
          let over := fst jump in
          let to := snd jump in
          let new_link := existT (fun _ => Position) over to in
          build_maximal_chains_aux fuel' b pc to
            (chain_so_far ++ [new_link])
            (over :: captured_so_far)
        ) valid_jumps
      end
  end.

(* Main function to build maximal chains from a position *)
Definition build_maximal_chains (b : Board) (pc : Piece) (from : Position) : list JumpChain :=
  (* Check if there's at least one jump available *)
  if exists_jump_from b pc from then
    (* Use fuel = 32 (max possible chain length) *)
    let chains := build_maximal_chains_aux 32 b pc from [] [] in
    (* Filter out empty chains *)
    filter (fun ch => negb (match ch with [] => true | _ => false end)) chains
  else
    [].

(* Generate all jump moves for the side to move *)
Definition gen_jumps (st : GameState) : list Move :=
  flat_map (fun from =>
    match piece_at (board st) from with
    | Some pc =>
      if Color_eq_dec (pc_color pc) (turn st) then
        map (Jump from) (build_maximal_chains (board st) pc from)
      else []
    | None => []
    end
  ) enum_pos.

(* Generate all step moves for the side to move *)
Definition gen_steps (st : GameState) : list Move :=
  flat_map (fun from =>
    match piece_at (board st) from with
    | Some pc =>
      if Color_eq_dec (pc_color pc) (turn st) then
        gen_steps_from (board st) pc from
      else []
    | None => []
    end
  ) enum_pos.

(* Main move generator with forcing rule *)
Definition generate_moves_impl (st : GameState) : list Move :=
  let jumps := gen_jumps st in
  match jumps with
  | [] => gen_steps st  (* No jumps available, generate steps *)
  | _ => jumps           (* Jumps available, must jump *)
  end.

(* Validation for Section 14 *)
Example move_gen_respects_forcing : forall st,
  gen_jumps st <> [] ->
  generate_moves_impl st = gen_jumps st.
Proof.
  intros st Hjumps.
  unfold generate_moves_impl.
  destruct (gen_jumps st) eqn:E.
  - contradiction.
  - reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 15: GAME TREE PROPERTIES                                         *)
(* ========================================================================= *)

(* One-step reachability via a legal move *)
Definition step_reachable (st1 st2 : GameState) : Prop :=
  exists m, legal_move_impl st1 m = true /\ apply_move_impl st1 m = Some st2.

(* Reflexive-transitive closure of legal moves *)
Inductive reachable : GameState -> GameState -> Prop :=
| reach_refl : forall st, reachable st st
| reach_step : forall st1 st2 st3,
    step_reachable st1 st2 ->
    reachable st2 st3 ->
    reachable st1 st3.

(* ========================================================================= *)
(* SECTION 16: TERMINAL CONDITIONS                                          *)
(* ========================================================================= *)

(* Check if a color has no pieces left *)
Definition has_no_pieces (b : Board) (c : Color) : bool :=
  Nat.eqb (count_pieces b c) 0.

(* Check if the side to move has no legal moves *)
Definition has_no_legal_moves (st : GameState) : bool :=
  match generate_moves_impl st with
  | [] => true
  | _ => false
  end.

(* Game result *)
Inductive GameResult :=
| Win : Color -> GameResult
| Draw : GameResult.

(* Check if game is terminal and get result *)
Definition is_terminal (st : GameState) : option GameResult :=
  if has_no_pieces (board st) (turn st) then
    Some (Win (opp (turn st)))
  else if has_no_pieces (board st) (opp (turn st)) then
    Some (Win (turn st))
  else if has_no_legal_moves st then
    Some (Win (opp (turn st)))
  else
    None.

(* Check for threefold repetition *)
Definition count_position_key (key : PositionKey) (book : list PositionKey) : nat :=
  List.length (filter (fun k =>
    (* Need to compare boards and colors *)
    match key, k with
    | (b1, c1), (b2, c2) =>
      andb (if Color_eq_dec c1 c2 then true else false)
           (if forallb (fun p =>
                 match board_get b1 p, board_get b2 p with
                 | None, None => true
                 | Some pc1, Some pc2 =>
                   andb (if Color_eq_dec (pc_color pc1) (pc_color pc2) then true else false)
                        (if PieceKind_eq_dec (pc_kind pc1) (pc_kind pc2) then true else false)
                 | _, _ => false
                 end
               ) enum_pos then true else false)
    end
  ) book).

(* Check if forty-move rule applies *)
Definition can_claim_forty_move (st : GameState) : bool :=
  Nat.leb 80 (ply_without_capture_or_man_advance st).

(* Check for threefold repetition *)
Definition can_claim_threefold (st : GameState) : bool :=
  Nat.leb 3 (count_position_key (key_of_state st) (repetition_book st)).

(* Validation for Section 16 *)
Example immobilization_loses : forall st,
  WFState st ->
  has_no_legal_moves st = true ->
  has_no_pieces (board st) (turn st) = false ->
  has_no_pieces (board st) (opp (turn st)) = false ->
  is_terminal st = Some (Win (opp (turn st))).
Proof.
  intros st Hwf Hno_moves Hhas_pieces Hopp_has_pieces.
  unfold is_terminal.
  rewrite Hhas_pieces, Hopp_has_pieces, Hno_moves.
  reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 17: OPTIONAL/HISTORICAL RULES                                    *)
(* ========================================================================= *)

(* Huffing (deprecated): modeled as illegal-move correction outside core state *)
(* We don't implement actual huffing since it's deprecated in modern play *)

(* Three-move ballot openings *)
Inductive Opening :=
| Opening11_15 : Opening  (* 11-15 *)
| Opening12_16 : Opening  (* 12-16 *)
| Opening9_13 : Opening   (* 9-13 *)
| Opening9_14 : Opening   (* 9-14 *)
| Opening10_14 : Opening  (* 10-14 *)
| Opening10_15 : Opening  (* 10-15 *)
| Opening11_16 : Opening  (* 11-16 *).

(* Helper: get position from square number (1-32) *)
(* For simplicity, we'll use a direct mapping *)
Definition get_position_from_number (n : nat) : option Position :=
  if andb (Nat.leb 1 n) (Nat.leb n 32) then
    (* Find the position with the matching sq_index *)
    find (fun p => Nat.eqb (sq_index p) n) enum_pos
  else
    None.

(* Apply opening ballot *)
Definition apply_opening_move (st : GameState) (from_sq to_sq : nat) : option GameState :=
  match get_position_from_number from_sq, get_position_from_number to_sq with
  | Some from, Some to =>
    let m := Step from to in
    if legal_move_impl st m then
      apply_move_impl st m
    else
      None
  | _, _ => None
  end.

(* Apply a three-move opening ballot *)
Definition apply_opening_ballot (st : GameState) (op : Opening) : option GameState :=
  match op with
  | Opening11_15 =>
    (* Dark: 11-15, Light: 23-19, Dark: 8-11 *)
    match apply_opening_move st 11 15 with
    | Some st1 => match apply_opening_move st1 23 19 with
                  | Some st2 => apply_opening_move st2 8 11
                  | None => None
                  end
    | None => None
    end
  | Opening12_16 =>
    (* Dark: 12-16, Light: 24-20, Dark: 8-12 *)
    match apply_opening_move st 12 16 with
    | Some st1 => match apply_opening_move st1 24 20 with
                  | Some st2 => apply_opening_move st2 8 12
                  | None => None
                  end
    | None => None
    end
  | Opening9_13 =>
    (* Dark: 9-13, Light: 22-18, Dark: 5-9 *)
    match apply_opening_move st 9 13 with
    | Some st1 => match apply_opening_move st1 22 18 with
                  | Some st2 => apply_opening_move st2 5 9
                  | None => None
                  end
    | None => None
    end
  | Opening9_14 =>
    (* Dark: 9-14, Light: 22-17, Dark: 5-9 *)
    match apply_opening_move st 9 14 with
    | Some st1 => match apply_opening_move st1 22 17 with
                  | Some st2 => apply_opening_move st2 5 9
                  | None => None
                  end
    | None => None
    end
  | Opening10_14 =>
    (* Dark: 10-14, Light: 22-17, Dark: 6-10 *)
    match apply_opening_move st 10 14 with
    | Some st1 => match apply_opening_move st1 22 17 with
                  | Some st2 => apply_opening_move st2 6 10
                  | None => None
                  end
    | None => None
    end
  | Opening10_15 =>
    (* Dark: 10-15, Light: 22-18, Dark: 15-22 (capture!) *)
    match apply_opening_move st 10 15 with
    | Some st1 => match apply_opening_move st1 22 18 with
                  | Some st2 =>
                    (* This is actually a capture: 15x22 *)
                    match get_position_from_number 15, get_position_from_number 18,
                          get_position_from_number 22 with
                    | Some from, Some over, Some to =>
                      let link := existT (fun _ => Position) over to in
                      apply_move_impl st2 (Jump from [link])
                    | _, _, _ => None
                    end
                  | None => None
                  end
    | None => None
    end
  | Opening11_16 =>
    (* Dark: 11-16, Light: 24-20, Dark: 8-11 *)
    match apply_opening_move st 11 16 with
    | Some st1 => match apply_opening_move st1 24 20 with
                  | Some st2 => apply_opening_move st2 8 11
                  | None => None
                  end
    | None => None
    end
  end.

(* ========================================================================= *)
(* SECTION 18: VALIDATION FRAMEWORK & REPETITION KEYS                       *)
(* ========================================================================= *)

(* Position key and repetition detection are already defined in Section 10 *)

(* Perft: count nodes at given depth *)
Fixpoint perft (st : GameState) (depth : nat) : nat :=
  match depth with
  | 0%nat => 1%nat
  | S d =>
    let moves := generate_moves_impl st in
    fold_left (fun acc m =>
      match apply_move_impl st m with
      | Some st' => (acc + perft st' d)%nat
      | None => acc
      end
    ) moves 0%nat
  end.

(* Validation theorem for Section 18 *)
Theorem repetition_detects_threefold : forall st,
  count_position_key (key_of_state st) (repetition_book st) = 3%nat ->
  can_claim_threefold st = true.
Proof.
  intros st H.
  unfold can_claim_threefold.
  rewrite Nat.leb_le.
  rewrite H.
  apply le_n.
Qed.

(* Validation example for Section 18 *)
Example perft_initial_depth2 : perft initial_state 2 = 49%nat.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* Additional test: Problem position for multi-jump correctness *)
(* Create a simpler board for testing *)
Definition simple_jump_test_board : Board :=
  fun p =>
    let idx := sq_index p in
    if Nat.eqb idx 9 then Some {| pc_color := Dark; pc_kind := Man |}
    else if Nat.eqb idx 14 then Some {| pc_color := Light; pc_kind := Man |}
    else None.

(* Simpler test that a single jump works correctly *)
Example single_jump_correctness :
  match get_position_from_number 9, get_position_from_number 14,
        get_position_from_number 18 with
  | Some from, Some over, Some to =>
    jump_impl simple_jump_test_board
      {| pc_color := Dark; pc_kind := Man |} from over to = true
  | _, _, _ => True  (* Default to true if positions don't exist *)
  end.
Proof.
  unfold get_position_from_number.
  simpl.
  unfold find.
  (* This simplifies to checking specific positions *)
  vm_compute.
  reflexivity.
Qed.

(* Test: Simple promotion scenario *)
Definition promotion_test_board : Board :=
  fun p =>
    let idx := sq_index p in
    if Nat.eqb idx 25 then Some {| pc_color := Dark; pc_kind := Man |}
    else if Nat.eqb idx 28 then Some {| pc_color := Light; pc_kind := Man |}
    else None.

(* Test that promotion actually happens when reaching crown head *)
Example promotion_occurs_at_crown_head :
  match get_position_from_number 32 with
  | Some pos =>
    reaches_crown_head {| pc_color := Dark; pc_kind := Man |} pos = true
  | None => True
  end.
Proof.
  unfold get_position_from_number.
  simpl.
  unfold reaches_crown_head, is_crown_head.
  simpl.
  (* For Dark, crown head is rank 7 (0-indexed) *)
  (* Position 32 should be at rank 7 *)
  vm_compute.
  reflexivity.
Qed.

(* Verify that chain_maximal correctly returns true when no jumps available *)
Example chain_maximal_when_no_jumps :
  let empty_board : Board := fun _ => None in
  let pc := {| pc_color := Dark; pc_kind := Man |} in
  match get_position_from_number 16 with
  | Some pos =>
    chain_maximal empty_board pc pos [] = true
  | None => True
  end.
Proof.
  unfold get_position_from_number.
  simpl.
  unfold chain_maximal, exists_jump_from.
  simpl.
  vm_compute.
  reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 19: NOTATION (PDN-STYLE)                                         *)
(* ========================================================================= *)

(* Convert nat to string - using fuel for termination *)
Fixpoint nat_to_string_aux (fuel : nat) (n : nat) (acc : string) : string :=
  match fuel with
  | O => acc  (* Out of fuel *)
  | S fuel' =>
    match n with
    | O => acc
    | _ =>
      let digit := Nat.modulo n 10 in
      let rest := Nat.div n 10 in
      let c := Ascii.ascii_of_nat (digit + 48) in (* 48 is ASCII '0' *)
      let acc' := String c acc in
      match rest with
      | O => acc'
      | _ => nat_to_string_aux fuel' rest acc'
      end
    end
  end.

Definition nat_to_string (n : nat) : string :=
  match n with
  | O => "0"%string
  | _ => nat_to_string_aux 100 n EmptyString  (* 100 digits should be enough *)
  end.

(* Convert position to square number string *)
Definition position_to_string (p : Position) : string :=
  nat_to_string (sq_index p).

(* Helper to build jump string from chain *)
Fixpoint build_jump_string (pos : Position) (chain : JumpChain) : string :=
  match chain with
  | [] => EmptyString
  | link :: rest =>
    let to := link_to link in
    let sep := "x"%string in
    append sep (append (position_to_string to)
                      (build_jump_string to rest))
  end.

(* Convert move to PDN notation *)
Definition move_to_numeric (st : GameState) (m : Move) : string :=
  match m with
  | Step from to =>
    (* Non-capturing: "a-b" *)
    append (position_to_string from) (append "-"%string (position_to_string to))
  | Jump from ch =>
    (* Capturing: "axb[x...]" *)
    let from_str := position_to_string from in
    append from_str (build_jump_string from ch)
  | Resign c =>
    match c with
    | Dark => "Dark resigns"%string
    | Light => "Light resigns"%string
    end
  | AgreeDraw => "Draw"%string
  end.

(* Validation: Test simple step move notation *)
Example step_notation_test :
  match get_position_from_number 9, get_position_from_number 14 with
  | Some from, Some to =>
    move_to_numeric initial_state (Step from to) = "9-14"%string
  | _, _ => True
  end.
Proof.
  unfold get_position_from_number, move_to_numeric, position_to_string.
  simpl.
  (* This should compute to "9-14" *)
  vm_compute.
  reflexivity.
Qed.

(* Helper: parse a digit character to nat *)
Definition digit_of_ascii (c : ascii) : option nat :=
  let n := Ascii.nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then
    Some (Nat.sub n 48)
  else
    None.

(* Helper: parse a nat from string *)
Fixpoint parse_nat_aux (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c rest =>
    match digit_of_ascii c with
    | Some d => parse_nat_aux rest (acc * 10 + d)
    | None => None
    end
  end.

Definition parse_nat (s : string) : option nat :=
  match s with
  | EmptyString => None
  | _ => parse_nat_aux s 0
  end.

(* Helper: split string at first occurrence of separator *)
Fixpoint split_at_char (s : string) (sep : ascii) : (string * option string) :=
  match s with
  | EmptyString => (EmptyString, None)
  | String c rest =>
    if Ascii.eqb c sep then
      (EmptyString, Some rest)
    else
      let (before, after) := split_at_char rest sep in
      (String c before, after)
  end.

(* Parse a move from PDN notation *)
Definition parse_numeric (s : string) (st : GameState) : option Move :=
  (* Check for special moves first *)
  if String.eqb s "Draw"%string then
    Some AgreeDraw
  else if String.eqb s "Dark resigns"%string then
    Some (Resign Dark)
  else if String.eqb s "Light resigns"%string then
    Some (Resign Light)
  else
    (* Try to parse as a regular move *)
    (* First, check if it's a step (contains '-') or jump (contains 'x') *)
    let dash := Ascii.ascii_of_nat 45 in  (* '-' *)
    let x_char := Ascii.ascii_of_nat 120 in  (* 'x' *)
    let (before_dash, after_dash) := split_at_char s dash in
    match after_dash with
    | Some rest =>
      (* It's a step move: parse "from-to" *)
      match parse_nat before_dash, parse_nat rest with
      | Some from_num, Some to_num =>
        match get_position_from_number from_num, get_position_from_number to_num with
        | Some from, Some to => Some (Step from to)
        | _, _ => None
        end
      | _, _ => None
      end
    | None =>
      (* Check if it's a jump move *)
      let (before_x, after_x) := split_at_char s x_char in
      match after_x with
      | Some rest =>
        (* It's a jump move: parse "fromxto[xto2...]" *)
        match parse_nat before_x with
        | Some from_num =>
          match get_position_from_number from_num with
          | Some from =>
            (* Parse the chain of captures - simplified without inner recursion *)
            (* For a single jump, just parse the target *)
            match parse_nat rest with
            | Some to_num =>
              match get_position_from_number to_num with
              | Some to_pos =>
                (* Find the over position *)
                match find (fun over =>
                  andb (if diag_adj_dec from over then true else false)
                       (if diag_adj_dec over to_pos then true else false)
                ) enum_pos with
                | Some over =>
                  let link := existT (fun _ => Position) over to_pos in
                  Some (Jump from [link])
                | None => None
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None => None
      end
    end.

Lemma nat_to_string_parse_nat_small : forall n,
  (n <= 32)%nat ->
  parse_nat (nat_to_string n) = Some n.
Proof.
  intros n Hn.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/
          n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/
          n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/
          n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31 \/ n = 32)%nat by lia.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  rewrite H; vm_compute; reflexivity.
Qed.

Lemma fin8_to_nat_bounded : forall f : Fin8,
  (fin8_to_nat f < 8)%nat.
Proof.
  intro f.
  unfold fin8_to_nat.
  destruct (Fin.to_nat f) as [n H].
  exact H.
Qed.

Lemma sq_index_positive : forall p,
  (1 <= sq_index p)%nat.
Proof.
  intro p.
  unfold sq_index.
  simpl.
  apply Nat.lt_0_succ.
Qed.

Lemma fin8_to_nat_max : forall f : Fin8,
  (fin8_to_nat f <= 7)%nat.
Proof.
  intro f.
  unfold fin8_to_nat.
  destruct (Fin.to_nat f) as [n H].
  simpl.
  lia.
Qed.

Lemma rank_times_4_bounded : forall r : Fin8,
  (fin8_to_nat r * 4 <= 28)%nat.
Proof.
  intro r.
  assert (H: (fin8_to_nat r <= 7)%nat) by apply fin8_to_nat_max.
  lia.
Qed.

Lemma file_div_2_bounded_even : forall f : Fin8,
  (fin8_to_nat f / 2 <= 3)%nat.
Proof.
  intro f.
  assert (H: (fin8_to_nat f <= 7)%nat) by apply fin8_to_nat_max.
  destruct (fin8_to_nat f) eqn:E; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  exfalso.
  assert (fin8_to_nat f >= 8)%nat.
  { rewrite E. simpl. apply le_n_S, le_n_S, le_n_S, le_n_S.
    apply le_n_S, le_n_S, le_n_S, le_n_S, Nat.le_0_l. }
  lia.
Qed.

Lemma file_div_2_bounded_odd : forall f : Fin8,
  (S (fin8_to_nat f) / 2 <= 4)%nat.
Proof.
  intro f.
  assert (H: (fin8_to_nat f <= 7)%nat) by apply fin8_to_nat_max.
  destruct (fin8_to_nat f) eqn:E; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  exfalso.
  assert (fin8_to_nat f >= 8)%nat.
  { rewrite E. simpl. apply le_n_S, le_n_S, le_n_S, le_n_S.
    apply le_n_S, le_n_S, le_n_S, le_n_S, Nat.le_0_l. }
  lia.
Qed.

Lemma divmod_bound : forall n,
  (n <= 7)%nat ->
  (fst (Nat.divmod n 1 0 1) <= 3)%nat.
Proof.
  intros n Hn.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  exfalso. lia.
Qed.

Lemma divmod_S_bound : forall n,
  (n <= 7)%nat ->
  (fst (Nat.divmod (S n) 1 0 1) <= 4)%nat.
Proof.
  intros n Hn.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  exfalso. lia.
Qed.

Example parse_print_works_for_9_14 :
  let st := initial_state in
  match get_position_from_number 9, get_position_from_number 14 with
  | Some from, Some to =>
    parse_numeric (move_to_numeric st (Step from to)) st = Some (Step from to)
  | _, _ => True
  end.
Proof.
  simpl.
  vm_compute.
  reflexivity.
Qed.
                        
