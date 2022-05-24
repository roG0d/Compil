Require Import Coq.Program.Equality.
Require Import Lia.
Require Import FSets.
From SF Require Import Imp.
From SF Require Import Sequences.
From SF Require Import Semantics.

(** In this chapter: liveness analysis and its use for an optimization
  called dead code elimination. *)

(** * 1. Sets of variables *)

(** The static analysis we need -- liveness analysis -- operates over
  sets of variables.  Coq's standard library provides a rich, efficient
  implementation of finite sets.  Before being able to use it, however,
  we must provide it with a Coq module equipping the type of identifiers
  with a total, decidable ordering.  The implementation of this module follows. *)

Module Id_Ordered <: OrderedType with Definition t := id.
  Definition t := id.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) := match x, y with Id nx, Id ny => nx < ny end.

  Lemma eq_refl : forall x : t, eq x x.
  Proof. intro. reflexivity. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. unfold eq; intros; auto. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. unfold eq; intros; congruence. Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt; intros. destruct x; destruct y; destruct z. lia. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros. destruct x; destruct y.
    assert (n <> n0) by lia. congruence.
  Qed. 

  Definition compare: forall (x y: t), Compare lt eq x y.
  Proof.
    intros. case x; intro nx. case y; intro ny.
    remember (beq_nat nx ny). destruct b.
    apply EQ. red. f_equal. apply beq_nat_true. auto.
    assert (nx <> ny). apply beq_nat_false. auto.
    remember (ble_nat nx ny). destruct b.
    assert (nx <= ny). apply ble_nat_true; auto.
    apply LT. red. lia.
    assert (~(nx <= ny)). apply ble_nat_false; auto.
    apply GT. red. lia.
  Defined.

  Definition eq_dec: forall (x y: t), {x=y} + {x<>y}.
  Proof.
    intros; destruct x; destruct y. 
    remember (beq_nat n n0); destruct b. 
    left. f_equal. apply beq_nat_true. auto.
    right. assert (n <> n0). apply beq_nat_false; auto. congruence.
  Defined.
End Id_Ordered.

(** We then instantiate the finite sets modules from Coq's standard library
  with this ordered type of integers. *)

Module VS := FSetAVL.Make(Id_Ordered).
Module VSP := FSetProperties.Properties(VS).
Module VSdecide := FSetDecide.Decide(VS).
Import VSdecide.

(** * 2. Liveness analysis *)

(** ** Free variables *)

(** Computation of the set of variables appearing in an expression or command. *)

Fixpoint fv_aexp (a: aexp) : VS.t :=
  match a with
  | ANum n => VS.empty
  | AId v => VS.singleton v
  | APlus a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | AMinus a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | AMult a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  end.

Fixpoint fv_bexp (b: bexp) : VS.t :=
  match b with
  | BTrue => VS.empty
  | BFalse => VS.empty
  | BEq a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | BLe a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | BNot b1 => fv_bexp b1
  | BAnd b1 b2 => VS.union (fv_bexp b1) (fv_bexp b2)
  end.

Fixpoint fv_com (c: com) : VS.t :=
  match c with
  | SKIP => VS.empty
  | x ::= a => fv_aexp a
  | (c1; c2) => VS.union (fv_com c1) (fv_com c2)
  | IFB b THEN c1 ELSE c2 FI => VS.union (fv_bexp b) (VS.union (fv_com c1) (fv_com c2))
  | WHILE b DO c END => VS.union (fv_bexp b) (fv_com c)
  end.

(** ** Computing post-fixpoints. *)

Section FIXPOINT.

Variable F: VS.t -> VS.t.
Variable default: VS.t.

(** Our goal is to find a set of variables [x] such that [F x] is a subset of [x]
  (a post-fixpoint of F).  We use a naive algorithm: iterate [F] at most [n] times,
  stopping as soon as a post-fixpoint is encountered.  If not,
  we return a safe default result. *)

Fixpoint iter (n: nat) (x: VS.t) : VS.t :=
  match n with
  | O => default
  | S n' =>
      let x' := F x in
      if VS.subset x' x then x else iter n' x'
  end.

Definition niter := 10%nat.

Definition fixpoint : VS.t := iter niter VS.empty.

Lemma fixpoint_charact:
  VS.Subset (F fixpoint) fixpoint \/ fixpoint = default.
Proof.
  unfold fixpoint. generalize niter, VS.empty. induction n; intros; simpl.
  auto.
  case_eq (VS.subset (F t) t); intro. 
  left. apply VS.subset_2. auto.
  apply IHn. 
Qed.

Hypothesis F_stable:
  forall x, VS.Subset x default -> VS.Subset (F x) default.

Lemma fixpoint_upper_bound:
  VS.Subset fixpoint default.
Proof.
  assert (forall n x, VS.Subset x default -> VS.Subset (iter n x) default).
  induction n; intros; simpl.
  red; auto.
  case_eq (VS.subset (F x) x); intro. auto. apply IHn. auto. 
  unfold fixpoint. apply H. apply VSP.subset_empty. 
Qed.

End FIXPOINT.

(** ** Liveness analysis. *)

(** [L] is the set of variables live "after" command [c].
  The result of [live c L] is the set of variables live "before" [c]. *)

Fixpoint live (c: com) (L: VS.t) : VS.t :=
  match c with
  | SKIP => L
  | x ::= a =>
      if VS.mem x L
      then VS.union (VS.remove x L) (fv_aexp a)
      else L
  | (c1; c2) =>
      live c1 (live c2 L)
  | IFB b THEN c1 ELSE c2 FI =>
      VS.union (fv_bexp b) (VS.union (live c1 L) (live c2 L))
  | WHILE b DO c END =>
      let L' := VS.union (fv_bexp b) L in
      let default := VS.union (fv_com (CWhile b c)) L in
      fixpoint (fun x => VS.union L' (live c x)) default
  end.

Lemma live_upper_bound:
  forall c L,
  VS.Subset (live c L) (VS.union (fv_com c) L).
Proof.
  induction c; intros; simpl.
  fsetdec.
  case_eq (VS.mem i L); intros. fsetdec. fsetdec.
  generalize (IHc1 (live c2 L)). generalize (IHc2 L). fsetdec.
  generalize (IHc1 L). generalize (IHc2 L). fsetdec.
  apply fixpoint_upper_bound. intro x. generalize (IHc x). fsetdec.
Qed.

Lemma live_while_charact:
  forall b c L,
  let L' := live (WHILE b DO c END) L in
  VS.Subset (fv_bexp b) L' /\ VS.Subset L L' /\ VS.Subset (live c L') L'.
Proof.
  intros.
  generalize (fixpoint_charact
    (fun x : VS.t => VS.union (VS.union (fv_bexp b) L) (live c x))
          (VS.union (VS.union (fv_bexp b) (fv_com c)) L)).
  simpl in L'. fold L'. intros [A|A].
  split. generalize A; fsetdec. split; generalize A; fsetdec. 
  split. rewrite A. fsetdec. 
  split. rewrite A. fsetdec.
  eapply VSP.subset_trans. apply live_upper_bound. rewrite A. fsetdec.
Qed.

(** * 3. Dead code elimination *)

(** ** Code transformation *)

(** The code transformation turns assignments [x ::= a] to dead variables
  into [SKIP] statements. *)

Fixpoint dce (c: com) (L: VS.t): com :=
  match c with
  | SKIP => SKIP
  | x ::= a => if VS.mem x L then x ::= a else SKIP
  | (c1; c2) => (dce c1 (live c2 L); dce c2 L)
  | IFB b THEN c1 ELSE c2 FI => IFB b THEN dce c1 L ELSE dce c2 L FI
  | WHILE b DO c END => WHILE b DO dce c (live (WHILE b DO c END) L) END
  end.

(** Example of optimization. *)

Notation va := (Id 0).
Notation vb := (Id 1).
Notation vq := (Id 2).
Notation vr := (Id 3).

Definition prog :=
  ( vr ::= AId va;
    vq ::= ANum 0;
    WHILE BLe (AId vb) (AId vr) DO
      vr ::= AMinus (AId vr) (AId vb);
      vq ::= APlus (AId vq) (ANum 1)
    END ).

Eval vm_compute in (dce prog (VS.singleton vr)).

(** Result is:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b <= r do                while b <= r do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

Eval vm_compute in (dce prog (VS.singleton vq)).

(** Program is unchanged. *)

(** ** Semantic correctness *)

(** Two states agree on a set [L] of live variables if they assign
  the same values to each live variable. *)

Definition agree (L: VS.t) (s1 s2: state) : Prop :=
  forall x, VS.In x L -> s1 x = s2 x.

(** Monotonicity property. *)

Lemma agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> VS.Subset L L' -> agree L s1 s2.
Proof.
  unfold VS.Subset, agree; intros. auto.
Qed.

(** Agreement on the free variables of an expression implies that this
    expression evaluates identically in both states. *)

Lemma aeval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall a, VS.Subset (fv_aexp a) L -> aeval s1 a = aeval s2 a.
Proof.
  induction a; simpl; intros.
  auto.
  apply H. generalize H0; fsetdec. 
  f_equal. apply IHa1. generalize H0; fsetdec. apply IHa2. generalize H0; fsetdec. 
  f_equal. apply IHa1. generalize H0; fsetdec. apply IHa2. generalize H0; fsetdec.
  f_equal. apply IHa1. generalize H0; fsetdec. apply IHa2. generalize H0; fsetdec. 
Qed.

Lemma beval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall b, VS.Subset (fv_bexp b) L -> beval s1 b = beval s2 b.
Proof.
  induction b; simpl; intros.
  auto.
  auto.
  repeat rewrite (aeval_agree L s1 s2); auto; generalize H0; fsetdec.
  repeat rewrite (aeval_agree L s1 s2); auto; generalize H0; fsetdec.
  f_equal; apply IHb; auto.
  f_equal. apply IHb1. generalize H0; fsetdec. apply IHb2. generalize H0; fsetdec.
Qed.

(** Agreement is preserved by simultaneous assignment to a live variable. *)

Lemma agree_update_live:
  forall s1 s2 L x v,
  agree (VS.remove x L) s1 s2 ->
  agree L (update s1 x v) (update s2 x v).
Proof.
  intros; red; intros. unfold update. remember (beq_id x x0). destruct b.
  auto.
  apply H. apply VS.remove_2. apply beq_id_false_not_eq. auto. auto. 
Qed.

(** Agreement is also preserved by unilateral assignment to a dead variable. *)

Lemma agree_update_dead:
  forall s1 s2 L x v,
  agree L s1 s2 -> ~VS.In x L ->
  agree L (update s1 x v) s2.
Proof.
  intros; red; intros. unfold update. remember (beq_id x x0). destruct b.
  assert (x = x0). apply beq_id_eq; auto. subst x0. contradiction.
  apply H; auto.
Qed.

(** Semantic preservation for terminating programs.  A simple induction on
  the big-step evaluation derivation. *)

Theorem dce_correct_terminating:
  forall st c st', c / st ==> st' ->
  forall L st1,
  agree (live c L) st st1 ->
  exists st1', dce c L / st1 ==> st1' /\ agree L st' st1'.
Proof.
  induction 1; intros; simpl.

(* Case skip *)
  exists st1; split. constructor. auto.

(* Case ::= *)
  rename l into x. simpl in H0. remember (VS.mem x L) as is_live. destruct is_live.
(* SCase x is live after *)
    assert (aeval st1 a1 = n).
      rewrite <- H. symmetry. eapply aeval_agree. eauto. fsetdec.
    exists (update st1 x n); split.
    apply E_Ass. auto.
    apply agree_update_live. eapply agree_mon. eauto. fsetdec.
(* SCase x is dead after *)
    exists st1; split.
    apply E_Skip. 
    apply agree_update_dead. auto. 
    red; intros. assert (VS.mem x L = true). apply VS.mem_1; auto. congruence.

(* Case seq *)
  simpl in H1.
  destruct (IHceval1 _ _ H1) as [st1' [E1 A1]].
  destruct (IHceval2 _ _ A1) as [st2' [E2 A2]].
  exists st2'; split.
  apply E_Seq with st1'; auto.
  auto.

(* Case if true *)
  simpl in H1.
  assert (beval st1 b1 = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec. 
  destruct (IHceval L st1) as [st1' [E A]].
    eapply agree_mon; eauto. fsetdec.
  exists st1'; split.
  apply E_IfTrue; auto.
  auto.

(* Case if false *)
  simpl in H1.
  assert (beval st1 b1 = false).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec. 
  destruct (IHceval L st1) as [st1' [E A]].
    eapply agree_mon; eauto. fsetdec.
  exists st1'; split.
  apply E_IfFalse; auto.
  auto.

(* Case while end *)
  destruct (live_while_charact b1 c1 L) as [P [Q R]].
  assert (beval st1 b1 = false).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  exists st1; split.
  apply E_WhileEnd. auto. 
  eapply agree_mon; eauto. 

(* Case while loop *)
  destruct (live_while_charact b1 c1 L) as [P [Q R]].
  assert (beval st1 b1 = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  destruct (IHceval1 (live (CWhile b1 c1) L) st1) as [st2 [E1 A1]].
    eapply agree_mon; eauto.
  destruct (IHceval2 L st2) as [st3 [E2 A2]].
    auto. 
  exists st3; split.
  apply E_WhileLoop with st2; auto. 
  auto.
Qed.

(** Semantic preservation for diverging programs.  This one is by
  coinduction, using the big-step semantics for divergence. *)

Theorem dce_correct_diverging:
  forall st c L st1,
  c / st ==> ∞  ->
  agree (live c L) st st1 ->
  dce c L / st1 ==> ∞.
Proof.
  cofix COINDHYP; intros until st1; intros DIV AG; inv DIV.

(* Case seq left *)
  simpl in *. apply Einf_Seq_1. apply COINDHYP with st. auto. auto. 

(* Case seq right *)
  simpl in *.
  destruct (dce_correct_terminating _ _ _ H _ _ AG) as [st1' [E A]].
  apply Einf_Seq_2 with st1'. auto. apply COINDHYP with st2; auto.

(* Case if true *)
  simpl in *.
  assert (beval st1 b = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec.
  apply Einf_IfTrue. auto.
  apply COINDHYP with st. auto. eapply agree_mon; eauto. fsetdec. 

(* Case if false *)
  simpl in *.
  assert (beval st1 b = false).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec.
  apply Einf_IfFalse. auto.
  apply COINDHYP with st. auto. eapply agree_mon; eauto. fsetdec.

(* Case while body *)
  destruct (live_while_charact b c1 L) as [P [Q R]].
  assert (beval st1 b = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  apply Einf_WhileBody. auto.
  apply COINDHYP with st. auto. eapply agree_mon; eauto. 

(* Case while loop *)
  destruct (live_while_charact b c1 L) as [P [Q R]].
  assert (beval st1 b = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  destruct (dce_correct_terminating _ _ _ H0 (live (CWhile b c1) L) st1) as [st2 [E1 A1]].
    eapply agree_mon; eauto.
  apply Einf_WhileLoop with st2. auto. apply E1. 
  apply (COINDHYP st' (WHILE b DO c1 END) L st2). auto. auto.
Qed.

(** **** Exercise (4 stars) *)

(** Complete the following alternate proof of semantic preservation.
  This one uses the small-step semantics. *)

Fixpoint measure (c: com) : nat :=
  match c with
  | CAss x a => 1
  | CSeq c1 c2 => measure c1
  | _ => 0
  end.

Theorem dce_simulation:
  forall c st c' st',
  c / st --> c' / st' ->
  forall L st1,
  agree (live c L) st st1 ->
  (exists st1',
   dce c L / st1 --> dce c' L / st1' /\
   agree (live c' L) st' st1')
  \/
  (measure c' < measure c /\ dce c L = dce c' L /\ agree (live c' L) st' st1).
Proof.
  intros until st'. intro STEP. dependent induction STEP; simpl; intros.
  (* FILL IN HERE *)
Admitted.

(** **** Exercise (3 stars) *)

(** Complete the following alternate proof of semantic preservation.
  This one uses the definitional interpreter. *)

Inductive results_agree: VS.t -> option state -> option state -> Prop :=
  | res_agree_None: forall L,
      results_agree L None None
  | res_agree_Some: forall L st st1,
      agree L st st1 ->
      results_agree L (Some st) (Some st1).

Lemma dce_ceval_step:
  forall n c L st st1,
  agree (live c L) st st1 ->
  results_agree L (ceval_step st c n) (ceval_step st1 (dce c L) n).
Proof.
  induction n; intros.
  (** FILL IN HERE *)
Admitted.

Require Import Max.

Theorem dce_denot:
  forall c L st st1,
  agree (live c L) st st1 ->
  results_agree L (denot st c) (denot st1 (dce c L)).
Proof.
  intros. 
  destruct (denot_limit st c) as [m1 LIM1].
  destruct (denot_limit st1 (dce c L)) as [m2 LIM2].
  rewrite <- (LIM1 (max m1 m2)). rewrite <- (LIM2 (max m1 m2)).
  apply dce_ceval_step. auto.
  apply le_max_r. apply le_max_l.
Qed.


