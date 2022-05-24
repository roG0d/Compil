Require Import Coq.Program.Equality.
Require Import FSets.
From SF Require Import Imp.
From SF Require Import Semantics.
From SF Require Import Deadcode.
Import VSdecide.

(** In this chapter: a study of register allocation viewed as
  renaming the variables of an IMP program in a semantic-preserving
  manner.*)

(** * 1. Renaming variables in a program *)

(** Recognition of expressions that are just variables. *)

Definition expr_is_var (a: aexp): option id :=
  match a with AId x => Some x | _ => None end.

Lemma expr_is_var_correct:
  forall a x, expr_is_var a = Some x -> a = AId x.
Proof.
  unfold expr_is_var; intros. destruct a; congruence.
Qed.

Section RENAMING.

Variable f: id -> id.

(** Renaming variables in an expression. *)

Fixpoint rename_aexp (a: aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId (f x)
  | APlus a1 a2 => APlus (rename_aexp a1) (rename_aexp a2)
  | AMinus a1 a2 => AMinus (rename_aexp a1) (rename_aexp a2)
  | AMult a1 a2 => AMult (rename_aexp a1) (rename_aexp a2)
  end.

Fixpoint rename_bexp (b: bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (rename_aexp a1) (rename_aexp a2)
  | BLe a1 a2 => BLe (rename_aexp a1) (rename_aexp a2)
  | BNot b1 => BNot (rename_bexp b1)
  | BAnd b1 b2 => BAnd (rename_bexp b1) (rename_bexp b2)
  end.

(** Transformation of a command:
- renaming the variables
- dead code elimination as in the previous chapter
- coalescing: useless variable-to-variable copies [x ::= y] where
  [f x = f y]are turned into [SKIP].
*)

Fixpoint transf_com (c: com) (L: VS.t): com :=
  match c with
  | SKIP => SKIP
  | x ::= a =>
      if VS.mem x L then
        match expr_is_var a with
        | None => (f x) ::= (rename_aexp a)
        | Some y => if beq_id (f x) (f y) then SKIP else (f x) ::= (rename_aexp a)
        end
      else SKIP
  | (c1; c2) =>
      (transf_com c1 (live c2 L); transf_com c2 L)
  | IFB b THEN c1 ELSE c2 FI =>
      IFB rename_bexp b THEN transf_com c1 L ELSE transf_com c2 L FI
  | WHILE b DO c END =>
      WHILE rename_bexp b DO transf_com c (live (WHILE b DO c END) L) END
  end.

(** * 2. Semantic preservation *)

(** We adapt the notion of agreement between two states over a given
  set of live variables that was introduced in chapter [Deadcode]. *)

Definition agree (L: VS.t) (s1 s2: state) : Prop :=
  forall x, VS.In x L -> s1 x = s2 (f x).

(** Monotonicity property. *)

Lemma agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> VS.Subset L L' -> agree L s1 s2.
Proof.
  unfold VS.Subset, agree; intros. auto.
Qed.

Lemma agree_extensional:
  forall L s1 s2 s3,
  agree L s1 s2 -> (forall x, s2 x = s3 x) -> agree L s1 s3.
Proof.
  unfold agree; intros. transitivity (s2 (f x)); auto.
Qed.

(** Agreement on the free variables of an expression implies that this
    expression and its renaming evaluates identically in both states. *)

Lemma aeval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall a, VS.Subset (fv_aexp a) L ->
  aeval s1 a = aeval s2 (rename_aexp a).
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
  forall b, VS.Subset (fv_bexp b) L -> 
  beval s1 b = beval s2 (rename_bexp b).
Proof.
  induction b; simpl; intros.
  auto.
  auto.
  repeat rewrite (aeval_agree L s1 s2); auto; generalize H0; fsetdec.
  repeat rewrite (aeval_agree L s1 s2); auto; generalize H0; fsetdec.
  f_equal; auto.
  f_equal. apply IHb1. generalize H0; fsetdec. apply IHb2. generalize H0; fsetdec.
Qed.

(** Agreement is preserved by unilateral assignment to a dead variable. *)

Lemma agree_update_dead:
  forall s1 s2 L x v,
  agree L s1 s2 -> ~VS.In x L ->
  agree L (update s1 x v) s2.
Proof.
  intros; red; intros. unfold update. remember (beq_id x x0). destruct b.
  assert (x = x0). apply beq_id_eq. auto. subst x0. contradiction.
  apply H; auto.
Qed.

(** Agreement is preserved by simultaneous assignment to a live variable
   [x] and its renaming [f x], provided none of the other live variables
   [z] is renamed to [f x] (non-interference property). *)

Lemma agree_update_live:
  forall s1 s2 L x v,
  agree (VS.remove x L) s1 s2 ->
  (forall z, VS.In z L -> z <> x -> f z <> f x) ->
  agree L (update s1 x v) (update s2 (f x) v).
Proof.
  intros; red; intros. unfold update. remember (beq_id x x0). destruct b.
(* Case x = x0 *)
  assert (x = x0). apply beq_id_eq. auto. subst x0.
  rewrite <- beq_id_refl. auto.
(* Case x <> x0 *)
  assert (x <> x0). apply beq_id_false_not_eq; auto.
  assert (f x0 <> f x). apply H0; auto.
  rewrite not_eq_beq_id_false.
  apply H. apply VS.remove_2; auto.
  auto.
Qed.

(** A special case of [agree_update_live] where the value being assigned
  is not arbitrary, but is the value of another variable [y].
  In this case, we can relax the non-interference hypothesis
  (Chaitin's observation). *)

Lemma agree_update_move:
  forall s1 s2 L x y,
  agree (VS.union (VS.remove x L) (VS.singleton y)) s1 s2 ->
  (forall z, VS.In z L -> z <> x -> z <> y -> f z <> f x) ->
  agree L (update s1 x (s1 y)) (update s2 (f x) (s2 (f y))).
Proof.
  intros; red; intros. unfold update. remember (beq_id x x0). destruct b.
(* Case x = x0 *)
  assert (x = x0). apply beq_id_eq. auto. subst x0.
  rewrite <- beq_id_refl. apply H. fsetdec. 
(* Case x <> x0 *)
  assert (x <> x0). apply beq_id_false_not_eq; auto.
  remember (beq_id x0 y). destruct b.
(*  SCase x0 = y *)
    assert (x0 = y). apply beq_id_eq. auto. subst x0.
    transitivity (s2 (f y)).
    apply H. fsetdec.
    destruct (beq_id (f x) (f y)); auto.
(*  SCase x0 <> y *)
    assert (x0 <> y). apply beq_id_false_not_eq; auto.
    assert (f x0 <> f x). apply H0; auto. 
    rewrite not_eq_beq_id_false. 
    apply H. apply VS.union_2. apply VS.remove_2; auto. 
    auto.
Qed.

(** A special case of [agree_update_move] where [f x = f y].
  In this case, the assignment in the transformed program
  can be optimized away. *)

Lemma agree_update_coalesced_move:
  forall s1 s2 L x y,
  agree (VS.union (VS.remove x L) (VS.singleton y)) s1 s2 ->
  (forall z, VS.In z L -> z <> x -> z <> y -> f z <> f x) ->
  f x = f y ->
  agree L (update s1 x (s1 y)) s2.
Proof.
  intros. apply agree_extensional with (update s2 (f x) (s2 (f y))).
  apply agree_update_move; auto.
  intros. rewrite H1. unfold update. remember (beq_id (f y) x0). destruct b.
  assert (f y = x0). apply beq_id_eq; auto.
  congruence.
  auto.
Qed.

(** Gathering together the various non-interference conditions above,
  we obtain the following correctness criterion for a candidate
  renaming [f].  Note that this is a boolean-valued function, not
  a predicate; therefore, it can be used as a validator for
  a renaming computed by an untrusted heuristic. *)

Fixpoint correct_allocation (c: com) (L: VS.t) : bool :=
  match c with
  | SKIP =>
      true
  | x ::= a =>
      if VS.mem x L then
        match expr_is_var a with
        | Some y =>
            VS.for_all (fun z => beq_id z x || beq_id z y || negb (beq_id (f z) (f x))) L
        | None => 
            VS.for_all (fun z => beq_id z x || negb (beq_id (f z) (f x))) L
        end
      else true
  | (c1; c2) => 
      correct_allocation c1 (live c2 L) && correct_allocation c2 L
  | IFB b THEN c1 ELSE c2 FI =>
      correct_allocation c1 L && correct_allocation c2 L
  | WHILE b DO c END =>
      correct_allocation c (live (WHILE b DO c END) L)
  end.

Remark correct_allocation_assign_1:
  forall x y L,
  VS.for_all (fun z => beq_id z x || beq_id z y || negb (beq_id (f z) (f x))) L = true ->
  forall z, VS.In z L -> z <> x -> z <> y -> f z <> f x.
Proof.
  intros. 
  set (g := fun z => beq_id z x || beq_id z y || negb (beq_id (f z) (f x))) in *.
  assert (VS.For_all (fun x => g x = true) L).
    apply VS.for_all_2. 
    red; intros. congruence.
    auto. 
  red in H3. generalize (H3 z H0). unfold g. 
  rewrite not_eq_beq_id_false; auto. 
  rewrite not_eq_beq_id_false; auto.
  simpl. remember (beq_id (f z) (f x)). destruct b; simpl; intros.
  congruence.
  apply beq_id_false_not_eq; auto. 
Qed.

Remark correct_allocation_assign_2:
  forall x L,
  VS.for_all (fun z => beq_id z x || negb (beq_id (f z) (f x))) L = true ->
  forall z, VS.In z L -> z <> x -> f z <> f x.
Proof.
  intros. 
  set (g := fun z => beq_id z x || negb (beq_id (f z) (f x))) in *.
  assert (VS.For_all (fun x => g x = true) L).
    apply VS.for_all_2. 
    red; intros. congruence.
    auto. 
  red in H2. generalize (H2 z H0). unfold g. 
  rewrite not_eq_beq_id_false; auto.
  simpl. remember (beq_id (f z) (f x)). destruct b; simpl; intros.
  congruence.
  apply beq_id_false_not_eq; auto. 
Qed.

(** The proof of semantic preservation is a straightforward adaptation
  of the proof for dead code elimination.  There are more cases to
  be considered in the assignment case [x ::= a], corresponding
  to variable-to-variable moves [x ::= y], either coalesced or not. *)

Theorem transf_correct_terminating:
  forall st c st', c / st ==> st' ->
  forall L st1,
  agree (live c L) st st1 ->
  correct_allocation c L = true ->
  exists st1', transf_com c L / st1 ==> st1' /\ agree L st' st1'.
Proof.
  induction 1; intros L st1 AG CORR; simpl; simpl in CORR.

(*Case skip *)
  exists st1; split. constructor. auto.

(* := *)
  rename l into x. simpl in AG. remember (VS.mem x L) as is_live. destruct is_live.
(* SSCase x is live after *)
    assert (aeval st1 (rename_aexp a1) = n).
      rewrite <- H. symmetry. eapply aeval_agree. eauto. fsetdec.
    remember (expr_is_var a1) as is_var. destruct is_var as [y | ].
    (*  SSCasemove x := y *)
      assert (a1 = AId y). apply expr_is_var_correct; auto. subst a1. simpl in *.
      remember (beq_id (f x) (f y)) as coalesced.  destruct coalesced.
      (*  SSCase coalesced move *)
        assert (f x = f y). apply beq_id_eq; auto.
        exists st1; split.
        apply E_Skip.
        rewrite <- H. apply agree_update_coalesced_move; auto. 
        apply correct_allocation_assign_1; auto.
      (*  SSCase preserved move *)
        exists (update st1 (f x) n); split.
        apply E_Ass. simpl. auto.
        rewrite <- H at 1. rewrite <- H0.
        apply agree_update_move; auto.
        apply correct_allocation_assign_1; auto.
    (*  SSCase not a move *)
      exists (update st1 (f x) n); split.
      apply E_Ass. auto.
      apply agree_update_live.
      eapply agree_mon; eauto. fsetdec.
      apply correct_allocation_assign_2; auto.
  (*  SCase x is dead after *)
    exists st1; split.
    apply E_Skip. 
    apply agree_update_dead. auto. 
    red; intros. assert (VS.mem x L = true). apply VS.mem_1; auto. congruence.

(*  Case seq *)
  simpl in AG. destruct (andb_true _ _ CORR). 
  destruct (IHceval1 _ _ AG H1) as [st1' [E1 A1]].
  destruct (IHceval2 _ _ A1 H2) as [st2' [E2 A2]].
  exists st2'; split.
  apply E_Seq with st1'; auto.
  auto.

(*  Case if true *)
  simpl in AG. destruct (andb_true _ _ CORR). 
  assert (beval st1 (rename_bexp b1) = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec. 
  destruct (IHceval L st1) as [st1' [E A]].
    eapply agree_mon; eauto. fsetdec.
    auto.
  exists st1'; split.
  apply E_IfTrue; auto.
  auto.

(*  Case if false *)
  simpl in AG. destruct (andb_true _ _ CORR). 
  assert (beval st1 (rename_bexp b1) = false).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec. 
  destruct (IHceval L st1) as [st1' [E A]].
    eapply agree_mon; eauto. fsetdec.
    auto.
  exists st1'; split.
  apply E_IfFalse; auto.
  auto.

(*  Case while end *)
  destruct (live_while_charact b1 c1 L) as [P [Q R]].
  assert (beval st1 (rename_bexp b1) = false).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  exists st1; split.
  apply E_WhileEnd. auto. 
  eapply agree_mon; eauto. 

(*  Case while loop *)
  destruct (live_while_charact b1 c1 L) as [P [Q R]].
  assert (beval st1 (rename_bexp b1) = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  destruct (IHceval1 (live (CWhile b1 c1) L) st1) as [st2 [E1 A1]].
    eapply agree_mon; eauto.
    auto.
  destruct (IHceval2 L st2) as [st3 [E2 A2]].
    auto. auto.  
  exists st3; split.
  apply E_WhileLoop with st2; auto. 
  auto.
Qed.

Theorem transf_correct_diverging:
  forall st c L st1,
  c / st ==> ∞  ->
  agree (live c L) st st1 ->
  correct_allocation c L = true ->
  transf_com c L / st1 ==> ∞.
Proof.
  cofix COINDHYP; intros until st1; intros DIV AG CORR; inv DIV.

(*  Case seq left *)
  simpl in *. destruct (andb_prop _ _ CORR). 
  apply Einf_Seq_1. apply COINDHYP with st. auto. auto. auto. 

(*  Case seq right *)
  simpl in *. destruct (andb_prop _ _ CORR). 
  destruct (transf_correct_terminating _ _ _ H _ _ AG H1) as [st1' [E A]].
  apply Einf_Seq_2 with st1'. auto. apply COINDHYP with st2; auto.

(*  Case if true *)
  simpl in *. destruct (andb_prop _ _ CORR). 
  assert (beval st1 (rename_bexp b) = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec.
  apply Einf_IfTrue. auto.
  apply COINDHYP with st. auto. eapply agree_mon; eauto. fsetdec. auto. 

(*  Case if false *)
  simpl in *. destruct (andb_prop _ _ CORR). 
  assert (beval st1 (rename_bexp b) = false).
    rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec.
  apply Einf_IfFalse. auto.
  apply COINDHYP with st. auto. eapply agree_mon; eauto. fsetdec. auto. 

(*  Case while body *)
  destruct (live_while_charact b c1 L) as [P [Q R]].
  assert (beval st1 (rename_bexp b) = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  apply Einf_WhileBody. auto.
  apply COINDHYP with st. auto. eapply agree_mon; eauto. auto. 

(* while loop *)
  destruct (live_while_charact b c1 L) as [P [Q R]].
  assert (beval st1 (rename_bexp b) = true).
    rewrite <- H. symmetry. eapply beval_agree; eauto.
  destruct (transf_correct_terminating _ _ _ H0 (live (CWhile b c1) L) st1) as [st2 [E1 A1]].
    eapply agree_mon; eauto. auto.
  apply Einf_WhileLoop with st2. auto. apply E1. 
  apply (COINDHYP st' (WHILE b DO c1 END) L st2). auto. auto. auto.
Qed.

End RENAMING.

(** * 3. Examples *)

(** If we give it the identity renaming, our code transformation
  behaves exactly like dead code elimination. *)

Definition trivial_alloc := fun (x: id) => x.

Eval vm_compute in (correct_allocation trivial_alloc prog (VS.singleton vr)).
Eval vm_compute in (transf_com trivial_alloc prog (VS.singleton vr)).

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

(** Here is another allocation that collapses variables [r] and [a].*)

Definition my_alloc := fun (x: id) => if beq_id x vr then va else x.

Eval vm_compute in (correct_allocation my_alloc prog (VS.singleton vr)).
Eval vm_compute in (transf_com my_alloc prog (VS.singleton vr)).

(** Here is the result.  Note the removal of [r := a].
<<
   r := a;                 ===>   skip;
   q := 0;                        skip;
   while b <= r do                while b <= a do
     r := r - b;                    a := a - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

(** Finally, if we try to collapse variable [r] and [b], the validation
  function [correct_allocation] rejects the allocation. *)

Definition wrong_alloc := fun (x: id) => if beq_id x vr then vb else x.

Eval vm_compute in (correct_allocation wrong_alloc prog (VS.singleton vr)).

(** * 4. Putting it all together *)

(** We assume given a register allocation heuristic that computes a candidate
  allocation. *)

Parameter regalloc_heuristic: com -> VS.t -> (id -> id).

(** Typically, this heuristic will be written in Caml and linked with
  the Caml code extracted from the present Coq development. *)

(** We then define the register allocation pass.  [prog] is the program to be
  transformed and [obs] is the set of variables we want to observe at the
  end of its execution.  This compilation pass can fail at compile-time,
  in which case it returns [None]. *)

Definition regalloc (prog: com) (obs: VS.t) : option com :=
  let f := regalloc_heuristic prog obs in
  if correct_allocation f prog obs
  then Some(transf_com f prog obs)
  else None.
