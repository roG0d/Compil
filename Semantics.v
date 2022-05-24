Require Import Coq.Program.Equality.
From SF Require Import Imp.
From SF Require Import Sequences.
Require Export Lia.
Require Import String.
Open Scope string_scope.

(** In this chapter: various styles of semantics for the Imp language
  from "Software Foundations", and equivalence results between these
  semantics. *)

(** * 1. Big-step semantics for termination. *)

(** The starting point is the big-step semantics defined in file [sf/Imp.v],
  recalled here for reference.
<<
Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st ==> st
  | E_Ass  : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st ==> (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  ==> st' ->
      c2 / st' ==> st'' ->
      (c1 ; c2) / st ==> st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st ==> st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (WHILE b1 DO c1 END) / st' ==> st'' ->
      (WHILE b1 DO c1 END) / st ==> st''

  where "c1 '/' st '==>' st'" := (ceval st c1 st').
>>

[ c / st ==> st' ] means "executed in initial state [st], command [c]
terminates in final state [st']".

*)


(** * 2. Small-step semantics.  *)

Reserved Notation " c '/' st '-->' c' '/' st' " (at level 40, st at level 39, c' at level 39).

(** In small-step style, the semantics is presented as a one-step reduction
  relation [ c / st --> c' / st' ], meaning that the command [c],
  executed in initial state [st'], performs one elementary step of computation.
  [st'] is the updated state after this step.
  [c'] is the residual command, capturing all the computations that
  remain to be done.

  A small-step semantics for Imp was given in file [sf/Imp.v], where
  not only the execution of commands is broken in individual steps,
  but also the evaluation of arithmetic and boolean expressions.
  We depart from this semantics by still treating the evaluation
  of arithmetic and boolean expressions as one atomic "big-step"
  (cf. rules [CS_Ass], [CS_IfTrue] and [CS_IfFalse] below.
  Non-atomic evaluation of expressions makes a difference in the case
  of parallel (interleaved) execution of several commands.  In a purely
  sequential setting, it is equivalent (and much simpler) to
  evaluate expressions in one atomic step, since their evaluations
  always terminate.

  In summary, we have:
- Three "computational" rules: [CS_Ass], [CS_IfTrue] and [CS_IfFalse]
  that actually perform a significant computation.
- Two "refocusing" rules: [CS_SeqFinish] and [CS_While]
  that just shift the focus of reduction to the next redex.
- One "context" rule: [CS_SeqStep]
  that lets us reduce "under" a sequence.
*)

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_Ass : forall st i a n,
      aeval st a = n ->
      (i ::= a) / st --> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ; c2) / st --> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ; c2) / st --> c2 / st
  | CS_IfTrue : forall st b c1 c2,
      beval st b = true ->
      IFB b THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st b c1 c2,
      beval st b = false ->
      IFB b THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : forall st b c1,
      (WHILE b DO c1 END) / st
       --> (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " c '/' st '-->' c' '/' st' " := (cstep (c,st) (c',st')).

Lemma cstep_deterministic:
  forall cs cs1, cstep cs cs1 -> forall cs2, cstep cs cs2 -> cs1 = cs2.
Proof.
  induction 1; intros cs2 CSTEP; inversion CSTEP; subst.
  auto.
  generalize (IHcstep _ H4). congruence.
  inversion H.
  inversion H3.
  auto.
  auto.
  congruence.
  congruence.
  auto.
  auto.
Qed.

(** In small-step style, the semantics of a command [c] in a state [st]
  is determined by forming sequences of reductions starting from [c, st].
- Finite sequences: zero, one or several reductions (reflexive transitive closure)
- Infinite sequences: infinitely many reductions.

These sequences are defined using the generic [star] and [infseq] operators
over binary relations, which are defined in module [Sequences], along
with useful lemmas. *)

Notation " c '/' st '-->*' c' '/' st' " := (star cstep (c, st) (c', st'))
(at level 40, st at level 39, c' at level 39).

Notation " c '/' st '-->'  '∞' " := (infseq cstep (c, st))
(at level 40, st at level 39).

Definition terminates (c: com) (st: state) (st': state) : Prop :=
  c / st -->* SKIP / st'.

Definition diverges (c: com) (st: state) : Prop :=
  c / st --> ∞.

Definition goes_wrong (c: com) (st: state) : Prop :=
  exists c', exists st',
  c / st --> c' / st' /\ irred cstep (c', st') /\ c' <> SKIP.

(** *** Exercise (2 stars) *)
(** Show that Imp programs cannot go wrong. *)
Lemma not_goes_wrong:
  forall c st, ~(goes_wrong c st).
Proof.
  (* FILL IN HERE *)
Admitted.

(** Sequences of reductions can go under a sequence context, generalizing
  rule [CS_SeqStep]. *)

Lemma star_CS_SeqStep:
  forall c2 st c st' c',
  c / st -->* c' / st' ->
  (c;c2) / st -->* (c';c2) / st'.
Proof.
  intros. dependent induction H.
  apply star_refl.
  destruct b as [st1 c1].
  eapply star_step. apply CS_SeqStep. eauto. auto.  
Qed.

(** We now recall the equivalence result between 
- termination according to the big-step semantics
- existence of a finite sequence of reductions to [SKIP]
  according to the small-step semantics.

We start with the implication big-step ==> small-step, which is
a straightforward induction on the big-step evaluation derivation. *)

Theorem ceval_to_csteps:
  forall c st st',
  c / st ==> st' ->
  c / st -->* SKIP / st'.
Proof.
  induction 1.
Case "SKIP".
  apply star_refl.
Case ":=".
  apply star_one. apply CS_Ass. auto.
Case "seq".
  eapply star_trans. apply star_CS_SeqStep. apply IHceval1.
  eapply star_step. apply CS_SeqFinish. auto.
Case "if true".
  eapply star_step. apply CS_IfTrue. auto. auto.
Case "if false".
  eapply star_step. apply CS_IfFalse. auto. auto.
Case "while stop".
  eapply star_step. apply CS_While. 
  apply star_one. apply CS_IfFalse. auto.
Case "while true".
  eapply star_step. apply CS_While. 
  eapply star_step. apply CS_IfTrue. auto.
  eapply star_trans. apply star_CS_SeqStep. apply IHceval1. 
  eapply star_step. apply CS_SeqFinish. auto.
Qed.

(** The reverse implication, from small-step to big-step, is more subtle.
The key lemma is the following, showing that one step of reduction
followed by a big-step evaluation to a final state can be collapsed
into a single big-step evaluation to that final state. *)

Lemma cstep_append_ceval:
  forall c1 st1 c2 st2,
  c1 / st1 --> c2 / st2 ->
  forall st3,
  c2 / st2 ==> st3 ->
  c1 / st1 ==> st3.
Proof.
  intros until st2. intro STEP. dependent induction STEP; intros.
Case "CS_Ass".
  inversion H; subst. apply E_Ass. auto.
Case "CS_SeqStep".
  inversion H; subst. apply E_Seq with st'. eauto. auto.
Case "CS_SeqFinish".
  apply E_Seq with st2. apply E_Skip. auto.
Case "CS_IfTrue".
  apply E_IfTrue; auto.
Case "CS_IfFalse".
  apply E_IfFalse; auto.
Case "CS_While".
  inversion H; subst. 
  SCase "while loop".
    inversion H6; subst. 
    apply E_WhileLoop with st'; auto.
  SCase "while end".
    inversion H6; subst. 
    apply E_WhileEnd; auto.
Qed.

(** As a consequence, a term that reduces to [SKIP] evaluates in big-step
  with the same final state. *)

Theorem csteps_to_ceval:
  forall st c st',
  c / st -->* SKIP / st' ->
  c / st ==> st'.
Proof.
  intros. dependent induction H.
  apply E_Skip.
  destruct b as [st1 c1]. apply cstep_append_ceval with st1 c1; auto.
Qed.

(** * 3. Coinductive big-step semantics for divergence *)

(** We now define a predicate [ c / st ==> ∞ ] that characterizes
  diverging evaluations in big-step style, that is, by following
  the structure of the command [c].  The only commands that can diverge are:

- [c1;c2] if either [c1] diverges, or [c1] terminates and [c2] diverges.
- [IFB b THEN c1 ELSE c2 FI] if either [b] is true and [c1] diverges,
  or [b] is false and [c2] diverges.
- [WHILE b DO c END] if either [c] diverges at the first iteration
  or the loop diverges at later iterations.
*)

Reserved Notation " c '/' st '==>'  '∞' " (at level 40, st at level 39).

CoInductive cevalinf: com -> state -> Prop :=
  | Einf_Seq_1: forall c1 c2 st,
      c1 / st ==> ∞ ->
      (c1; c2) / st ==> ∞
  | Einf_Seq_2: forall c1 c2 st1 st2,
      c1 / st1 ==> st2 -> c2 / st2 ==> ∞ ->
      (c1; c2) / st1 ==> ∞
  | Einf_IfTrue: forall b c1 c2 st,
      beval st b = true ->
      c1 / st ==> ∞ ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> ∞
  | Einf_IfFalse: forall b c1 c2 st,
      beval st b = false ->
      c2 / st ==> ∞ ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> ∞
  | Einf_WhileBody: forall b c1 st,
      beval st b = true ->
      c1 / st ==> ∞ ->
      (WHILE b DO c1 END) / st ==> ∞
  | Einf_WhileLoop: forall b c1 st st',
      beval st b = true ->
      c1 / st ==> st' -> (WHILE b DO c1 END) / st' ==> ∞ ->
      (WHILE b DO c1 END) / st ==> ∞

where " c '/' st '==>' '∞' " := (cevalinf c st).

(** The [ c / st ==> ∞ ] predicate is declared as coinductive, meaning
  that we are interested in finite or infinite derivations.  If it were declared
  inductive, only finite derivations would be accepted, and the predicate would always
  be false, since there are no axioms to start a finite derivation. *)

(** To show that [ c / st ==> ∞ ] holds for some [c] and [st], we must
  use proofs by coinduction.  A proof by coinduction shows the existence
  of a derivation by assuming the result (as coinduction hypothesis),
  then constructing the bottom steps of the derivation, using one or
  several constructors of the coinductive predicate, then possibly using
  the coinduction hypothesis as argument to some of those constructors.
  For example, here is a proof that [WHILE BTrue DO SKIP END] always
  diverges. *)

Remark while_true_skip_diverges:
  forall st, (WHILE BTrue DO SKIP END) / st ==> ∞.
Proof.
  (** Start a coinductive proof, remembering the coinductive hypothesis as COINDHYP. *)
  cofix COINDHYP.
  intros. 
  (** Use rule [Einf_Whileloop] as the bottom step of the derivation. *)
  apply Einf_WhileLoop with st.
  (** Show that [BTrue] evaluates to [true]. *)
  auto.
  (** Show that [SKIP] terminates without changing the state. *)
  apply E_Skip. 
  (** Show that the next iteration of the loop diverges, by invoking the coinduction hypothesis. *)
  apply COINDHYP.
Qed.

(** Of course, we must be careful not to use the coinduction hypothesis immediately,
  but only as argument to a constructor.  Otherwise, Coq will refuse the proof. *)

Remark while_true_skip_diverges_wrong_proof:
  forall st, (WHILE BTrue DO SKIP END) / st ==> ∞.
Proof.
  cofix COINDHYP.
  intros.
  apply COINDHYP.
  (** error if Qed *)
Admitted.

(** **** Exercise (1 star) *)

(** Show that the program [WHILE 1 <= x DO x ::= x + 1 END] diverges
  if started in a state [st] such that [st x >= 1]:
*)

Notation vx := (Id 0).

Remark counting_program_diverges:
  forall st,
  st vx >= 1 ->
  WHILE BLe (ANum 1) (AId vx) DO vx ::= APlus (AId vx) (ANum 1) END / st ==> ∞.
Proof.
  cofix COINDHYP. intros.
  (** FILL IN HERE *)
Admitted.

(** To make sure that the coinductive big-step notion of divergence is correct,
  we show that it is equivalent to the existence of infinite reduction sequences.
  We start with the implication coinductive big-step => infinite reductions.
  The crucial lemma is that a command that diverges according to the big-step
  definition can always reduce, and its reduct still diverges. *)

Lemma cevalinf_can_progress:
  forall c st,
  c / st ==> ∞  -> exists c', exists st', c / st --> c' / st' /\ c' / st' ==> ∞.
Proof.
  induction c; intros st CINF; inversion CINF; subst.
Case "Seq1".
  destruct (IHc1 _ H2) as [c1' [st' [A B]]].
  exists (c1';c2); exists st'; split.
  apply CS_SeqStep; auto.
  eapply Einf_Seq_1; eauto.
Case "Seq2".
  assert (ST: star cstep (c1, st) (SKIP, st2)). apply ceval_to_csteps; auto.
  inversion ST; subst.
  SCase "Seq2 skip".
    exists c2; exists st2; split. 
    apply CS_SeqFinish.
    auto.
  SCase "Seq2 notskip".
    destruct b as [c1' st'].
    exists (c1';c2); exists st'; split.
    apply CS_SeqStep; auto.
    apply Einf_Seq_2 with st2. apply csteps_to_ceval; auto. auto.
Case "IfTrue".
  exists c1; exists st; split.
  apply CS_IfTrue; auto. 
  auto.
Case "IfFalse".
  exists c2; exists st; split.
  apply CS_IfFalse; auto. 
  auto.
Case "WhileBody".
  exists (IFB b THEN (c; (WHILE b DO c END)) ELSE SKIP FI); exists st; split.
  apply CS_While.
  apply Einf_IfTrue; auto. apply Einf_Seq_1; auto. 
Case "WhileLoop".
  exists (IFB b THEN (c; (WHILE b DO c END)) ELSE SKIP FI); exists st; split.
  apply CS_While.
  apply Einf_IfTrue; auto. apply Einf_Seq_2 with st'; auto.
Qed.

(** By iterating the lemma above "infinitely often", we can build
  an infinite sequence of reductions.  The actual proof is a coinductive argument,
  of course. *)

Lemma cevalinf_diverges:
  forall c st,
  c / st ==> ∞  ->  c / st --> ∞.
Proof.
  cofix COINDHYP; intros.
  destruct (cevalinf_can_progress c st H) as [c' [st' [A B]]]. 
  apply infseq_step with (c', st'). auto. apply COINDHYP. auto.
Qed.

(** Reverse implication: from infinite reduction sequences to coinductive big-step divergence.
  We start with a number of inversion lemmas to decompose infinite reduction
  sequences [ c / st --> ∞ ] into sub-sequences according to 
  the shape of the command [c] considered. *)

Lemma diverges_skip_impossible:
  forall st, ~(SKIP / st --> ∞).
Proof.
  intros; red; intros. inversion H; subst. inversion H0. 
Qed.

Lemma diverges_assign_impossible:
  forall v a st, ~((v ::= a) / st --> ∞).
Proof.
  intros; red; intros. inversion H; subst. inversion H0; subst.
  inversion H1; subst. inversion H2.
Qed.

Ltac inv H := inversion H; subst; clear H.

(** The following inversion lemma for sequences uses the fact that a reduction
  sequence is either infinite or finite, terminating on an irreducible state.
  This is intuitively obvious, but not provable in core Coq because only constructive
  proofs are accepted.  We need to use classical logic, namely the axiom of
  excluded middle, to obtain this proof.  See file [Sequences], theorem
  [infseq_or_finseq]. *)

Lemma diverges_seq_inversion:
  forall st c1 c2,
  (c1;c2) / st --> ∞  ->
  c1 / st --> ∞ \/ (exists st', c1 / st -->* SKIP / st' /\ c2 / st' --> ∞).
Proof.
  intros.
  destruct (infseq_or_finseq cstep (c1, st)) as [DIV1 | [[c' st'] [RED1 IRRED1]]].
Case "c1 diverges".
  auto.
Case "c1 terminates".
  assert ((c'; c2) / st' --> ∞). 
    eapply infseq_star_inv; eauto.
    intros; eapply cstep_deterministic; eauto.
    apply star_CS_SeqStep; auto.
  inv H0.
  inv H1.
  elim (IRRED1 _ H6).
  right; exists st'; auto.
Qed.

Lemma diverges_ifthenelse_inversion:
  forall b c1 c2 st,
  (IFB b THEN c1 ELSE c2 FI) / st --> ∞  ->
  (beval st b = true /\ c1 / st --> ∞) \/ (beval st b = false /\ c2 / st --> ∞).
Proof.
  intros. inv H. inv H0; auto.
Qed.

Lemma diverges_while_inversion:
  forall b c st,
  (WHILE b DO c END) / st --> ∞  ->
  beval st b = true /\
  (c / st --> ∞ \/ (exists st', c / st -->* SKIP / st' /\ (WHILE b DO c END) / st' --> ∞)).
Proof.
  intros. inv H. inv H0. inv H1. inv H. 
Case "b is true".
  split. auto. apply diverges_seq_inversion. auto.
Case "b is false".
  elim (diverges_skip_impossible _ H0).
Qed.

Lemma diverges_to_cevalinf:
  forall c st,  c / st --> ∞  ->  c / st ==> ∞.
Proof.
  cofix COINDHYP; intros.
  destruct c.
Case "skip".
  elim (diverges_skip_impossible _ H).
Case ":=".
  elim (diverges_assign_impossible _ _ _ H).
Case "seq".
  destruct (diverges_seq_inversion _ _ _ H) as [DIV1 | [st' [TERM1 DIV2]]]. 
  apply Einf_Seq_1. apply COINDHYP; auto.
  apply Einf_Seq_2 with st'. apply csteps_to_ceval; auto. apply COINDHYP; auto.
Case "if".
  destruct (diverges_ifthenelse_inversion _ _ _ _ H) as [[TRUE DIV1] | [FALSE DIV2]].
  apply Einf_IfTrue. auto. apply COINDHYP; auto.
  apply Einf_IfFalse. auto. apply COINDHYP; auto.
Case "while".
  destruct (diverges_while_inversion _ _ _ H) as [TRUE [DIV1 | [st' [TERM1 DIV2]]]].
  apply Einf_WhileBody. auto. apply COINDHYP; auto.
  apply Einf_WhileLoop with st'. auto. apply csteps_to_ceval; auto. apply COINDHYP; auto.
Qed.

(** * 4. Definitional interpreter *)

(** Yet another way to define the semantics of commands is via an interpreter:
  a function that computes the final state [st'] for a command [c]
  started in initial state [st].  As explained in the "Software Foundations"
  course, such a function must be parameterized by an integer [i]
  bounding the number of recursive calls of the interpreter.
  We recall the definition of the [ceval_step] interpreter given in
  file [Imp] of "Software Foundations":
<<
Fixpoint ceval_step (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ; c2 => 
          bind_option 
            (ceval_step st c1 i')
            (fun st' => ceval_step st' c2 i')
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) then ceval_step st c1 i' else ceval_step st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then bind_option 
                 (ceval_step st c1 i')
                 (fun st' => ceval_step st' c i')
          else Some st
    end
  end.
>>
*)

(** In file [Imp], it is shown that the definitional interpreter is
  equivalent to the big-step semantics for termination, in the following sense:
*)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st ==> st'.
Proof.
Admitted.

Theorem ceval__ceval_step: forall c st st',
      c / st ==> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
Admitted.

(** We now show a similar result for the coinductive big-step semantics
  for divergence. *)

Remark ceval__ceval_step_either:
  forall n c st st', c / st ==> st' -> ceval_step st c n = None \/ ceval_step st c n = Some st'.
Proof.
  intros. 
  destruct (ceval__ceval_step _ _ _ H) as [m EVAL].
  remember (ceval_step st c n). destruct o.
  right.
  assert (m <= n \/ n <= m) by lia.
  destruct H0. 
  assert (ceval_step st c n = Some st'). 
    apply ceval_step_more with m; auto.
  congruence.
  assert (ceval_step st c m = Some s).
    apply ceval_step_more with n; auto.
  congruence.
  left; auto.
Qed.

(** If [c] in [st] diverges according to the big-step rules,
  then the definitional interpreter returns [None] no matter how many
  recursive steps it is allowed to take. *)

Theorem cevalinf__ceval_step_bottom:
  forall n c st, c / st ==> ∞  -> ceval_step st c n = None.
Proof.
  induction n; intros; simpl.
Case "n = 0".
  auto.
Case "n > 0".
  inv H. 
SCase "seq 1".
  rewrite (IHn _ _ H0). auto.
SCase "seq 2".
  destruct (ceval__ceval_step_either n _ _ _ H0) as [A|A]; rewrite A.
  auto.
  simpl. apply IHn; auto.
SCase "if true".
  rewrite H0. apply IHn; auto.
SCase "if false".
  rewrite H0. apply IHn; auto.
SCase "while body".
  rewrite H0. rewrite (IHn _ _ H1). auto.
SCase "while loop".
  rewrite H0. 
  destruct (ceval__ceval_step_either n _ _ _ H1) as [A|A]; rewrite A.
  auto.
  simpl. apply IHn; auto.
Qed.

(** For the converse result, we again need a bit of classical logic
  (the axiom of excluded middle) to show that the sequence
  [n => ceval_step st c n] has a limit: it stabilizes to a fixed result
  when [n] is big enough. *)

Require Import Classical.
Require Import Max.

Lemma ceval_step_limit:
  forall st c,
  exists res, exists m, forall n, m <= n -> ceval_step st c n = res.
Proof.
  intros.
  destruct (classic (forall n, ceval_step st c n = None)).
Case "divergence".
  exists (@None state); exists 0; auto.
Case "convergence".
  assert (EX: exists m, ceval_step st c m <> None).
    apply not_all_ex_not. auto.
  destruct EX as [m EVAL].
  remember (ceval_step st c m) as res.
  destruct res as [st' | ]. 
  exists (Some st'); exists m; intros.
  apply ceval_step_more with m; auto. 
  congruence.
Qed.

(** From this lemma, it follows that a command for which the interpreter
  always returns [None] no matter how big the step limit is 
  does diverge according to the big-step semantics. *)

Theorem ceval_step_bottom__cevalinf:
  forall c st m,
  (forall n, m <= n -> ceval_step st c n = None) ->
  c / st ==> ∞.
Proof.
  cofix COINDHYP; intros.
  destruct c.
Case "skip".
  assert (ceval_step st SKIP (S m) = None). apply H. lia. 
  simpl in H0. congruence.
Case "assign".
  assert (ceval_step st (i ::= a) (S m) = None). apply H. lia. 
  simpl in H0. congruence.
Case "seq".
  destruct (ceval_step_limit st c1) as [res1 [m1 LIM1]].
  destruct res1 as [st1 | ].
  SCase "c1 converges".
  apply Einf_Seq_2 with st1.
  apply ceval_step__ceval. exists m1. apply LIM1. lia.
  apply COINDHYP with (max m m1). intros.
  assert (ceval_step st (c1; c2) (S n) = None).
    apply H. apply le_trans with (max m m1). apply le_max_l. lia.
  simpl in H1. rewrite LIM1 in H1. auto. apply le_trans with (max m m1). apply le_max_r. auto.
  SCase "c1 diverges".
  apply Einf_Seq_1. apply COINDHYP with m1. auto.
Case "if".
  remember (beval st b). destruct b0.
  SCase "if true".
  apply Einf_IfTrue. auto. apply COINDHYP with m. intros. 
  assert (ceval_step st (IFB b THEN c1 ELSE c2 FI) (S n) = None).
    apply H. lia.
  simpl in H1. rewrite <- Heqb0 in H1. auto.
  SCase "if false".
  apply Einf_IfFalse. auto. apply COINDHYP with m. intros. 
  assert (ceval_step st (IFB b THEN c1 ELSE c2 FI) (S n) = None).
    apply H. lia.
  simpl in H1. rewrite <- Heqb0 in H1. auto.
Case "while".
  remember (beval st b). destruct b0.
  destruct (ceval_step_limit st c) as [res1 [m1 LIM1]].
  destruct res1 as [st1 | ].
  SCase "body converges".
  apply Einf_WhileLoop with st1. auto.
  apply ceval_step__ceval. exists m1. apply LIM1. lia.
  apply COINDHYP with (max m m1). intros.
  assert (ceval_step st (WHILE b DO c END) (S n) = None).
    apply H. apply le_trans with (max m m1). apply le_max_l. lia.
  simpl in H1. rewrite <- Heqb0 in H1. rewrite LIM1 in H1. auto. apply le_trans with (max m m1). apply le_max_r. auto.
  SCase "body diverges".
  apply Einf_WhileBody. auto. apply COINDHYP with m1. auto.
  SCase "condition is false".
  assert (ceval_step st (WHILE b DO c END) (S m) = None).
    apply H. lia.
  simpl in H0. rewrite <- Heqb0 in H0. congruence.
Qed.

(** * 5. From a definitional interpreter to a denotational semantics *)

(** Using yet another bit of logic (an axiom of description -- a variant
  of the axiom of choice), we can show the existence of a function
  [denot st c] which is the limit of the sequence [n => ceval_step st c n]
  as [n] goes to infinity.  The result of this function is to be
  interpreted as the denotation of command [c] in state [st]:
- [denot st c = None] (or "bottom") means that [c] diverges
- [denot st c = Some st'] means that [c] terminates with final state [st'].
*)

Require Import ClassicalDescription.

Definition interp_limit_dep (st: state) (c: com) :
  { res: option state | exists m, forall n, m <= n -> ceval_step st c n = res}.
Proof.
  intros. apply constructive_definite_description. 
  destruct (ceval_step_limit st c) as [res X]. 
  exists res. red. split. auto. intros res' X'. 
  destruct X as [m P]. destruct X' as [m' P']. 
  transitivity (ceval_step st c (max m m')).
  symmetry. apply P. apply le_max_l.
  apply P'. apply le_max_r.
Qed.

Definition denot (st: state) (c: com) : option state :=
  proj1_sig (interp_limit_dep st c).

Lemma denot_limit:
  forall st c,
  exists m, forall n, m <= n -> ceval_step st c n = denot st c.
Proof.
  intros. unfold denot. apply proj2_sig.
Qed.

Lemma denot_charact:
  forall st c m res,
  (forall n, m <= n -> ceval_step st c n = res) ->
  denot st c = res.
Proof.
  intros. destruct (denot_limit st c) as [m' I].
  assert (ceval_step st c (max m m') = res).
    apply H. apply le_max_l.
  assert (ceval_step st c (max m m') = denot st c).
    apply I. apply le_max_r.
  congruence.
Qed.

Lemma denot_terminates:
  forall st c n st', ceval_step st c n = Some st' -> denot st c = Some st'.
Proof.
  intros.
  apply denot_charact with n. intros. apply ceval_step_more with n; auto.
Qed.

(** We can then show that this [denot] function satisfies the equations of
  denotational semantics for the Imp language. *)

Lemma denot_skip:
  forall st, denot st SKIP = Some st.
Proof.
  intros. apply denot_terminates with 1. simpl. auto.
Qed.

Lemma denot_assign:
  forall v a st, denot st (v ::= a) = Some (update st v (aeval st a)).
Proof.
  intros. apply denot_terminates with 1. simpl. auto.
Qed.

Lemma denot_seq:
  forall c1 c2 st, 
  denot st (c1;c2) = bind_option (denot st c1) (fun st' => denot st' c2).
Proof.
  intros. destruct (denot_limit st c1) as [m1 LIM1].
  destruct (denot st c1) as [st' | ]; simpl.
Case "c1 terminates".
  destruct (denot_limit st' c2) as [m2 LIM2].
  apply denot_charact with (S (max m1 m2)). intros. 
  destruct n. elimtype False; lia. 
  simpl. rewrite LIM1; simpl. apply LIM2. 
  apply le_trans with (max m1 m2). apply le_max_r. lia.
  apply le_trans with (max m1 m2). apply le_max_l. lia.
Case "c1 diverges".
  apply denot_charact with (S m1); intros.
  destruct n. elimtype False; lia. 
  simpl. rewrite LIM1; simpl. auto. lia.
Qed.

Lemma denot_ifthenelse:
  forall b c1 c2 st,
  denot st (IFB b THEN c1 ELSE c2 FI) =
  if beval st b then denot st c1 else denot st c2.
Proof.
  intros. 
  remember (beval st b). destruct b0.
Case "b is true".
  destruct (denot_limit st c1) as [m LIM].
  apply denot_charact with (S m); intros.
  destruct n. elimtype False; lia. 
  simpl. rewrite <- Heqb0. apply LIM. lia.
Case "b is false".
  destruct (denot_limit st c2) as [m LIM].
  apply denot_charact with (S m); intros.
  destruct n. elimtype False; lia. 
  simpl. rewrite <- Heqb0. apply LIM. lia.
Qed.

Lemma denot_while:
  forall b c st,
  denot st (WHILE b DO c END) =
  if beval st b
  then bind_option (denot st c) (fun st' => denot st' (WHILE b DO c END))
  else Some st.
Proof.
  intros. remember (beval st b). destruct b0.
Case "b is true".
  destruct (denot_limit st c) as [m1 LIM1].
  destruct (denot st c) as [st' | ]; simpl.
SCase "c terminates".
  destruct (denot_limit st' (WHILE b DO c END)) as [m2 LIM2].
  apply denot_charact with (S (max m1 m2)). intros. 
  destruct n. elimtype False; lia. 
  simpl. rewrite <- Heqb0. rewrite LIM1; simpl. apply LIM2. 
  apply le_trans with (max m1 m2). apply le_max_r. lia.
  apply le_trans with (max m1 m2). apply le_max_l. lia.
SCase "c diverges".
  apply denot_charact with (S m1); intros.
  destruct n. elimtype False; lia. 
  simpl. rewrite <- Heqb0. rewrite LIM1; simpl. auto. lia.
Case "b is false".
  apply denot_terminates with 1. simpl. rewrite <- Heqb0. auto.
Qed.

(** Moreover, [denot st (WHILE b DO c END)] is the least fixpoint of the equation above. *)

Definition result_less_defined (r1 r2: option state) : Prop :=
  r1 = None \/ r1 = r2.

Lemma denot_while_least_fixpoint:
  forall b c (f: state -> option state),
  (forall st,
   f st = if beval st b then bind_option (denot st c) f else Some st) ->
  (forall st,
   result_less_defined (denot st (WHILE b DO c END)) (f st)).
Proof.
  intros. 
  assert (forall n st, result_less_defined (ceval_step st (WHILE b DO c END) n) (f st)).
    induction n; intros; simpl.
    red; auto.
    rewrite (H st0). destruct (beval st0 b). 
    remember (ceval_step st0 c n). destruct o; simpl.
    replace (denot st0 c) with (Some s).
    apply IHn. symmetry. eapply denot_terminates; eauto. 
    red; auto.
    red; auto.
  destruct (denot_limit st (WHILE b DO c END)) as [m LIM].
  rewrite <- (LIM m). auto. lia.
Qed.

(** **** Exercise (2 stars). *)
(** Show that the denotational semantics for loops is compositional: *)

Lemma denot_while_compositional:
  forall b c1 c2,
  (forall st, denot st c1 = denot st c2) ->
  (forall st, denot st (WHILE b DO c1 END) = denot st (WHILE b DO c2 END)).
Proof.
  (* FILL IN HERE *)
Admitted.


(** Composing the various results so far, we obtain the following equivalences
  between the denotational semantics and the big-step semantics. *)

Lemma denot_ceval:
  forall c st st',
  c / st ==> st'  <->  denot st c = Some st'.
Proof.
  intros; split; intros.
Case "->".
  destruct (ceval__ceval_step _ _ _ H) as [m EVAL].
  apply denot_terminates with m; auto.
Case "<-".
  destruct (denot_limit st c) as [m LIMIT].
  apply ceval_step__ceval.  exists m. rewrite <- H. apply LIMIT. lia.
Qed.

Lemma denot_cevalinf:
  forall c st,
  c / st ==> ∞  <-> denot st c = None.
Proof.
  intros; split; intros.
Case "->".
  apply denot_charact with 0. intros. apply cevalinf__ceval_step_bottom. auto.
Case "<-".
  destruct (denot_limit st c) as [m LIMIT]. 
  apply ceval_step_bottom__cevalinf with m. intros. rewrite <- H. apply LIMIT; auto.
Qed.









  

