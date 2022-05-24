Require Import Coq.Program.Equality.
Require Import Lia.
From SF Require Import Imp.
From SF Require Import Sequences.
From SF Require Import Semantics.
From SF Require Import Compil.

(** In this chapter, we prove semantic preservation for the IMP-to-VM compiler
  using small-step semantics for IMP instead of (coinductive) big-step semantics
  as in chapter [Compil].  *)

(** * 1. Alternate compilation scheme for commands. *)

(** The compilation scheme for commands presented in chapter [Compil]
  raises so-called "stuttering" problems in the proof of forward simulation,
  in the case of loops.  We define an alternate compilation scheme that
  avoids this problem.  The only change is the insertion of an extra
  branch instruction at the beginning of the code generated for a while loop. *)

Fixpoint compile_com (c: com) : code :=
  match c with
  | CSkip =>
      nil
  | CAss id a =>
      compile_aexp a ++ Isetvar id :: nil
  | CSeq c1 c2 =>
      compile_com c1 ++ compile_com c2
  | CIf b ifso ifnot =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b false (length code_ifso + 1)
      ++ code_ifso
      ++ Ibranch_forward (length code_ifnot)
      :: code_ifnot
  | CWhile b body =>
      let code_body := compile_com body in
      let code_test := compile_bexp b false (length code_body + 1) in
      Ibranch_backward 0                  (**r new! added dummy branch *)
      :: code_test
      ++ code_body
      ++ Ibranch_backward (length code_test + length code_body + 1)
      :: nil
  end.

Definition compile_program (p: com) : code :=
  compile_com p ++ Ihalt :: nil.

(** * 2. Relational specification of the compiled code. *)

(** As explained in the slides, we need to generalize the condition
<<
       codeseq_at C pc (compile_com c)
>>
    previously used to relate the machine code with the command [c].
    We adopt the following relational specification.
    [spec_compile_com C c pc1 pc2] holds if code [c] contains
    a path of instructions, starting at position [pc1], ending at
    position [pc2], and "spelling out" the instructions needed
    to execute command [c].  The main difference with the 
    functional specification [compile_com] is that we allow unconditional
    branches to be inserted (nondeterministically) in the machine code.
    (See cases [scc_branch_forward] and [scc_branch_backward] below.)
*)

Inductive spec_compile_com (C: code): com -> nat -> nat -> Prop :=
  | scc_skip: forall pc,
      spec_compile_com C SKIP pc pc
  | scc_ass: forall id a pc,
      codeseq_at C pc (compile_aexp a) ->
      code_at C (pc + length (compile_aexp a)) = Some(Isetvar id) ->
      spec_compile_com C (id ::= a) pc (pc + length (compile_aexp a) + 1)
  | scc_seq: forall c1 c2 pc1 pc2 pc3,
      spec_compile_com C c1 pc1 pc2 ->
      spec_compile_com C c2 pc2 pc3 ->
      spec_compile_com C (c1;c2) pc1 pc3
  | scc_if: forall b ifso ifnot pc pc' ofs,
      let code_test := compile_bexp b false ofs in
      codeseq_at C pc code_test ->
      spec_compile_com C ifso (pc + length code_test) pc' ->
      spec_compile_com C ifnot (pc + length code_test + ofs) pc' ->
      spec_compile_com C (IFB b THEN ifso ELSE ifnot FI) pc pc'
  | scc_while: forall b body pc1 pc2 pc3 pc4 ofs1 ofs2 ofs3,
      let code_test := compile_bexp b false ofs3 in
      code_at C pc1 = Some(Ibranch_backward ofs1) ->
      pc2 = pc1 + 1 - ofs1 ->
      codeseq_at C pc2 code_test ->
      spec_compile_com C body (pc2 + length code_test) pc3 ->
      code_at C pc3 = Some(Ibranch_backward ofs2) ->
      pc2 + length code_test + ofs3 = pc4 ->
      pc3 + 1 - ofs2 = pc2 ->
      spec_compile_com C (WHILE b DO body END) pc1 pc4
  | scc_branch_forward: forall c pc pc1 pc2 ofs,
      spec_compile_com C c pc pc1 ->
      code_at C pc1 = Some(Ibranch_forward ofs) ->
      pc2 = pc1 + 1 + ofs ->
      spec_compile_com C c pc pc2
  | scc_branch_backward: forall c pc pc1 pc2 ofs,
      spec_compile_com C c pc pc1 ->
      code_at C pc1 = Some(Ibranch_backward ofs) ->
      pc2 = pc1 + 1 - ofs ->
      spec_compile_com C c pc pc2.

Lemma compile_com_meets_spec:
  forall C c pc,
  codeseq_at C pc (compile_com c) ->
  spec_compile_com C c pc (pc + length (compile_com c)).
Proof.
  induction c; simpl; intros.
(* Case SKIP *)
  rewrite plus_0_r. constructor.
(* Case := *)
  normalize. constructor; eauto with codeseq.
(* Case seq *)
  normalize. eapply scc_seq.
  apply IHc1. eauto with codeseq.
  apply IHc2. eauto with codeseq.
(* Case if *)
  normalize. eapply scc_if. eauto with codeseq.
  eapply scc_branch_forward. apply IHc1. eauto with codeseq. 
  eauto with codeseq. lia.
  replace (S (length (compile_com c2))) with (1 + length (compile_com c2)).
  normalize. apply IHc2. eauto with codeseq. 
  lia.
(* Case while *)
  normalize. eapply scc_while. eauto with codeseq.
  eauto. rewrite <- minus_n_O. eauto with codeseq.
  rewrite <- minus_n_O. apply IHc. eauto with codeseq.
  eauto with codeseq. 
  lia.
  lia.
Qed.

(** * 3. Forward simulation diagram. *)

(** We are about to prove forward simulation using a simulation diagram
  of the following shape:
<<
                  match_states
     c / st  ----------------------- machstate
       |                                |
       |                                | + or ( * and |c'| < |c| )
       |                                |
       v                                v
    c' / st' ----------------------- machstate'
                  match_states 
>>
Hypotheses:
- Left: one reduction in the small-step semantics of IMP.
- Top: the [match_state] predicate defined below.
Conclusions:
- Bottom: the [match_state] predicate again (invariant).
- Right: either 
--  one or several VM transitions in the compiled code
--  or zero, one or several VM transitions + a proof that the measure of c decreases
*)

Inductive match_state (C: code): com * state -> machine_state -> nat -> Prop :=
  | match_state_intro: 
      forall c st pc1 pc2 (SCC: spec_compile_com C c pc1 pc2),
      match_state C (c, st) (pc1, nil, st) pc2.

Fixpoint com_size (c: com) : nat :=
  match c with
  | CSkip => 1
  | CAss id a => 1
  | CSeq c1 c2 => com_size c1 + com_size c2 + 1
  | CIf b ifso ifnot => com_size ifso + com_size ifnot + 1
  | CWhile b body => com_size body + 1
  end.

Definition measure (cs: com * state) : nat := com_size (fst cs).

Definition cstep_simulation_diagram (C: code) (cs1 cs2: com * state) (S1: machine_state) (target: nat) : Prop :=
  exists S2,
  (plus (transition C) S1 S2 \/ (measure cs2 < measure cs1 /\ star (transition C) S1 S2))
  /\ match_state C cs2 S2 target.

Remark cstep_simulation_branch_forward:
  forall C pc ofs pc' S1 cs1 cs2,
  code_at C pc = Some(Ibranch_forward ofs) ->
  pc' = pc + 1 + ofs ->
  cstep_simulation_diagram C cs1 cs2 S1 pc ->
  cstep_simulation_diagram C cs1 cs2 S1 pc'.
Proof.
  intros. destruct H1 as [S2 [A MS]]. inv MS.
  exists (pc1, [], st); split. auto.
  constructor. eapply scc_branch_forward; eauto. 
Qed.

Remark cstep_simulation_branch_backward:
  forall C pc ofs pc' S1 cs1 cs2,
  code_at C pc = Some(Ibranch_backward ofs) ->
  pc' = pc + 1 - ofs ->
  cstep_simulation_diagram C cs1 cs2 S1 pc ->
  cstep_simulation_diagram C cs1 cs2 S1 pc'.
Proof.
  intros. destruct H1 as [S2 [A MS]]. inv MS.
  exists (pc1, [], st); split. auto.
  constructor. eapply scc_branch_backward; eauto. 
Qed.

Remark spec_compile_com_SKIP:
  forall C stk st pc1 pc2,
  spec_compile_com C SKIP pc1 pc2 ->
  star (transition C) (pc1, stk, st) (pc2, stk, st).
Proof.
  intros. dependent induction H. 
  apply star_refl.
  eapply star_trans. eauto. apply star_one. apply trans_branch_forward with ofs; auto.
  eapply star_trans. eauto. apply star_one. apply trans_branch_backward with ofs; auto.
Qed.

(** The proof of the forward simulation diagram is by induction on the
  reduction [c1 / st1 --> c2 / st2] and an inner induction on the
  [spec_compile_com] relation. *)

Lemma cstep_simulation:
  forall C cs1 cs2,
  cstep cs1 cs2 ->
  forall S1 target,
  match_state C cs1 S1 target ->
  cstep_simulation_diagram C cs1 cs2 S1 target.
Proof.
  pose (CSBF := cstep_simulation_branch_forward).
  pose (CSBB := cstep_simulation_branch_backward).
  induction 1; intros S1 target MS; inv MS; dependent induction SCC; eauto.
(* Case CS_Ass *)
  econstructor; split.
  left. eapply star_plus_trans. 
  apply compile_aexp_correct; eauto. 
  apply plus_one. apply trans_setvar. eauto with codeseq. 
  econstructor. constructor.
(* Case CS_SeqStep *)
  destruct (IHcstep (pc1, nil, st) pc2) as [S2 [EXEC MS']]. 
    constructor. auto.
  exists S2; split.
  unfold measure in *; simpl in *. intuition lia. 
  inv MS'. constructor. econstructor; eauto.
(* Case CS_SeqFinish *)
  exists (pc2, nil, st); split.
  right; split. unfold measure; simpl. lia. apply spec_compile_com_SKIP. auto.
  constructor; auto. 
(* Case CS_IfTrue *)
  econstructor; split.
  right; split. 
  unfold measure; simpl. lia.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := ofs). auto.
  rewrite H. simpl. rewrite plus_0_r. fold code_test. constructor. auto.
(* Case CS_IfFalse *)
  econstructor; split.
  right; split.
  unfold measure; simpl. lia.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := ofs). auto.
  rewrite H. simpl. fold code_test. constructor; auto.
(* Case CS_While *)
  exists (pc1 + 1 -ofs1, nil, st); split.
  left. apply plus_one. apply trans_branch_backward with ofs1. eauto with codeseq. auto.
  constructor. 
  eapply scc_if. eauto. 
  eapply scc_seq. eauto.
  eapply scc_while. eauto. eauto. rewrite H4. eauto. rewrite H4. eauto. eauto. 
  fold code_test. lia. auto.  
  apply scc_skip.
Qed.

(** As a corollary, we obtain the following diagram,
  which will prove forward simulation in the terminating case.

<<
                  match_states
     c / st  ----------------------- machstate
       |                                |
     * |                                | *
       |                                |
       v                                v
    c' / st' ----------------------- machstate'
                  match_states 
>>
*)

Lemma cstep_simulation_star:
  forall C cs1 cs2,
  star cstep cs1 cs2 ->
  forall S1 target,
  match_state C cs1 S1 target ->
  exists S2, star (transition C) S1 S2 /\ match_state C cs2 S2 target.
Proof.
  induction 1; intros.
  exists S1; split. apply star_refl. auto.
  destruct (cstep_simulation _ _ _ H _ _ H1) as [S2 [EXEC1 MS1]].
  destruct (IHstar _ _ MS1) as [S3 [EXEC2 MS2]].
  exists S3; split.
  eapply star_trans; eauto. 
  destruct EXEC1 as [PLUS | [MEAS STAR]]. 
  inv PLUS. econstructor; eauto. 
  auto.
  auto.
Qed.

Lemma match_initial_state:
  forall c st,
  match_state (compile_program c) (c, st) (0, nil, st) (length (compile_com c)).
Proof.
  intros. constructor. 
  apply compile_com_meets_spec with (pc := 0). 
  unfold compile_program. apply codeseq_at_intro with (C1 := nil). auto.
Qed.

Theorem compile_program_correct_terminating:
  forall c st st',
  c / st -->* SKIP / st' ->
  mach_terminates (compile_program c) st st'.
Proof.
  intros.
  generalize (match_initial_state c st); intro.
  destruct (cstep_simulation_star _ _ _ H _ _ H0) as [S2 [STAR MS]]. 
  inv MS.
  red. exists (length (compile_com c)); split.
  unfold compile_program. apply code_at_app. auto.
  eapply star_trans. apply STAR. apply spec_compile_com_SKIP; auto.
Qed.

(** To prove forward simulation in the diverging case, we first show
  that the machine can always make progress if the source command
  diverges.  The proof is an induction on the maximal number [m]
  of stutterings that the machine can make before taking at least one transition. *)

Lemma cstep_simulation_productive:
  forall C m cs1 S1 target,
  measure cs1 < m ->
  infseq cstep cs1 ->
  match_state C cs1 S1 target ->
  exists cs2, exists S2,
     infseq cstep cs2
  /\ plus (transition C) S1 S2
  /\ match_state C cs2 S2 target.
Proof.
  induction m; intros.
  elimtype False; lia.
  inv H0. rename b into cs2. 
  destruct (cstep_simulation _ _ _ H2 _ _ H1) as [S2 [EXEC1 MS1]].
  destruct EXEC1 as [PLUS | [MEAS STAR]].
  exists cs2; exists S2; auto.
  inv STAR. 
  apply IHm with cs2. lia. auto. auto. 
  exists cs2; exists S2; intuition. econstructor; eauto.
Qed.

Lemma cstep_simulation_infseq:
  forall C cs S target,
  infseq cstep cs ->
  match_state C cs S target ->
  infseq (transition C) S.
Proof.
  intros. 
  apply infseq_coinduction_principle_2 with (X := fun S => exists cs, infseq cstep cs /\ match_state C cs S target).
  intros. destruct H1 as [cs1 [A B]]. 
  destruct (cstep_simulation_productive C (measure cs1 + 1) cs1 a target) as [cs2 [S2 [P [Q R]]]].
  lia. auto. auto. 
  exists S2; split. auto. exists cs2; auto.
  exists cs; auto.
Qed.

Theorem compile_program_correct_diverging:
  forall c st,
  c / st --> ∞  ->
  mach_diverges (compile_program c) st.
Proof.
  intros. red. 
  apply cstep_simulation_infseq with (c, st) (length (compile_com c)).
  auto. apply match_initial_state. 
Qed.
