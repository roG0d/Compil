Require Import Coq.Program.Equality.
Require Import Lia.
From SF Require Import Imp.
From SF Require Import Sequences.
From SF Require Import Semantics.





(** This chapter defines a compiler from the Imp language to a virtual machine
  (a small subset of the Java Virtual Machine) and proves that this
  compiler preserves the semantics of the source programs. *)

(** * 1. The virtual machine. *)

(** The machine operates on a code [c] (a fixed list of instructions)
  and three variable components:
- a program counter, denoting a position in [c]
- a state assigning integer values to variables
- an evaluation stack, containing integers.
*)

(** The instruction set of the machine. *)

Inductive instruction: Type :=
  | Iconst(n: nat)                 (**r push integer [n] on stack *)
  | Ivar(x: id)                    (**r push the value of variable [x] *)
  | Isetvar(x: id)                 (**r pop an integer, assign it to variable [x] *)
  | Iadd                           (**r pop [n2], pop [n1], push back [n1+n2] *)
  | Isub                           (**r pop [n2], pop [n1], push back [n1-n2] *)
  | Imul                           (**r pop [n2], pop [n1], push back [n1*n2] *)
  | Ibranch_forward(ofs: nat)      (**r skip [ofs] instructions forward *)
  | Ibranch_backward(ofs: nat)     (**r skip [ofs] instructions backward *)
  | Ibeq(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1=n2] *)
  | Ibne(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<>n2] *)
  | Ible(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<=n2] *)
  | Ibgt(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1>n2] *)
  | Ihalt.                         (**r terminate execution successfully *)

Definition code := list instruction.

(** [code_at C pc = Some i] if [i] is the instruction at position [pc]
  in the list of instructions [C]. *)

Fixpoint code_at (C: code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i :: C', O => Some i
  | i :: C', S pc' => code_at C' pc'
  end.

Definition stack := list nat.

(** The semantics of the virtual machine is given in small-step style,
  as a transition relation between machine states: triples
  (program counter, evaluation stack, variable state).
  The transition relation is parameterized by the code [c].
  There is one transition rule for each kind of instruction,
  except [Ihalt], which has no transition. *)

Definition machine_state := (nat * stack * state)%type.

Inductive transition (C: code): machine_state -> machine_state -> Prop :=
  | trans_const: forall pc stk s n,
      code_at C pc = Some(Iconst n) ->
      transition C (pc, stk, s) (pc + 1, n :: stk, s)
  | trans_var: forall pc stk s x,
      code_at C pc = Some(Ivar x) ->
      transition C (pc, stk, s) (pc + 1, s x :: stk, s)
  | trans_setvar: forall pc stk s x n,
      code_at C pc = Some(Isetvar x) ->
      transition C (pc, n :: stk, s) (pc + 1, stk, update s x n)
  | trans_add: forall pc stk s n1 n2,
      code_at C pc = Some(Iadd) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 + n2) :: stk, s)
  | trans_sub: forall pc stk s n1 n2,
      code_at C pc = Some(Isub) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 - n2) :: stk, s)
  | trans_mul: forall pc stk s n1 n2,
      code_at C pc = Some(Imul) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 * n2) :: stk, s)
  | trans_branch_forward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      transition C (pc, stk, s) (pc', stk, s)
  | trans_branch_backward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      transition C (pc, stk, s) (pc', stk, s)
  | trans_beq: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibeq ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bne: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibne ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_ble: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ible ofs) ->
      pc' = (if ble_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bgt: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibgt ofs) ->
      pc' = (if ble_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s).

(** As usual with small-step semantics, we form sequences of machine transitions
  to define the behavior of a code.  We always start with [pc = 0]
  and an empty evaluation stack.  We stop successfully if [pc] points
  to an [Ihalt] instruction and the evaluation stack is empty.

  If [R] is a binary relation, [star R] is its reflexive transitive closure.
  (See file [Sequences] for the definition.)  [star (transition C)]
  therefore represents a sequence of  zero, one or several machine transitions.
*)

Definition mach_terminates (C: code) (s_init s_fin: state) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, nil, s_init) (pc, nil, s_fin).


(** Likewise, [infseq R] represents an infinite sequence of [R] transitions.
  (Also defined in file [Sequences].) *)

Definition mach_diverges (C: code) (s_init: state) :=
  infseq (transition C) (0, nil, s_init).

Definition mach_goes_wrong (C: code) (s_init: state) :=
  exists pc, exists stk, exists s_fin,
  star (transition C) (0, nil, s_init) (pc, stk, s_fin)
  /\ irred (transition C) (pc, stk, s_fin)
  /\ (code_at C pc <> Some Ihalt \/ stk <> nil).

(** **** Exercise (1 star). *)
(** Note that unlike the small-step semantics for Imp, the machine
  can go wrong. Here are some examples: *)

Lemma wrong_program_example_1:
  forall st, mach_goes_wrong (Iadd :: nil) st.
Proof.
  intros. unfold mach_goes_wrong.
  (* FILL IN HERE *)
Admitted.

Lemma wrong_program_example_2:
  forall st, mach_goes_wrong (Ibranch_forward 2 :: nil) st.
Proof.
  intros. unfold mach_goes_wrong.
  (* FILL IN HERE *)
Admitted.

(** * 2. The compilation scheme *)

(** The code for an arithmetic expression [a]
- executes in sequence (no branches)
- deposits the value of [a] at the top of the stack
- preserves the variable state.

This is the familiar translation to "reverse Polish notation".
*)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | ANum n => Iconst n :: nil
  | AId v => Ivar v :: nil
  | APlus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | AMinus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Isub :: nil
  | AMult a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Imul :: nil
  end.

(** Some examples. *)

Notation vx := (Id 0).
Notation vy := (Id 1).

Eval compute in (compile_aexp (APlus (AId vx) (ANum 1))).

Eval compute in (compile_aexp (AMult (AId vy) (APlus (AId vx) (ANum 1)))).

(** The code [compile_bexp b cond ofs] for a boolean expression [b]
- skips forward the [ofs] following instructions if [b] evaluates to [cond] (a boolean)
- executes in sequence if [b] evaluates to the negation of [cond]
- leaves the stack and the variable state unchanged.

See slides for explanation of the mysterious branch offsets!
*)

Fixpoint compile_bexp (b: bexp) (cond: bool) (ofs: nat) : code :=
  match b with
  | BTrue =>
      if cond then Ibranch_forward ofs :: nil else nil
  | BFalse =>
      if cond then nil else Ibranch_forward ofs :: nil
  | BEq a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ibeq ofs :: nil else Ibne ofs :: nil)
  | BLe a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ible ofs :: nil else Ibgt ofs :: nil)
  | BNot b1 =>
      compile_bexp b1 (negb cond) ofs
  | BAnd b1 b2 =>
      let c2 := compile_bexp b2 cond ofs in
      let c1 := compile_bexp b1 false (if cond then length c2 else ofs + length c2) in
      c1 ++ c2
  end.

(** Examples. *)

Eval compute in (compile_bexp (BEq (AId vx) (ANum 1)) true 42).

Eval compute in (compile_bexp (BAnd (BLe (ANum 1) (AId vx)) (BLe (AId vx) (ANum 10))) false 42).

Eval compute in (compile_bexp (BNot (BAnd BTrue BFalse)) true 42).

(** The code for a command [c]
- updates the variable state as prescribed by [c]
- preserves the stack
- finishes on the next instruction immediately following the generated code.

Again, see slides for explanations of the generated branch offsets.
*)

Fixpoint compile_com (c: com) : code :=
  match c with
  | SKIP =>
      nil
  | (id ::= a) =>
      compile_aexp a ++ Isetvar id :: nil
  | (c1; c2) =>
      compile_com c1 ++ compile_com c2
  | IFB b THEN ifso ELSE ifnot FI =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b false (length code_ifso + 1)
      ++ code_ifso
      ++ Ibranch_forward (length code_ifnot)
      :: code_ifnot
  | WHILE b DO body END =>
      let code_body := compile_com body in
      let code_test := compile_bexp b false (length code_body + 1) in
      code_test
      ++ code_body
      ++ Ibranch_backward (length code_test + length code_body + 1)
      :: nil
  end.

(** The code for a program [p] (a command) is similar, but terminates
  cleanly on an [Ihalt] instruction. *)

Definition compile_program (p: com) : code :=
  compile_com p ++ Ihalt :: nil.

(** Examples of compilation: *)

Eval compute in (compile_program (vx ::= APlus (AId vx) (ANum 1))).

Eval compute in (compile_program (WHILE BTrue DO SKIP END)).

Eval compute in (compile_program (IFB BEq (AId vx) (ANum 1) THEN vx ::= ANum 0 ELSE SKIP FI)).

(** **** Exercise (1 star) *)
(** The last example shows a slight inefficiency in the code generated for
  [IFB ... THEN ... ELSE SKIP FI].  How would you change [compile_com]
  to generate better code?  Hint: ponder the following function. *)

Definition smart_Ibranch_forward (ofs: nat) : code :=
  if beq_nat ofs 0 then nil else Ibranch_forward(ofs) :: nil.

(** * 3. Semantic preservation *)

(** ** Auxiliary results about code sequences. *)

(** To reason about the execution of compiled code, we need to consider
  code sequences [C2] that are at position [pc] in a bigger code
  sequence [C = C1 ++ C2 ++ C3].  The following predicate
  [codeseq_at C pc C2] does just this. *)

Inductive codeseq_at: code -> nat -> code -> Prop :=
  | codeseq_at_intro: forall C1 C2 C3 pc,
      pc = length C1 ->
      codeseq_at (C1 ++ C2 ++ C3) pc C2.

(** We show a number of no-brainer lemmas about [code_at] and [codeseq_at],
  then populate a "hint database" so that Coq can use them automatically. *)

Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 ->
  code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc; auto.
Qed.

Lemma codeseq_at_head:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  code_at C pc = Some i.
Proof.
  intros. inv H. simpl. apply code_at_app. auto.
Qed.

Lemma codeseq_at_tail:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  codeseq_at C (pc + 1) C'.
Proof.
  intros. inv H. 
  change (C1 ++ (i :: C') ++ C3)
    with (C1 ++ (i :: nil) ++ C' ++ C3).
  rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed. 

Lemma codeseq_at_app_left:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C pc C1.
Proof.
  intros. inv H. rewrite app_ass. constructor. auto.
Qed.

Lemma codeseq_at_app_right:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inv H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Lemma codeseq_at_app_right2:
  forall C pc C1 C2 C3,
  codeseq_at C pc (C1 ++ C2 ++ C3) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inv H. repeat rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

#[global] Hint Resolve codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2: codeseq.

Ltac normalize :=
  repeat rewrite app_length; repeat rewrite plus_assoc; simpl.

(** ** Correctness of generated code for expressions. *)

(** Remember the informal specification we gave for the code generated
  for an arithmetic expression [a].  It should
- execute in sequence (no branches)
- deposit the value of [a] at the top of the stack
- preserve the variable state.

We now prove that the code [compile_aexp a] fulfills this contract.
The proof is a nice induction on the structure of [a]. *)

Lemma compile_aexp_correct:
  forall C st a pc stk,
  codeseq_at C pc (compile_aexp a) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_aexp a), aeval st a :: stk, st).
Proof.
  induction a; simpl; intros.

Case ANum.
  apply star_one. apply trans_const. eauto with codeseq. 

Case AId.
  apply star_one. apply trans_var. eauto with codeseq. 

Case APlus.
  eapply star_trans.
  apply IHa1. eauto with codeseq. 
  eapply star_trans.
  apply IHa2. eauto with codeseq. 
  apply star_one. normalize. apply trans_add. eauto with codeseq. 

Case AMinus.
  eapply star_trans.
  apply IHa1. eauto with codeseq. 
  eapply star_trans.
  apply IHa2. eauto with codeseq. 
  apply star_one. normalize. apply trans_sub. eauto with codeseq. 

Case AMult.
  eapply star_trans.
  apply IHa1. eauto with codeseq. 
  eapply star_trans.
  apply IHa2. eauto with codeseq. 
  apply star_one. normalize. apply trans_mul. eauto with codeseq. 
Qed.

(** Here is a similar proof for the compilation of boolean expressions. *)

Lemma compile_bexp_correct:
  forall C st b cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_bexp b cond ofs) + if eqb (beval st b) cond then ofs else 0, stk, st).
Proof.
  induction b; simpl; intros.

Case BTrue.
  destruct cond; simpl.
  SCase true.
    apply star_one. apply trans_branch_forward with ofs. eauto with codeseq. auto.
  SCase false.
    repeat rewrite plus_0_r. apply star_refl.
 
Case BFalse.
  destruct cond; simpl.
  SCase true.
    repeat rewrite plus_0_r. apply star_refl.
  SCase  false.
    apply star_one. apply trans_branch_forward with ofs. eauto with codeseq. auto.

Case BEq.
  eapply star_trans. 
  apply compile_aexp_correct with (a := a). eauto with codeseq. 
  eapply star_trans.
  apply compile_aexp_correct with (a := a0). eauto with codeseq. 
  apply star_one. normalize.
  destruct cond.
  SCase true.
    apply trans_beq with ofs. eauto with codeseq.
    destruct (beq_nat (aeval st a) (aeval st a0)); simpl; lia.
  SCase false.
    apply trans_bne with ofs. eauto with codeseq. 
    destruct (beq_nat (aeval st a) (aeval st a0)); simpl; lia.

Case BLe.
  eapply star_trans. 
  apply compile_aexp_correct with (a := a). eauto with codeseq. 
  eapply star_trans.
  apply compile_aexp_correct with (a := a0). eauto with codeseq. 
  apply star_one. normalize.
  destruct cond.
  SCase  true.
    apply trans_ble with ofs. eauto with codeseq.
    destruct (ble_nat (aeval st a) (aeval st a0)); simpl; lia.
  SCase false.
    apply trans_bgt with ofs. eauto with codeseq. 
    destruct (ble_nat (aeval st a) (aeval st a0)); simpl; lia.

Case BNot.
  replace (eqb (negb (beval st b)) cond)
     with (eqb (beval st b) (negb cond)).
  apply IHb; auto. 
  destruct (beval st b); destruct cond; auto.

Case BAnd.
  set (code_b2 := compile_bexp b2 cond ofs) in *.
  set (ofs' := if cond then length code_b2 else ofs + length code_b2) in *.
  set (code_b1 := compile_bexp b1 false ofs') in *.
  apply star_trans with (pc + length code_b1 + (if eqb (beval st b1) false then ofs' else 0), stk, st).
  apply IHb1. eauto with codeseq.
  destruct cond.
  SCase true.
    destruct (beval st b1); simpl.
    SSCase true.
      normalize. rewrite plus_0_r. apply IHb2. eauto with codeseq. 
    SSCase  false.
      normalize. rewrite plus_0_r. apply star_refl.
  SCase false.
    destruct (beval st b1); simpl.
    SSCase  true.
      normalize. rewrite plus_0_r. apply IHb2. eauto with codeseq. 
    SSCase false.
      replace ofs' with (length code_b2 + ofs). normalize. apply star_refl.
      unfold ofs'; lia.
Qed.


(** ** Correctness of generated code for commands: terminating case. *)

Lemma compile_com_correct_terminating:
  forall C st c st',
  c / st ==> st' ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_com c), stk, st').

Proof.
  induction 1; intros stk pc AT.

 (* Case SKIP *)
  simpl in *. rewrite plus_0_r. apply star_refl.

(* Case ::= *)
  simpl in *. subst n.
  eapply star_trans. apply compile_aexp_correct. eauto with codeseq.
  apply star_one. normalize. apply trans_setvar. eauto with codeseq. 

(* Case sequence *)
  simpl in *.
  eapply star_trans. apply IHceval1. eauto with codeseq. 
  normalize. apply IHceval2. eauto with codeseq. 

(* Case if true *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  Close Scope string_scope.  (* trying to acote the scope of the string library*)
  set (codeb := compile_bexp b1 false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  eapply star_trans. 
  apply compile_bexp_correct with (b := b1) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq. 
  rewrite H. simpl. rewrite plus_0_r. fold codeb. normalize.
  eapply star_trans. apply IHceval. eauto with codeseq. 
  apply star_one. eapply trans_branch_forward. eauto with codeseq. lia.

(* Case if false *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b1 false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  eapply star_trans. 
  apply compile_bexp_correct with (b := b1) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq. 
  rewrite H. simpl. fold codeb. normalize.
  replace (pc + length codeb + length code1 + S(length code2))
     with (pc + length codeb + length code1 + 1 + length code2).
  apply IHceval. eauto with codeseq. lia. 

(* Case while false *)
  simpl in *. 
  eapply star_trans.
  apply compile_bexp_correct with (b := b1) (cond := false) (ofs := length (compile_com c1) + 1). 
  eauto with codeseq.
  rewrite H. simpl. normalize. apply star_refl.

(* Case while true *)
  apply star_trans with (pc, stk, st').
  simpl in *.
  eapply star_trans.
  apply compile_bexp_correct with (b := b1) (cond := false) (ofs := length (compile_com c1) + 1). 
  eauto with codeseq. 
  rewrite H; simpl. rewrite plus_0_r.
  eapply star_trans. apply IHceval1. eauto with codeseq. 
  apply star_one.
  eapply trans_branch_backward. eauto with codeseq. lia.
  apply IHceval2. auto.
Qed.

Theorem compile_program_correct_terminating:
  forall c st st',
  c / st ==> st' ->
  mach_terminates (compile_program c) st st'.
Proof.
  intros. unfold compile_program. red.
  exists (length (compile_com c)); split.
  apply code_at_app. auto.
  apply compile_com_correct_terminating with (pc := 0). auto. 
  apply codeseq_at_intro with (C1 := nil). auto.
Qed.


(** **** Exercise (2 stars) *)
(** The previous exercise in this chapter suggested to use
  [smart_Ibranch_forward] to avoid generating useless "branch forward"
  instructions when compiling [IFB ... THEN ... ELSE SKIP FI] commands.
  Once you have modified [compile_com] to use [smart_Ibranch_forward],
  adapt the proof of [compile_com_correct_terminating] accordingly.
  The following lemma will come handy: *)

Lemma trans_smart_branch_forward:
  forall C ofs pc stk st,
  codeseq_at C pc (smart_Ibranch_forward ofs) ->
  star (transition C) (pc, stk, st) (pc + length (smart_Ibranch_forward ofs) + ofs, stk, st).
Proof.
  unfold smart_Ibranch_forward; intros.
  (* FILL IN HERE *)
Admitted.

(** ** Correctness of generated code for commands: diverging case. *)

(** We consider the set of machine states that correspond to a diverging
  command: the PC points to [compile_com c] and c diverges in the current state,
  as captured by the coinductive big-step semantics. *)

Inductive diverging_state: code -> machine_state -> Prop :=
  | div_state_intro: forall c st C pc stk,
      c / st ==> ∞ -> 
      codeseq_at C pc (compile_com c) ->
      diverging_state C (pc, stk, st).

(** We then show that from any diverging state, the machine can always make
  one or several transitions and reach another diverging state. *)

Lemma diverging_state_productive:
  forall C S1,
  diverging_state C S1 ->
  exists S2, plus (transition C) S1 S2 /\ diverging_state C S2.
Proof.
  intros. inv H. revert c st pc H0 H1.
  induction c; intros st pc EXECINF AT; inv EXECINF.

(* Case seq left *)
  simpl in AT. apply IHc1. auto. eauto with codeseq.

(* Case seq right *)
  simpl in AT. 
  destruct (IHc2 st2 (pc + length (compile_com c1))) as [S [A B]]. auto. eauto with codeseq.
  exists S; split.
  eapply star_plus_trans. apply compile_com_correct_terminating. eauto. eauto with codeseq. apply A.
  apply B.

(* Case if true *)
  simpl in AT.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  destruct (IHc1 st (pc + length codeb)) as [S [A B]]. auto. eauto with codeseq. 
  exists S; split.
  eapply star_plus_trans. 
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq.
  rewrite H3; simpl. rewrite plus_0_r. apply A.
  apply B.

(* Case if false *)
  simpl in AT.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  destruct (IHc2 st (pc + length codeb + length code1 + 1)) as [S [A B]]. auto. eauto with codeseq. 
  exists S; split.
  eapply star_plus_trans. 
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq.
  rewrite H3; simpl. normalize. apply A.
  apply B.

(* Case while body *)
  simpl in AT.
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  destruct (IHc st (pc + length codeb)) as [S [A B]]. auto. eauto with codeseq.
  exists S; split.
  eapply star_plus_trans.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1).
  eauto with codeseq.
  rewrite H1; simpl. rewrite plus_0_r. apply A.
  apply B.

(* Case while loop *)
  exists (pc, stk, st'); split.
  simpl in AT.
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  eapply star_plus_trans.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1).
  eauto with codeseq.
  rewrite H1; simpl. rewrite plus_0_r.
  eapply star_plus_trans.
  apply compile_com_correct_terminating. eauto. eauto with codeseq.
  apply plus_one. 
  eapply trans_branch_backward. eauto with codeseq. fold codec; fold codeb. lia. 
  econstructor. eauto. auto.
Qed.

(** From the lemma above, we deduce that the machine makes infinitely many
  transitions if it is started in a diverging state.  The proof uses
  the alternate coinduction principle [infseq_coinduction_principle_2]
  defined and proved in file [Sequences]. *)

Lemma compile_com_correct_diverging:
  forall c st C pc stk,
  c / st ==> ∞ -> codeseq_at C pc (compile_com c) ->
  infseq (transition C) (pc, stk, st).
Proof.
  intros. 
  apply infseq_coinduction_principle_2 with (X := diverging_state C).
  apply diverging_state_productive. 
  econstructor; eauto.
Qed.

Theorem compile_program_correct_diverging:
  forall c st,
  c / st ==> ∞ ->
  mach_diverges (compile_program c) st.
Proof.
  intros. unfold compile_program. red.
  apply compile_com_correct_diverging with (c := c). auto.
  apply codeseq_at_intro with (C1 := nil); auto.
Qed.
