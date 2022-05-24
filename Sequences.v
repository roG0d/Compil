(** A library of relation operators defining sequences of transitions
  and useful properties about them. *)

Require Import Classical.

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.
Variable R: A -> A -> Prop.

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  intros. econstructor; eauto. constructor.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b, R a b -> plus a b.
Proof.
  intros. apply plus_left with b. auto. apply star_refl.
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
  intros. inversion H. eapply star_step; eauto. 
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
  intros. inversion H. eapply plus_left; eauto. eapply star_trans; eauto.
Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H0. inversion H. econstructor; eauto.
  econstructor; eauto. eapply star_trans; eauto. econstructor; eauto. 
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
  intros. eapply star_plus_trans; eauto. apply plus_one; auto.
Qed.

(** Infinitely many transitions. *)

CoInductive infseq: A -> Prop :=
  | infseq_step: forall a b,
      R a b -> infseq b -> infseq a.

(** Coinduction principles to show the existence of infinite sequences. *)

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, R a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros X P. cofix COINDHYP; intros.
  destruct (P a H) as [b [U V]]. apply infseq_step with b; auto. 
Qed.

Lemma infseq_coinduction_principle_2:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros.
  apply infseq_coinduction_principle with
    (X := fun a => exists b, star a b /\ X b).
  intros. 
  destruct H1 as [b [STAR Xb]]. inversion STAR; subst.
  destruct (H b Xb) as [c [PLUS Xc]]. inversion PLUS; subst.
  exists b0; split. auto. exists c; auto. 
  exists b0; split. auto. exists b; auto.

  exists a; split. apply star_refl. auto.
Qed.

(** An example of use of [infseq_coinduction_principle]. *)

Lemma infseq_alternate_characterization:
  forall a,
  (forall b, star a b -> exists c, R b c) ->
  infseq a.
Proof.
  apply infseq_coinduction_principle.
  intros. destruct (H a) as [b Rb]. constructor. 
  exists b; split; auto. 
  intros. apply H. econstructor; eauto.
Qed.

(** A sequence is either infinite or stops on an irreducible term. *)

Definition irred (a: A) : Prop := forall b, ~(R a b).

Lemma infseq_or_finseq:
  forall a, infseq a \/ exists b, star a b /\ irred b.
Proof.
  intros.
  destruct (classic (forall b, star a b -> exists c, R b c)).
  left. apply infseq_alternate_characterization; auto.
  right.
  generalize (not_all_ex_not _ _ H). intros [b P].
  generalize (imply_to_and _ _ P). intros [U V].
  exists b; split. auto.
  red; intros; red; intros. elim V. exists b0; auto.
Qed.

(** Additional properties for deterministic transition relations. *)

Hypothesis R_determ:
  forall a b c, R a b -> R a c -> b = c.

(** Uniqueness of transition sequences. *)

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
  induction 1; intros.
  auto.
  inversion H1; subst. right. eapply star_step; eauto. 
  assert (b = b0). eapply R_determ; eauto. subst b0. 
  apply IHstar; auto.
Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof.
  intros. destruct (star_star_inv H H1).
  inversion H3; subst. auto. elim (H0 _ H4).
  inversion H3; subst. auto. elim (H2 _ H4).
Qed.

Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof.
  induction 1; intros. auto. 
  inversion H1; subst. assert (b = b0). eapply R_determ; eauto. subst b0.
  apply IHstar. auto.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> infseq a -> False.
Proof.
  intros. 
  assert (infseq b). eapply infseq_star_inv; eauto. 
  inversion H2. elim (H0 b0); auto. 
Qed.

End SEQUENCES.


  


