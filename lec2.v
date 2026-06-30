Set Implicit Arguments.

(* Reasoning with functions *)

Theorem Lawvere X Y (f : X -> X -> Y) :
  (forall g : X -> Y, exists x, f x = g)
    -> forall h : Y -> Y, exists y, h y = y.
Proof.
  intros Hg h.
  pose (g x := h (f x x)).
  destruct (Hg g) as [x Hx].
  exists (f x x).
  change (g x = f x x).
  rewrite <- Hx. reflexivity.
Qed.

Theorem Cantor (f : nat -> nat -> bool) :
  ~ forall g, exists n, f n = g.
Proof.
  intros Hg. enough (H : true = false).
  - change (if true then False else True).
    rewrite H. apply I.
  - assert (H : exists b, negb b = b) by apply (Lawvere f Hg).
    destruct H as [b Hb]. destruct b.
    + cbn in Hb. now rewrite Hb.
    + cbn in Hb. now rewrite Hb.
Qed.

(* Logical connectives and proof terms *)

Goal (forall P Q : Prop, (P -> Q) -> P -> Q).
Proof.
  intros P Q H HP. apply H. apply HP.
  Show Proof.
  Restart.
  exact (fun P Q H HP => H HP).
Qed.

Goal (forall P : Prop, P -> P).
Proof.
  intros P. intros H. exact H.
  Show Proof.
  Restart.
  exact (fun P H => H).
Qed.

Print False.

Goal (forall P : Prop, ~ ~ ~ P -> ~ P).
Proof.
  intros P H HP.
  apply H. intros H'. apply H', HP.
  Restart.
  exact (fun P H HP => H (fun H' => H' HP)).
Qed.

Print or.

Goal (forall P : Prop, ~ ~ (P \/ ~ P)).
Proof.
  intros P H. apply H. right. intros HP. apply H. left. apply HP.
  Restart.
  exact (fun P H => H (or_intror (fun HP => H (or_introl HP)))).
Qed.

Print and.

Goal (forall P Q : Prop, P \/ Q -> ~ (~ P /\ ~ Q)).
Proof.
  intros P Q [H|H] [H1 H2].
  - apply H1, H.
  - apply H2, H.
  Restart.
  tauto.
  Restart.
  exact (fun P Q H H' => let (H1, H2) := H' in match H with
    | or_introl H => H1 H
    | or_intror H => H2 H
    end).
Qed.

Print ex.

Goal (forall X (P : X -> Prop), (exists x, P x) -> ~ forall x, ~ P x).
Proof.
  intros X P [x Hx] H. apply (H x). apply Hx.
  Restart.
  exact (fun X P H' H => let (x, Hx) := H' in H x Hx).
Qed.

(* Excluded middle and related aioms *)

Definition LEM := forall P : Prop, P \/ ~ P.
Definition DNE := forall P : Prop, ~ ~ P -> P.
Definition DMP := forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q.
Definition DMQ := forall X (P : X -> Prop), ~ (forall x, ~ P x)
  -> exists x, P x.

Lemma LEM_DNE :
  LEM -> DNE.
Proof.
  intros lem P HP.
  destruct (lem P) as [H|H].
  - apply H.
  - exfalso. apply HP, H.
Qed.

Lemma DNE_DMP :
  DNE -> DMP.
Proof.
  intros dne P Q H. apply dne. intros H'.
  apply H. split.
  - intros HP. apply H'. left. apply HP.
  - intros HQ. apply H'. right. apply HQ.
Qed.

Lemma DMP_LEM :
  DMP -> LEM.
Proof.
  intros dmp P. apply dmp. intros [H1 H2]. apply H2, H1.
Qed.

Definition MP := forall f : nat -> bool, ~ ~ (exists n, f n = true)
  -> exists n, f n = true.

Lemma LEM_MP :
  LEM -> MP.
Proof.
  intros lem f. apply LEM_DNE. apply lem.
Qed.


