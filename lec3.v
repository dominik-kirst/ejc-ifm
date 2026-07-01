Set Implicit Arguments.
Require Import Setoid Bool.
Require Import Coq.Logic.ConstructiveEpsilon.

(* Basic synthetic computability notions *)

Definition dec X (P : X -> Prop) :=
  exists d : X -> bool, forall x, P x <-> d x = true.

Definition sdec X (P : X -> Prop) :=
  exists s : X -> nat -> bool, forall x, P x <-> exists n, s x n = true.

Lemma dec_sdec X (P : X -> Prop) :
  dec P -> sdec P.
Proof.
  intros [d Hd]. exists (fun x _ => d x). intros x; split; intros H.
  - exists 42. apply Hd, H.
  - destruct H as [_ H]. apply Hd, H.
Qed.

Notation compl P :=
  (fun x => ~ P x).

Lemma dec_sdec_compl X (P : X -> Prop) :
  dec P -> sdec (compl P).
Proof.
  intros [d Hd]. exists (fun x _ => negb (d x)). intros x; split; intros H.
  - exists 42. rewrite Hd in H. destruct (d x); trivial. now contradict H.
  - destruct H as [_ H]. intros Hx % Hd. destruct (d x); cbn in H; congruence.
Qed.

Definition red X Y (P : X -> Prop) (Q : Y -> Prop) :=
  exists r : X -> Y, forall x, P x <-> Q (r x).

Lemma red_dec X Y (P : X -> Prop) (Q : Y -> Prop) :
  red P Q -> dec Q -> dec P.
Proof.
  intros [r Hr] [d Hd]. exists (fun x => d (r x)).
  intros x. rewrite Hr, Hd. reflexivity.
Qed.

(* Post's theorem *)

Axiom MP :
  forall f : nat -> bool, ~ ~ (exists n, f n = true) -> exists n, f n = true.

Theorem Post X (P : X -> Prop) :
  sdec P -> sdec (compl P) -> dec P.
Proof.
  intros [f Hf] [g Hg].
  enough (H : forall x, { n | orb (f x n) (g x n) = true }).
  - exists (fun x => f x (proj1_sig (H x))). intros x. split; intros Hx.
    + destruct (H x) as [n Hn]; cbn. apply orb_true_iff in Hn as [Hn|Hn].
      * apply Hn.
      * exfalso. apply (Hg x); trivial. now exists n.
    + apply Hf. eauto.
  - intros x. apply constructive_indefinite_ground_description_nat.
    + intros n. destruct (f x n || g x n); eauto.
    + apply MP. intros H. assert (Hx : ~ ~ (P x \/ ~ P x)) by tauto.
      apply Hx. intros [HP|HN]; apply H.
      * apply Hf in HP as [n Hn]. exists n. apply orb_true_iff. now left.
      * apply Hg in HN as [n Hn]. exists n. apply orb_true_iff. now right.
Qed.

(* Formal systems *)

Section Sys.

  Variable sent : Type.
  Variable neg : sent -> sent.
  Variable prv : sent -> Prop.

  Hypothesis neg_cons : forall A, prv A -> prv (neg A) -> False.
  Hypothesis prv_sdec : sdec prv.

  Definition complete :=
    forall A, prv A \/ prv (neg A).

  Lemma complete_dec :
    complete -> dec prv.
  Proof.
    intros HC. apply Post.
    - apply prv_sdec.
    - destruct prv_sdec as [s Hs].
      exists (fun A n => s (neg A) n).
      intros A. split; intros HA.
      + destruct (HC A) as [HP|HR].
        * contradiction.
        * apply Hs. apply HR.
      + apply Hs in HA. intros H. now apply (neg_cons H).
  Qed.

  Variable K : nat -> Prop.
  Hypothesis K_undec : ~ dec K.

  Definition expressive :=
    red K prv.

  Theorem Godel :
    expressive -> ~ complete.
  Proof.
    intros H H'. apply K_undec. apply (red_dec H). now apply complete_dec.
  Qed.

End Sys.






