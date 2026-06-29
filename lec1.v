Set Implicit Arguments.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Check S (S (S O)).

Fixpoint add (n m : nat) :=
  match m with
  | O => n
  | S m => S (add n m)
  end.

Compute add (S (S (S O))) (S (S O)).

Lemma add_O_rigth n :
  add n O = n.
Proof.
  cbn. reflexivity.
Qed.

Lemma add_O_left m :
  add O m = m.
Proof.
  induction m.
  - cbn. reflexivity.
  - cbn. rewrite IHm. reflexivity.
Qed.

Lemma add_S_left n m :
  add (S n) m = S (add n m).
Proof.
  induction m; cbn.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

Lemma add_comm n m :
  add n m = add m n.
Proof.
  induction n; cbn.
  - apply add_O_left.
  - rewrite add_S_left. rewrite IHn. reflexivity.
Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Check false.

Definition neg (b : bool) :=
  match b with true => false | false => true end.

Compute neg true.

Lemma neg_inv b :
  neg (neg b) = b.
Proof.
  destruct b.
  - cbn. reflexivity.
  - reflexivity.
Qed.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Check cons O (nil nat).

Arguments nil {_}.

Check cons O nil.
