Set Implicit Arguments.

(* Booleans and negation *)

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

(* Natural numbers and addition *)

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

Lemma add_O_right n :
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

(* Lists, concatenation and length *)

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Check cons O (nil nat).

Arguments nil {_}.

Check cons O nil.

Fixpoint app A (L L' : list A) : list A :=
  match L with 
  | nil => L'
  | cons x L => cons x (app L L')
  end.

Compute app (cons true nil) (cons false nil).

Lemma app_nil_right A (L : list A) :
  app L nil = L.
Proof.
  induction L; cbn.
  - reflexivity.
  - rewrite IHL. reflexivity.
Qed.

Fixpoint length A (L : list A) : nat :=
  match L with
  | nil => O
  | cons x L => S (length L)
  end.

Compute length (cons true (cons false nil)).

Lemma length_add A (L L' : list A) :
  length (app L L') = add (length L) (length L').
Proof.
  induction L; cbn.
  - now rewrite add_O_left.
  - now rewrite IHL, add_S_left.
Qed.