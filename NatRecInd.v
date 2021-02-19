Module fmcthanos.

Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint plus (n m : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (plus n m)
  end.
Notation "x + y" := (plus x y).

(** Exercício x4.3 *)
Compute O + S(S(S(S O))).

(** Exercício x4.4 *)
Compute S(S(S O)) + S(S O).
Compute (S(S(S O)) + S(S O)) + S O.

(** Exercício x4.5 *)
Fixpoint double (n : Nat) : Nat :=
  n + n.

(** Exercício x4.6 *)
Fixpoint mult (n m : Nat) :=
  match m with
  | O => O
  | S m => (mult n m) + n
  end.
Notation "x * y" := (mult x y).

(** Exercício x4.7 *)
Compute S(S O) * (O + S O).

(** Exercício x4.8 *)
Compute S(S O) * S(S(S O)).
Compute S(S(S O)) * S(S O).

(** Exercício x4.9 *)
Fixpoint power (n m : Nat) :=
  match m with
  | O => S O
  | S m => (power n m) * n
  end.
Notation "x ^ y" := (power x y).

(** Exercício x4.10 *)
Compute S(S O) ^ S(S(S O)).

(** Exercício x4.11
Fixpoint minus (n m : Nat) : Nat =
  match m with
  | O => O
  | S m => 

Fixpoint fib (n : Nat) : Nat :=
  match n with
  | O => O
  | S O => S O
  | S(S n) => fib (S n) + fib (n)
  end.

Compute fib (S(S(S(S O)))). *)

Theorem plus_assoc :
forall (a m y : Nat), (a + m) + y = a + (m + y).
Proof.
  intros a m y.
  induction y as [ | z].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHz.
    reflexivity.
Qed.

Lemma plus_Sa_b :
forall (a b : Nat), S a + b = a + S b.
Proof.
  intros a b.
  induction b as [ | c].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHc.
    simpl.
    reflexivity.
Qed.
Theorem plus_comm :
forall (n m : Nat), n + m = m + n.
Proof.
  intros n m.
  induction n as [ | t].
  - induction m as [ | u].
    + reflexivity.
    + simpl.
      rewrite -> IHu.
      simpl.
      reflexivity.
  - rewrite -> plus_Sa_b.
    simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

(** Exercício x4.16 *)
Theorem mult_distr :
forall (x y z : Nat), x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  induction z as [ | z'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHz'.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

(** Exercício x4.14 *)
Theorem mult_assoc :
forall (n m k : Nat), (n * m) * k = n * (m * k).
Proof.
  intros n m k.
  induction k as [ | k'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHk'.
    rewrite <- mult_distr.
    reflexivity.
Qed.

(** Exercício x4.15 *)
Lemma mult_SO_a :
forall (a : Nat), S O * a = a.
Proof.
  intro a.
  induction a as [ | x].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHx.
    reflexivity.
Qed.
(** Lemma Sn_m :
forall (n t : Nat), S t * n = (t * n) + n.
Proof.
  intros n m.
  induction n as [ | x].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> plus_assoc.
    rewrite <- plus_comm.
    rewrite -> IHx. 
    rewrite -> plus_assoc.
    rewrite <- plus_comm.
Abort. *)
Theorem mult_comm :
forall (n m : Nat), n * m = m * n.
Proof.
  intros n m.
  induction m as [ | t].
  - induction n as [ | u].
    + reflexivity.
    + simpl.
      rewrite <- IHu.
      simpl.
      reflexivity.
  -  simpl.
    induction n as [ | v]. 
    + simpl. (*
      rewrite <- IHt.
      reflexivity.
    + simpl.
      rewrite -> IHv.
      * simpl. 
      induction n as [ | w].
      * simpl.
        rewrite -> IHt.
      simpl. *)
Abort.

Definition leq (n m : Nat) : Prop :=
exists (k : Nat), n + k = m.
Notation "x <= y" := (leq x y).

(** Exercício x4.20 *)
Example leq_or_equal_1 :
forall (n m : Nat), (n <= S m) -> (n <= m \/ n = S m).
Proof.
  intros n m.
  intro Hnleqsm.
  destruct n as [ | k].
  - left.
    exists m.
    rewrite -> plus_comm.
    simpl.
    reflexivity.
  - destruct Hnleqsm.
    left.
Abort.

(** Exercício x4.21 *)
Example leq_refl :
forall (x : Nat), x <= x.
Proof.
  intro x.
  exists O.
  simpl.
  reflexivity.
Qed.

End fmcthanos.
