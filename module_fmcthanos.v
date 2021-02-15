Module fmcthanos.

Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint Soma (n m : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (Soma n m)
  end.
Notation "x + y" := (Soma x y).

(** Exercício x4.3 *)
Compute O + S(S(S(S O))).

(** Exercício x4.4 *)
Compute S(S(S O)) + S(S O).
Compute (S(S(S O)) + S(S O)) + S O.

(** Exercício x4.5 *)
Fixpoint Dobro (n : Nat) : Nat :=
  n + n.

(** Exercício x4.6 *)
Fixpoint Multiplicacao (n m : Nat) :=
  match m with
  | O => O
  | S m => (Multiplicacao n m) + n
  end.
Notation "x * y" := (Multiplicacao x y).

(** Exercício x4.7 *)
Compute S(S O) * (O + S O).

(** Exercício x4.8 *)
Compute S(S O) * S(S(S O)).
Compute S(S(S O)) * S(S O).

(** Exercício x4.9 *)
Fixpoint Exponenciacao (n m : Nat) :=
  match m with
  | O => S O
  | S m => (Exponenciacao n m) * n
  end.
Notation "x ^ y" := (Exponenciacao x y).

(** Exercício x4.10 *)
Compute S(S O) ^ S(S(S O)).

(** Exercício x4.11 *)
Fixpoint Fib (n : Nat) : Nat :=
  match n with
  | O => O
  | S O => S O
  | S (S n) => Fib (S n) + Fib n
  end.

End fmcthanos.










