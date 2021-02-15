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

Fixpoint Multiplicacao (n m : Nat) :=
  match m with
  | O => O
  | S m => (Multiplicacao n m) + n
  end.

Notation "x * y" := (Multiplicacao x y).

Fixpoint Exponenciacao (n m : Nat) :=
  match m with
  | O => S O
  | S m => (Exponenciacao n m) * n
  end.

Notation "x ^ y" := (Exponenciacao x y).

End fmcthanos.
