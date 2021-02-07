Theorem p_implies_nnp : forall (p : Prop), p -> ~~p.
Proof.
  intros p.
  intros Hp.
  unfold not.
  intros Hnp.
  apply (Hnp Hp).
Qed.

Definition lem : Prop :=
forall (p : Prop), p \/ (~p).

Theorem doubleneg_elim :
lem -> forall (p : Prop), ~~ p -> p.
Proof.
  intros Hlem p Hnnp.
  unfold not in Hnnp.
  destruct (Hlem p) as [Hp | Hnp].
  - assumption.
  - unfold not in Hnp. apply Hnnp in Hnp. contradiction.
Qed.
