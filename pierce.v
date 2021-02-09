(** Pierce original *)

Definition lem : Prop :=
forall (p : Prop), (p \/ ~p).

Theorem pierce_with_lem :
lem -> forall (p q : Prop), ((p -> q) -> p) -> p.
Proof.
  intros Hlem p q Hpimpqimpp.
  apply (Hpimpqimpp (Hlem p q)).
Qed.

(** Pierce fraca *)

Theorem pierce_fraca :
forall (p q : Prop), ((p -> q) -> p) -> ~~p.
Proof.
  intros p q.
  intro Hpimpqimpp.
  unfold not.
  intro Hnp.
  apply (Hnp Hpimpqimpp).
Qed.
