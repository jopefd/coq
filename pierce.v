(** Pierce original *)

Definition lem : Prop :=
forall (p : Prop), (p \/ ~p).

Theorem pierce_with_lem :
lem -> forall (p q : Prop), ((p -> q) -> p) -> p.
Proof.
  intro Hlem.
  intros p q.
  destruct (Hlem p) as [Hp | Hnp].
  - intro Hpimpqimpp. apply (Hpimpqimpp Hp).
Qed.

(** Pierce fraca *)

Theorem peirce_fraca :
forall (p q : Prop), ((p -> q) -> p) -> ~~p.
Proof.
  intros p q.
  intro Hpimpqimpp.
  unfold not.
  intro Hnp.
  apply Hnp.
  apply Hpimpqimpp.
  intro Hp.
  contradiction.
Qed.
