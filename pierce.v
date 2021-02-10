(** Pierce original *)

Definition lem : Prop :=
forall (p : Prop), (p \/ ~p).

Theorem peirce_with_lem :
lem -> forall (p q : Prop), ((p -> q) -> p) -> p.
Proof.
  intro Hlem.
  intros p q.
  intro Hpimpqimpp.
  destruct (Hlem p) as [Hp | Hnp].
  { assumption. }
  { unfold not in Hnp.
    assert (Hpimpq: p -> q).
    { intro Hp.
      contradiction. }
    { apply (Hpimpqimpp Hpimpq). } }
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
