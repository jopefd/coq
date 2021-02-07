Definition lem : Prop :=
forall (p : Prop), p \/ (~p).

Theorem lem_irrefutavel :
lem -> forall (p : Prop), ~~(p \/ ~p).
Proof.
  intros Hlem p.
  unfold not.
  intro Hn_p_or_np.
