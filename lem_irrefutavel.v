Definition lem : Prop :=
forall (p : Prop), p \/ (~p).

Theorem lem_irrefutavel :
lem -> forall (p : Prop), ~~(p \/ ~p).
Proof.
  intros Hlem p.
  intro Hn_p_or_np.
  unfold not in Hn_p_or_np.
  apply (Hn_p_or_np (Hlem p)).
Qed.
