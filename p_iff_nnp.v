Theorem p_implies_nnp : forall (p : Prop), p -> ~~p.
Proof.
intros p.
intros Hp.
unfold not.
intros Hnp.
apply (Hnp Hp).
Qed.

Definition lem :
forall (p : Prop), p \/ (~p).
Admitted.

Theorem nnp_implies_p_with_lem :
lem -> forall (p : Prop), ~~p -> p.

Proof.
  intro p.
  unfold not.
  intro Hnnp.
  destruct Hnnp.
  intro bla.
  simpl.
  reflexivity.
  apply (lem Hnnp).
