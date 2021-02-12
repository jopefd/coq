Theorem demorgan1 :
forall (p q : Prop), ~(p \/ q) -> (~p /\ ~q).
Proof.
  intros p q.
  unfold not.
  intro Hnporq.
  split.
  - intro Hp.
    assert (Hporq: p \/ q).
    + left.
      assumption.
    + apply Hnporq in Hporq.
      assumption.
  - intro Hq.
    assert (Hporq: p \/ q).
    + right.
      assumption.
    + apply Hnporq in Hporq.
      assumption.
Qed.
