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

Theorem demorgan2 :
forall (p q : Prop), (~p /\ ~q) -> ~(p \/ q).
Proof.
  intros p q.
  unfold not.
  intro Hnpandnq.
  intro Hporq.
  destruct Hnpandnq as [Hnp Hnq].
  destruct Hporq as [Hp | Hq].
  - apply Hnp in Hp.
    assumption.
  - apply Hnq in Hq.
    assumption.
Qed.
