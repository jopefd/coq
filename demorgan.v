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

Definition lem : Prop :=
forall (p : Prop), (p \/ ~p).

Theorem demorgan3 :
lem -> forall (p q : Prop), ~(p /\ q) -> (~q \/ ~p).
Proof.
  intros Hlem p q.
  unfold not.
  intro Hnnpandq.
  destruct (Hlem p) as [Hp | Hnp].
  - destruct (Hlem q) as [Hq | Hnq].
    + assert (Hpandq: p /\ q).
      * split.
        -- assumption.
        -- assumption.
      * left.
        intro Hq'.
        apply Hnnpandq in Hpandq.
        assumption.
    + left.
      intro Hq.
      unfold not in Hnq.
      apply Hnq in Hq.
      assumption.
  - right.
    intro Hp.
    apply Hnp in Hp.
    assumption.
Qed.
