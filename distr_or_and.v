Theorem distr1_or_and :
forall (p q r: Prop), p /\ (q \/ r) -> (p /\ q) \/ (p /\ r).
Proof.
  intros p q r.
  intro Hpandqorr.
  destruct Hpandqorr as [Hp Hqorr].
  destruct Hqorr as [Hq | Hr].
  - left.
    split.
    + assumption.
    + assumption.
  - right.
    split.
    + assumption.
    + assumption.
Qed.
