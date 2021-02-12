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

Theorem distr2_or_and :
forall (p q r: Prop), (p /\ q) \/ (p /\ r) -> p /\ (q \/ r).
Proof.
  intros p q r.
  intro Hpandqorpandr.
  destruct Hpandqorpandr as [Hpandq | Hpandr].
  - destruct Hpandq as [Hp Hq].
    split.
    + assumption.
    + left.
      assumption.
  - destruct Hpandr as [Hp Hr].
    split.
    + assumption.
    + right.
      assumption.
Qed.
