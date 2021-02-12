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

Theorem distr3_or_and :
forall (p q r: Prop), p \/ (q /\ r) -> (p \/ q) /\ (p \/ r).
Proof.
  intros p q r.
  intro Hpandqorr.
  destruct Hpandqorr as [Hp | Hqandr].
  - split.
    + left.
      assumption.
    + left.
      assumption.
  - split.
    + destruct Hqandr as [Hq Hr].
      right.
      assumption.
    + destruct Hqandr as [Hq Hr].
      right.
      assumption.
Qed.

Theorem distr4_or_and :
forall (p q r: Prop), (p \/ q) /\ (p \/ r) -> p \/ (q /\ r).
Proof.
  intros p q r.
  intro Hporqandporr.
  destruct Hporqandporr as [Hporq Hporr].
  destruct Hporq as [Hp | Hq].
  - destruct Hporr as [Hp' | Hr].
    + left.
      assumption.
    + left.
      assumption.
  - destruct Hporr as [Hp' | Hr].
    + left.
      assumption.
    + right.
      assert (Hqandr: q /\ r).
      * split.
        -- assumption.
        -- assumption.
      * split.
        -- assumption.
        -- assumption.
Qed.
