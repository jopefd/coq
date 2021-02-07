Theorem de_morgan_1 :
forall (P Q : Prop), P \/ Q -> ~(~P /\ ~Q).
Proof.
  intros P Q.
  intro P_or_Q.
  unfold not.
  intro nP_and_nQ. 
  apply P_or_Q.
  left.
  destruct P_or_Q as [P_holds | Q_holds].
  { unfold not. left.
  unfold not.
  intro nP_and_nQ. 
  destruct P_or_Q as [P_holds | Q_holds].
  { unfold not. split.
  intro Hp_or_q.
  unfold not.
  intro Hn_np_and_nq.
