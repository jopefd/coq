Module fmcthanos.

Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint plus (n m : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (plus n m)
  end.
Notation "x + y" := (plus x y).

(** Exercício x4.3 *)
Compute O + S(S(S(S O))).

(** Exercício x4.4 *)
Compute S(S(S O)) + S(S O).
Compute (S(S(S O)) + S(S O)) + S O.

(** Exercício x4.5 *)
Fixpoint double (n : Nat) : Nat :=
  n + n.

(** Exercício x4.6 *)
Fixpoint mult (n m : Nat) :=
  match m with
  | O => O
  | S m => (mult n m) + n
  end.
Notation "x * y" := (mult x y).

(** Exercício x4.7 *)
Compute S(S O) * (O + S O).

(** Exercício x4.8 *)
Compute S(S O) * S(S(S O)).
Compute S(S(S O)) * S(S O).

(** Exercício x4.9 *)
Fixpoint power (n m : Nat) : Nat :=
  match m with
  | O => S O
  | S m => (power n m) * n
  end.
Notation "x ^ y" := (power x y).

(** Exercício x4.10 *)
Compute S(S O) ^ S(S(S O)).

(** Exercício x4.11 *)
Fixpoint fib (n : Nat) : Nat :=
  match n with
  | O => O
  | S O => S O
  | S(S n as n') => fib (n') + fib (n)
  end.

Compute fib (S O).
Compute fib (S(S O)).
Compute fib (S(S(S O))).
Compute fib (S(S(S(S O)))).

Theorem plus_assoc :
forall (a m y : Nat), (a + m) + y = a + (m + y).
Proof.
  intros a m y.
  induction y as [ | z].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHz.
    reflexivity.
Qed.

Lemma plus_Sa_b :
forall (a b : Nat), S a + b = a + S b.
Proof.
  intros a b.
  induction b as [ | c].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHc.
    simpl.
    reflexivity.
Qed.

Theorem plus_comm :
forall (n m : Nat), n + m = m + n.
Proof.
  intros n m.
  induction n as [ | t].
  - induction m as [ | u].
    + reflexivity.
    + simpl.
      rewrite -> IHu.
      simpl.
      reflexivity.
  - rewrite -> plus_Sa_b.
    simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

(** Exercício x4.16 *)
Theorem mult_distr :
forall (x y z : Nat), x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  induction z as [ | z'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHz'.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

(** Exercício x4.14 *)
Theorem mult_assoc :
forall (n m k : Nat), (n * m) * k = n * (m * k).
Proof.
  intros n m k.
  induction k as [ | k'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHk'.
    rewrite <- mult_distr.
    reflexivity.
Qed.

(** Extra *)
Lemma mult_SO_a :
forall (a : Nat), S O * a = a.
Proof.
  intro a.
  induction a as [ | x].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(** Exercício x4.15 *)
Lemma Sn_m :
forall (n t : Nat), S t * n = (t * n) + n.
Proof.
  intros n m.
  induction n as [ | x].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHx.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    rewrite <- (plus_comm m x).
    reflexivity.
Qed.

Theorem mult_comm :
forall (n m : Nat), n * m = m * n.
Proof.
  intros n m.
  induction m as [ | t].
  - induction n as [ | u].
    + reflexivity.
    + simpl.
      rewrite <- IHu.
      simpl.
      reflexivity.
  - simpl.
    rewrite -> Sn_m.
    rewrite -> IHt.
    reflexivity.
Qed.

Definition leq (n m : Nat) : Prop :=
exists (k : Nat), n + k = m.
Notation "x <= y" := (leq x y).

(** Exercício x4.20 *)
Example leq_or_equal_1 :
forall (n m : Nat), (n <= S m) -> (n <= m \/ n = S m).
Proof.
  intros n m.
  intro Hnlsm.
  destruct Hnlsm as [k Hk].
  destruct k as [ | k'].
  - right.
    assumption.
  - left.
    simpl in Hk.
    exists k'.
    inversion Hk.
    reflexivity.
Qed.

Example leq_or_equal_2 :
forall (n m : Nat), (n <= m \/ n = S m) -> (n <= S m).
Proof.
  intros n m.
  intro Hnmnsm.
  destruct Hnmnsm as [Hnm | Hnsm].
  - destruct Hnm as [k Hk].
    exists (S k).
    simpl.
    inversion Hk.
    reflexivity.
  - exists O.
    simpl.
    assumption.
Qed.

(** Exercício x4.21 *)
Theorem leq_refl :
forall (x : Nat), x <= x.
Proof.
  intro x.
  exists O.
  simpl.
  reflexivity.
Qed.

(** Exercício x4.22 *)
Theorem leq_trans :
forall (x y z: Nat), (x <= y) /\ (y <= z) -> x <= z.
Proof.
  intros x y z.
  unfold leq.
  intro Hxyyz.
  destruct Hxyyz as [Hxy Hyz].
  destruct Hxy as [k Hk].
  destruct Hyz as [k' Hk'].
  rewrite <- Hk in Hk'.
  exists (k + k').
  rewrite <- Hk'.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

(** Exercício x4.23 *)
Lemma x_diff :
forall (x y : Nat), x <> x + S y.
Proof.
  intros x y.
  unfold not.
  induction x as [ | w].
  - intro Hxxsy.
    rewrite -> plus_comm in Hxxsy.
    simpl in Hxxsy.
    inversion Hxxsy.
  - intro Hswswsy.
    rewrite -> plus_comm in Hswswsy.
    simpl in Hswswsy.
    inversion Hswswsy as [Hwsyw].
    rewrite -> plus_comm in Hwsyw.
    apply (IHw Hwsyw).
Qed.

Lemma y_equality :
forall (x y : Nat), x + y = x -> y = O.
Proof.
  intros x y.
  intro Hxyx.
  induction y as [ | y'].
  - reflexivity.
  - induction x as [ | x'].
    + simpl in Hxyx.
      discriminate.
    + rewrite -> IHy' in IHx'.
(*       * discriminate. *)
Abort.

Lemma xaxbab :
forall (x a b : Nat), a + x = b + x -> a = b.
Proof.
  intros x a b.
  intro Hxaxb.
  induction x as [ | x'].
  - assumption.
  - rewrite <- IHx' in Hxaxb.
    simpl in Hxaxb.
Abort.

Lemma abo :
forall (a b : Nat), a + b = O -> a = O /\ b = O.
Proof.
  intros a b Habo.
  destruct b as [ | b'].
  - split.
    + simpl in Habo.
      assumption.
    + reflexivity.
  - simpl in Habo.
    discriminate.
Qed.

Theorem leq_antisym :
forall (x y: Nat), (x <= y) /\ (y <= x) -> x = y.
Proof.
  intros x y.
  intro Hxyyx.
  destruct Hxyyx as [Hxy Hyx].
  destruct Hxy as [w Hw].
  destruct Hyx as [v Hv].
  rewrite <- Hw in Hv.
  induction y as [ | y'].
  - induction x as [ | x'].
    + induction w as [ | w'].
      * reflexivity.
      * reflexivity.
    + rewrite -> plus_comm in Hw.
      simpl in Hw.
      discriminate.
  - induction x as [ | x''].
    + induction w as [ | w''].
      * simpl in Hw.
        discriminate.
      * rewrite -> plus_comm in Hv.
        simpl in Hv.
        discriminate.
    + induction w as [ | w'''].
      * rewrite -> plus_comm in Hw.
        simpl in Hw.
        rewrite -> plus_comm in Hw.
        simpl in Hw.
        assumption.
      * induction v as [ | v'].
        simpl in Hv.
        -- rewrite Hv.
           reflexivity.
        --
        rewrite -> plus_comm in H.
  
  
  
  
  induction w as [ | u].
  - reflexivity.
  - pattern x at 1. rewrite <- Hv.
    induction v as [ | t].
    + rewrite -> Hw.
      reflexivity.
    + rewrite <- Hw in Hv.
      rewrite -> plus_assoc in Hv.
      simpl (S u + S t) in Hv.
      induction x as [ | s].
      * simpl in Hv.
        discriminate.
      * 
      
    destruct x as [ | Su].
    + rewrite -> plus_comm.
      simpl.
      discriminate.
    
    rewrite -> plus_assoc.
    reflexivity.
  - destruct Hxyyz as [Hxy Hyz].  
    destruct Hxy as [k Ek].
    destruct Hyz as [k' Ek'].
    destruct Hxz as [k'' Ek''].
    rewrite <- Ek'.
    rewrite <- Ek.
(*     rewrite <- Ek. *)
Abort.

(** Exercício x4.24 *)
Theorem leq_total :
forall (x y: Nat), (x <= y) \/ (y <= x).
Proof.
  intros x y.
  destruct y as [ | y'].
  - destruct x as [ | x'].
    + left.
      exists O.
      reflexivity.
    + right.
      exists (S x').
      rewrite -> plus_comm.
      simpl.
      reflexivity.
  - induction x as [ | x'].
    + left.
      exists (S y').
      rewrite -> plus_comm.
      simpl.
      reflexivity.
    + destruct IHx' as [Hx'sy' | Hsy'x'].
      destruct Hx'sy' as [w Hw].
      destruct w as [ | w'].
      * rewrite <- Hw.
        right.
        exists (S O).
        simpl.
        reflexivity.
      * rewrite <- Hw.
        left.
        exists w'.
        rewrite -> plus_comm.
        simpl.
        rewrite -> plus_comm.
        reflexivity.
      * destruct Hsy'x' as [v Hv].
        right.
        exists (S v).
        simpl.
        rewrite -> Hv.
        reflexivity.
Qed.

(** Exercício x4.25 *)
(* Example n2_leq_2n :
forall (n : Nat), S(S(S(S(S O)))) <= n -> n ^ (S(S O)) < S(S O) ^ n.
Admitted. *)

(** Homework: 20/02/2021, 1 *)
Fixpoint sum (i n x : Nat) : Nat :=
  match n with
  | O => O
  | S n' => x + (sum i n' x)
  end.

Compute (sum (S O) (S(S(S O))) (S O)).
Compute (sum (S O) (S(S(S(S(S(S O)))))) (S O)).

Theorem n_equals_sum_3_5 :
forall (n : Nat), exists (t u : Nat), n = S(S(S O)) * t + S(S(S(S(S O)))) * u.
Proof.
  intro n.
  induction n as [ | m].
  - exists O.
    exists O.
    simpl.
    reflexivity.
  - destruct IHm as [v Hv].
    destruct Hv as [w Hw].
    rewrite -> Hw.
    simpl.
    exists (S(S O)).
    exists (S O).


Fixpoint sum1 (n : Nat) (s : Nat -> Nat) : Nat :=
  match n with
  | O => O
  | S n' => (s n) + (sum1 n' s)
  end.

Compute (sum1 (S(S(S O))) (fun i => (S O))).
Compute (sum1 (S O) (S(S(S(S(S(S O)))))) (S O)).

Fixpoint sum_alt (i n x : Nat) : Nat :=
  match i with
  | S n => O
  | (S i' as j) => x + (sum_alt j n x) 
  | _ => O
  end.




End fmcthanos.
