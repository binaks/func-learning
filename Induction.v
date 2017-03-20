Require Export Basics.

Theorem plus_n_0 : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_0. reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'.
    rewrite -> negb_involutive.
    simpl. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. destruct n.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm.
    assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> plus_assoc'. rewrite -> H.
    rewrite -> plus_assoc'. reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n * m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    rewrite -> plus_n_Sm.
    rewrite <- plus_assoc'.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction n as [|n' IHn'].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - destruct m.
    + simpl. rewrite -> mult_0_r. reflexivity.
    + simpl. rewrite <- IHn'. simpl.
      rewrite -> plus_swap.
      rewrite -> mult_n_Sm.
      assert (H: m * n' + m = m + m * n').
      { rewrite -> plus_comm. reflexivity. }
      rewrite -> H. reflexivity.
Qed.

Theorem leb_refl : forall n : nat,
  true = leb n n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p as [|p' IHn'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite <- plus_n_0.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
      (orb (negb b)
        (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - simpl. destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> plus_assoc'.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. destruct n.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm.
    rewrite -> plus_assoc'.
    rewrite -> plus_assoc'.
    replace (n + m) with (m + n).
    + reflexivity.
    + rewrite -> plus_comm. reflexivity.
Qed.