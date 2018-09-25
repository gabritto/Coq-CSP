Require Import Coq.Init.Nat. 
Require Import Coq.Bool.Bool.

(** Defina a função paramétrica do_n_times
    que aplica [f] a [v], [n] vezes. *)
Fixpoint do_n_times {X:Type}
  (f:X->X) (v:X) (n:nat) : X :=
  match n with
  | 0 => v
  | S n' => f (do_n_times f v n')
  end.
  
(** Prove os seguintes teoremas auxiliares. *)
Theorem even_SSn : forall (n : nat),
  even (S (S n)) = even n.
Proof.
  intros n. simpl. reflexivity.
Qed.
  
Theorem even_iff : forall (n : nat),
  even n = negb (even (S n)).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - rewrite even_SSn. rewrite IHn'. destruct (even (S n')). auto. auto.
Qed.

Theorem even_Sn_true : forall (n : nat),
  (even (S n) = true -> even n = false).
Proof.
  destruct n as [| n'].
  - simpl. intros H. symmetry. apply H.
  - rewrite even_SSn. intros H. rewrite even_iff.
    rewrite even_SSn. rewrite H. reflexivity.
Qed.

Theorem even_Sn_false : forall (n : nat),
  (even (S n) = false -> even n = true).
Proof.
  destruct n as [| n'].
  - intros H. simpl. reflexivity.
  - rewrite even_SSn. intros H.
    rewrite even_iff in H. Print negb. unfold negb in H. destruct (even (S n')).
    + reflexivity.
    + symmetry. apply H.
Qed.

Lemma negb_negb: forall (b: bool),
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(** Agora, prove o seguinte teorema. *)

Theorem do_n_times_negb :
  forall (b : bool) (n : nat),
    (even n = true -> (do_n_times negb b n) = b) /\
    (even n = false -> (do_n_times negb b n) = negb b).
Proof.
  intros b n. induction n as [| n'].
  - split.
    + simpl. intros _. reflexivity.
    + simpl. destruct b. auto. auto.
  - split.
    + intros H. apply even_Sn_true in H. apply proj2 in IHn'. apply IHn' in H.
      simpl. rewrite H. apply negb_negb.
    + intros H. apply even_Sn_false in H. apply proj1 in IHn'. apply IHn' in H.
      simpl. rewrite H. reflexivity.
Qed.



