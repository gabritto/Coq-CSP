Require Import Coq.Init.Nat. 
Require Import Coq.Bool.Bool.

Fixpoint do_n_times {X:Type}
  (f:X->X) (v:X) (n:nat) : X :=
  match n with
  | O     => v
  | S n'  => f (do_n_times f v n')
  end.
  
Theorem even_SSn : forall (n : nat),
  even (S (S n)) = even n.
Proof.
  intro n. simpl. reflexivity.
Qed.
  
Theorem even_iff : forall (n : nat),
  even n = negb (even (S n)).
Proof.
  intro n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite even_SSn. rewrite IHn'.
    rewrite negb_involutive.
    reflexivity.
Qed.

Theorem even_Sn_true : forall (n : nat),
  (even (S n) = true -> even n = false).
Proof.
  intro n. destruct n as [| n'].
  - simpl. intro H. inversion H.
  - intro H. simpl in H.
    rewrite even_iff. simpl.
    rewrite H. simpl. reflexivity.
Qed. 

Theorem even_Sn_false : forall (n : nat),
  (even (S n) = false -> even n = true).
Proof.
  intro n. destruct n as [| n'].
  - simpl. intro H. reflexivity.
  - intro H. rewrite even_iff.
    rewrite H. simpl. reflexivity.
Qed.

Theorem do_n_times_even :
  forall (X : Type) (b : bool) (n : nat),
    (even n = true -> (do_n_times negb b n) = b) /\
    (even n = false -> (do_n_times negb b n) = negb b).
Proof.
  intros X b n. induction n as [| n' IHn'].
  - split.
    + simpl. reflexivity.
    + intro H. inversion H.
  - destruct IHn' as [IHn1' IHn2']. split. 
    + intro H. apply even_Sn_true in H.
      apply IHn2' in H. simpl.
      rewrite H. rewrite negb_involutive.
      reflexivity.
    + intro H. apply even_Sn_false in H.
      apply IHn1' in H. simpl.
      rewrite H. reflexivity.
Qed.