(** * Indução em Coq *)

Require Export aula03_provas.

(* ############################################### *)
(** * Prova por indução *)

(** Nem sempre é possível provar somente por:
    - simplificação
    - reescrita
    - análise de casos *)

(** Na aula passada, vimos o seguinte teorema *)

Print plus_O_n.

(** E se quisermos provar n + 0 = n? *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  simpl. (* não simplifica nada *)
  try reflexivity.
(** [reflexivity] não funciona, pois [n]
    em [n + 0] é um número arbitrário e
    não caso padrão com o [+] *)
  Print NatPlayground2.plus.
Abort.

(** Análise de casos também não ajuda. *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* quando [n] é 0, funciona *)
  - (* n = S n' *)
    simpl.       (* aqui [n] é [S n'],
                  outro número arbitrário *)
Abort.

(** Chamadas sucessivas a [destruct n']
    também não ajudaria. Precisamos de indução. *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'.
                   reflexivity.
Qed.

(** Outro exemplo. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(** Nota: [induction] move automaticamente
    variáveis quantificadas para o contexto. *)

(** **** Exercise: (basic_induction)  *)
(** Prove os seguintes teoremas. Será necessário
    buscar por resultados previamente provados. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - Print Nat.mul. simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. reflexivity. 
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IH].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IH. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

(* ############################################### *)
(** * Provas aninhadas *)

(** É possivel/aconselhável quebrar provas maiores
    em subprovas. Isto pode ser feito a partir de
    [Lemma], como também a partir de "sub-teoremas". *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  {
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

(** Outro exemplo: veja que a tática [rewrite]
    não é muito "inteligente" sobre onde aplicar
    a reescrita no objetivo. *)

Theorem plus_rearrange_firsttry :
  forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Só queremos trocar (n + m) por (m + n). *)
  rewrite -> plus_comm.
  (* Mas  reescrita não faz o que queremos. *)
Abort.

(** Veja a próxima prova. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

(* ############################################### *)
(** * Mais exercícios *)

(** **** Exercise: (mult_comm)  *)
(** Use [assert] para ajudar na prova. Não é
    necessário usar indução. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros. rewrite plus_assoc.
  assert (H: n + m = m + n).
  {
    rewrite plus_comm. reflexivity.
  }
  rewrite -> H. rewrite plus_assoc.
  reflexivity.
Qed.

(** Agora, prove comutatividade da multiplicação.
    Talvez seja necessário provar um teorema auxiliar.
    O teorema [plus_swap] será útil. *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros. induction m as [|m' IH].
  - simpl. Search (_ * 0). rewrite <- mult_n_O.
    reflexivity.
  - simpl. Print Nat.mul. Search (_ * _). rewrite <- mult_n_Sm.
    rewrite plus_comm. rewrite -> IH. reflexivity.
Qed.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Induction
  https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
*)
