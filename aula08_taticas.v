(** * Mais táticas básicas em Coq *)

(** Em particular, veremos:
    - provas "forward-style" e "backward-style"
    - como racicionar sobre construtores
      (funções injetoras e disjuntas)
    - como fortalecer uma hipótese de indução
    - mais detalhes sobre como raciocinar por casos. *)

Set Warnings "-notation-overridden,-parsing".
Require Export aula07_alta_ordem.

(* ############################################### *)
(** * A tática [apply] *)

(** Quando o objetivo de prova é _exatamente_ o
    mesmo de alguma hipótese do contexto
    ou algum lemma previamente provado. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(** Podemos terminar a prova escrevendo
    "[rewrite -> eq2. reflexivity.]". A tática
    [apply] gera o mesmo efeito. *)

  apply eq2.
Qed.

(** A tática [apply] também funciona com hipóteses
    condicionais. Se a afirmação sendo aplicada for
    uma implicação, as premissas da implicação
    serão adicionadas aos subobjetivos de prova
    a serem provados. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

(** Mais um exemplo a seguir. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

(** A conclusão da afirmação aplicada precisa
    casar exatamente com o objetivo de prova.
    Não funciona se o LHS e o RHS estiverem
    invertidos. Contudo, podemos usar outra
    tática: [symmetry]. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  try apply H. (* Não faz nada. *)
  symmetry.
  simpl. (* Opcional, pois [apply]
         faz [simpl] se necessário. *)
  apply H.  Qed.

(** **** Exercise: (apply_exercise1)  *)
(** Antes, prove os seguintes resultados auxiliares. *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [|x l1' IH].
  - simpl. Search ( _ ++ nil). symmetry. apply app_nil_r.
  - simpl. rewrite IH. Search (_ ++ _). symmetry. apply app_assoc.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X. intros l. induction l as [| x l' IH].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite IH. reflexivity. 
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' -> l' = rev l.
Proof.
  intros l l'. intros eq1. rewrite eq1. symmetry. apply rev_involutive.
Qed.

(* ############################################### *)
(** * A tática [apply ... with ...] *)

(** O seguinte exemplo usa [rewrite] duas vezes para
    obter [[e,f]] a partir de [[a,b]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(** De uma forma geral, podemos provar que a
    igualdade é transitiva. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

(** Para usar trans_eq no seguinte exemplo,
    preciamos de uma variação da tática [apply]. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  
(** Ao aplicar [apply trans_eq], Coq não consegue
    identificar como instanciar [m]. Precisamos informar
    usando [with (m := [c,d])]. *)
  
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

(** **** Exercise: (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros. apply trans_eq with (m:=m).
  apply H0. apply H.
Qed.

(* ############################################### *)
(** * A tática [inversion] *)

(** Lembre que construtores de um mesmo tipo são
    funções injetoras e disjuntas. A tática
    [inversion] permite explorar estes dois fatos. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** Ao usar [inversion H], pedimos que Coq
    gere todas as equações que ele consegue
    inferir a partir de [H], além de realizar
    reescrita de variáveis a partir das equações
    derivadas. *)

  inversion H.
  reflexivity.
Qed.

(** Outro exemplo. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity.
Qed.

(** Podemos nomear as equações que [inversion]
    gera com uma cláusula [as ...]. *)

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. 
  reflexivity.
Qed.

(** **** Exercise: (inversion_ex3)  *)
Example inversion_ex3 : forall (X : Type)
  (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros. inversion H0. reflexivity.
Qed.

(** Quando uma hipótese considera uma igualdade
    entre construtores diferentes, a tática
    [inversion] resolve o objetivo de prova
    imediatamente. *)
    
Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl. intros H.

(** Ao usar [inversion] em [H],
    Coq conclui a prova. *)
    
    inversion H.
Qed.

(** Isto é uma instância do _princípio da explosão_,
    que afirma que a partir de uma hipótese
    contraditória, pode-se concluir qualquer fato.
    
    Em Latim: ex falso (sequitur) quodlibet (EFQ),
    Em Inglês: from falsehood, anything (follows) *)

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra.
Qed.

(** **** Exercise: (inversion_ex6)  *)
Example inversion_ex6 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros. inversion H.
Qed.

(** A injetividade de construtores permite concluir que
    [forall (n m : nat), S n = S m -> n = m]. O converso
    desta implicação é um fato mais geral,
    que pode ser útil. *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq. rewrite eq. reflexivity.
Qed.

(* ############################################### *)
(** * Usando táticas em hipótese *)

(** A maior parte das táticas possui uma variante
    que permite sua aplicação em uma afirmação
    do contexto. *)
    
Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

(** Contudo, [apply L in H] funciona como "forward
    reasoning", enquanto que [apply L], como "backward
    reasoning". *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5  ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.
Qed.

(** Provas informais tendem a usar "forward
    reasoning". Coq tende a favorecer o uso de
    "backward reasoning". *)

(** **** Exercise: (plus_n_n_injective)  *)
(** Dica: faça uso de plus_n_Sm. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros. Search "plus_n_Sm". induction n as [|n' IHn].
  - simpl in H. Search (_ + _).
    + induction m as [| m' IHm].
      * reflexivity.
      * inversion H.
  - simpl in H. Search "plus_n_Sm".
    + destruct m as [| m'].
      * inversion H.
      * Search "plus_n_Sm". rewrite <- plus_n_Sm in H. simpl in H.
        rewrite <- plus_n_Sm in H. inversion H.
Qed.

(* ############################################### *)
(** * Variando a hipótese indutiva *)

(** É preciso ter cuidado com o uso de [intros];
    com o que se move do objetivo para o contexto
    antes de realizar uma prova por indução. Veja
    o exemplo a seguir. *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *) apply f_equal.

(** Neste momento, [IHn'] não possui [n' = m'].
    Há um [S] extra. Logo, não podemos concluir
    a prova. *)

Abort.

(** O problema aconteceu ao fazer a instanciação
    universal de [m]. A prova acima diz para Coq
    considerar um [n] e um [m] particular, e agora
    tentar provar que, se [double n = double m] para
    estes valores particulares de [n] e [m],
    então [n = m]. Pela indução, tentamos provar
    que para todo [n]:

      - [P n] = "if [double n = double m], then [n = m]"

    é verdade, mostrando que

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") e

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]"
        implies "if [double (S n) = double m]
        then [S n = m]"
    
    o que não faz sentido para um [m] arbitrário. Veja
    o seguinte exemplo ([m = 5]), temos que:

      - [Q] = "if [double n = 10] then [n = 5]"

    o que não ajuda a provar a próxima afirmação:

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    É preciso fazer a indução sem mover
    [m] para o contexto.
      
*)

Theorem double_injective : forall n m,
     double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) simpl.

(** Veja que o objetivo de prova e a IH
    são diferentes neste teorema em relação
    ao anterior. *)
    
    intros m eq. destruct m as [| m'].
    + (* m = O *) simpl. inversion eq.
    + (* m = S m' *) apply f_equal.
      apply IHn'. inversion eq. reflexivity.
Qed.

(** **** Exercise: (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
 (* COMPLETE AQUI *) Admitted.

(** Nem sempre fazer menos instanciações universais
    (para obter IHs mais gerais) é suficiente. Veja
    o exemplo a seguir. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
    (* Não temos como progredir neste ponto. *)
Abort.

(** O problema é que para fazer indução sobre [m],
    é preciso primeiro instanciar [n]. Para resolver
    esta situação, é preciso generalizar [n], antes
    de fazer indução sobre [m]. Isto é feito pela
    tática [generalize dependent]. *)

Theorem double_injective_take2 : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity.
Qed.

(** **** Exercise: (gen_dep_practice)  *)
(** Prova com indução sobre [l]. *)

Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
     length l = n -> nth_error l n = None.
Proof.
 (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - More basic tatics
  https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html
*)
