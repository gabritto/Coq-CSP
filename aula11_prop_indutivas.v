(** * Proposições definidas indutivamente *)

Set Warnings "-notation-overridden,-parsing".
Require Export aula09_logica.
Require Coq.omega.Omega.

(* ############################################### *)
(** * Proposições definidas indutivamente *)

(** Veremos agora que também é possível definir
    proposições de forma indutiva (i.e.,
    usando [Indutive].
    
    Por exemplo, podemos dizer que [n] é par
    escrevendo [evenb n = true] ou
    [exists k, n = double k]. Outra possibilidade
    é dizer que [n] é par se este fato pode ser
    deduzido a partir das seguintes regras:
    
    - Regra [ev_0]: o número [0] é par;
    - Regra [ev_SS]: se [n] é par,
                     então [S (S n)] é par.
                     
    Para provar, por exemplo, que [4] é par, pela
    regra [ev_SS], é suficiente provar que [2] é par.
    De novo pela mesma regra, é suficente provar
    que [0] é par. Por sua vez, a regra [ev_0]
    garante que 0 é par.
    
    Estas regras são vistas como regras de inferência.

        ------------                        (ev_0)
           ev 0

            ev n
       --------------                      (ev_SS)
        ev (S (S n))

    Se as premissas da regra foram satisfeitas
    (listadas acima da linha), podemos concluir
    a afirmação listada abaixo da linha.
    
    A prova que [4] é par poderia ser escrita
    da seguinte forma:


               ------  (ev_0)
                ev 0
               ------ (ev_SS)
                ev 2
               ------ (ev_SS)
                ev 4

    Em Coq, podemos, então, definir a propriedade
    de ser par da seguinte forma indutiva. Cada
    construtor corresponde a uma regra de inferência. *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Check ev_0.
Check ev.
Check ev_SS.

(** Observe que esta definição não resulta em um
    [Type], mas uma função de [nat] para [Prop];
    ou seja, uma propriedade sobre números.
    
    Além disto, observe que na definição de ev
    (linha 58), o argumento natural aparece sem
    nome (i.e., à direita do [:]). Na definição
    de listas, por exemplo, temos:
    
    Inductive list (X:Type) : Type :=
    
    Observe que aqui o X aparece antes do [: Type].
    Isto permite [ev] receber valores diferentes
    nos diferentes construtores. Veja que a
    definição abaixo gera um erro. *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** Podemos, portanto, pensar na definição de [ev]
    como a função [ev : nat -> Prop], em conjunto
    com os teoremas primitivos [ev_0 : ev 0] e
    [ev_SS : forall n, ev n -> ev (S (S n))].
    
    Tais "teoremas-construtores" possuem o mesmo
    status de outros teoremas em Coq. Em particular,
    podemos usar [apply] com o nome destes
    "teoremas-construtores". *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... ou ainda por uma perspectiva funcional. *)

Print ev_SS.
Compute (ev_SS).
Compute (ev_SS 0 ev_0).

Theorem ev_4' : ev 4.
Proof.
  Compute (ev_SS 2 (ev_SS 0 ev_0)).
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(** Outro exemplo. *)

Theorem ev_plus4 :
  forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: (ev_double)  *)
Theorem ev_double :
  forall n, ev (double n).
Proof.
  intros n. induction n as [|n'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.

(* ############################################### *)
(** * Usando evidência em provas *)

(** Definir [ev] como uma declaração [Inductive],
    não só diz que [ev_0] e [ev_SS] são formas
    válidas de criar evidência sobre números
    serem pares, mas também que estes dois
    construtores são as _únicas_ formas de criar
    evidência que números são pares (no contexto,
    da definição de [ev]).
    
    Logo, se tivermos uma evidência que [E]
    para a afirmação [ev n], [E] precisa ter uma
    das seguintes formas:

    - [E] é [ev_0] (e [n] é [O]), ou
    - [E] é [ev_SS n' E'] (e [n] é [S (S n')],
      onde [E'] é a evidência para [ev n']).
      
    Portanto, é possível usar táticas como [inversion],
    [induction] e [destruct] em evidências criadas
    indutivamente. *)

(** ** Inversion em evidências *)

(** Neste contexto, [inversion] realiza uma análise
    de casos, e sua sintaxe é similar à do
    [destruct]. Veja o exemplo abaixo. *)
    
Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. 
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** Neste caso, poderíamos ter usado [destruct]. *)

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** Nem sempre o uso de [inversion] e
    [destruct] produz o mesmo resultado. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.

(** Como aqui temos o [ev] aplicado a um
    elemento diferente de 0, esta evidência
    precisa ter sido construída a partir de
    ev_SS. No entanto, a tática [destruct]
    não faz este tipo de análise, e gera
    dois objetivos de prova. *)  
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* Não é possível provar que [n] é par a partir
       de nenhuma premissa. *)
Abort.

(** Veja a prova com [inversion]. A tática [inversion]
    detectou que (1) o caso ev_0 não se aplica, pois
    0 não pode ser igual a [S (S n)] e que (2) em
    [ev_SS n' E'], E = ev n' = ev n, pois n = n',
    uma vez que [S (S n')] = [S (S n)]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* Caso que [E = ev_SS n' E']. *)
  apply E'.
Qed.

(** Também podemos usar [inversion] como
    princípio da explicação em hipóteses
    envolvendo propriedades indutivas
    que são claramente contradições. *)

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not. intros H. inversion H.
Qed.

(** **** Exercise: (SSSSev__even)  *)
(** Prove o seguinte resultado usando [inversion]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E'].
  inversion E' as [| n'' E''].
  apply E''.
Qed.

(** **** Exercise: (even5_nonsense)  *)
(** Prove o seguinte resultado usando [inversion]. *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E. inversion E. inversion H0. inversion H2.
Qed.

(** ** Indução sobre evidências *)

(** Veja o exemplo a seguir. *)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       com IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k').
    simpl. reflexivity.
Qed.

(** Com este resultado, podemos provar
    que a propriedade de ser par definida
    por [ev n] e [exists k, n = double k]
    são equivalentes. *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk].
             rewrite Hk. apply ev_double.
Qed.

(** **** Exercise: (ev_sum)  *)
Theorem ev_sum :
  forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m.
  intros En Em.
  Print Nat.add.
  induction En as [| n' En' IHn].
  - simpl. apply Em.
  - simpl. apply ev_SS. apply IHn.
Qed.

(** **** Exercise: (ev_ev__ev)  *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m. intros Enm En. induction En as [| n' En' IHn].
  - simpl in Enm. apply Enm.
    (** Search (_ + _ = 0 -> _ = 0 /\ _ = 0).
    symmetry in H0. apply Plus.plus_is_O in H0.
    apply proj2 in H0. rewrite H0. apply ev_0.
    **)
  - simpl in Enm. inversion Enm. apply IHn in H0.
    apply H0.
Qed.

(* ############################################### *)
(** * Relações indutivas *)

(** Uma proposição parametrizada por um número
    (como [ev]), pode ser vista como uma propriedade
    sobre números: define um subconjunto de [nat]
    para os quais a propriedade pode ser provada.
    
    De forma similar, uma proposição com dois
    argumentos pode ser vista como uma relação:
    define um conjunto de pares para os quais
    a propriedade em questão pode ser provada. *)

Module Playground.

(** A próxima definição afirma que existem duas
    maneiras de produzir evidência de que um número
    é <= a outro: ou estes números são os mesmos,
    ou então o primeiro é <= ao predecessor
    do primeiro. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** A seguir, alguns testes para demonstrar
    que a definição de [le] é correta. Aqui,
    não é suficiente usar [simpl] e [reflexivity],
    uma vez que a prova não consiste em simplificar
    computações. *)
    
Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S.
  apply le_S. apply le_n.
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H.
  inversion H2.
Qed.

(** O operador [<] pode ser definido
    em termos de [le]. *)

End Playground.

Print le.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Outros exemplos de relações sobre números. *)

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).


(** **** Exercise: (le_exercises)  *)
(** A seguir, vários exercícios sobre as relações
    [<=] e [<], que constituem uma boa prática. *)

Lemma le_trans :
  forall m n o, m <= n -> n <= o -> m <= o.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem lt_S : forall n m,
  n < m -> n < S m.
Proof.(* COMPLETE AQUI *) Admitted.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.(* COMPLETE AQUI *) Admitted.

(** O próximo teorema é mais fácil de provar
    com uma indução sobre [m]. *)
    
Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.(* COMPLETE AQUI *) Admitted.

(** O próximo teorema pode ser provado
    facilmente sem [induction]. *)

Theorem leb_true_trans : forall n m o,
  leb n m = true ->
  leb m o = true -> leb n o = true.
Proof.(* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Estudo de caso: expressões regulares *)

(** Primeiro, a sintaxe. *)

Inductive reg_exp {T : Type} : Type :=
| EmptySet  : reg_exp
| EmptyStr  : reg_exp
| Char      : T -> reg_exp
| App       : reg_exp -> reg_exp -> reg_exp
| Union     : reg_exp -> reg_exp -> reg_exp
| Star      : reg_exp -> reg_exp.

(** Agora, a semântica (como uma relação indutiva). *)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty    : exp_match [] EmptyStr
| MChar     : forall x, exp_match [x] (Char x)
| MApp      : forall s1 re1 s2 re2,
                exp_match s1 re1 ->
                exp_match s2 re2 ->
                exp_match (s1 ++ s2) (App re1 re2)
| MUnionL   : forall s1 re1 re2,
                exp_match s1 re1 ->
                exp_match s1 (Union re1 re2)
| MUnionR   : forall re1 s2 re2,
                exp_match s2 re2 ->
                exp_match s2 (Union re1 re2)
| MStar0    : forall re, exp_match [] (Star re)
| MStarApp  : forall s1 s2 re,
                exp_match s1 re ->
                exp_match s2 (Star re) ->
                exp_match (s1 ++ s2) (Star re).

(** Açúcar sintático. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(** A relação anterior define as seguintes regras.

      ----------------                    (MEmpty)
       [] =~ EmptyStr

      ---------------                      (MChar)
       [x] =~ Char x

   s1 =~ re1    s2 =~ re2
  -------------------------                 (MApp)
   s1 ++ s2 =~ App re1 re2

          s1 =~ re1
    ---------------------                (MUnionL)
     s1 =~ Union re1 re2

          s2 =~ re2
    ---------------------                (MUnionR)
     s2 =~ Union re1 re2

      ---------------                     (MStar0)
       [] =~ Star re

  s1 =~ re    s2 =~ Star re
 ---------------------------            (MStarApp)
    s1 ++ s2 =~ Star re
*)

(** Alguns exemplos. *)

Example reg_exp_ex1 :
  [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 :
  [1; 2] =~ App (Char 1) (Char 2).
Proof.
  Compute (MApp [1] _ [2] _).
  apply (MApp [1] _ [2] _).
  - apply MChar.
  - apply MChar.
Qed.

(** Observe que no caso anterior é preciso
    manualmente informar como dividir a
    string [1;2] em [1] e [2]. Se o objetivo
    fosse [1] ++ [2], Coq conseguiria inferir. *)

Example reg_exp_ex3 :
  ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** Provando que toda string [s] que
    casa com o padrão [re], casa também
    com o padrão [Star re]. *)

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re -> s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Inductively defined propositions
  https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
*)
