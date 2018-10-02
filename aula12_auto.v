(** * Automação de táticas *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.omega.Omega.
Require Export aula11_prop_indutivas.

(** Nesta aula, veremos:
    - tacticals: meta-táticas ou táticas de alta ordem
    - provas automáticas com [auto], [omega] e [tauto]
    - uso da linguagem Ltac
    - instancianciação com [eapply] e [eauto]
    
    Benefícios:
    - Tornar as provas mais curtas (?!)
    - Tornar as provas mais robustas *)

(* ############################################### *)
(** * Táticas de alta ordem *)

(** Seja [T] uma tática, [try T] é uma tática
    similar à [T], sendo que, se [T] falha,
    [try T] não faz nada (no lugar de falhar. *)

Theorem silly1 :
  forall (x : nat), x = x.
Proof.
  try reflexivity. (* equivalente à [reflexivity] *)
Qed.

Theorem silly2 :
  forall (x : nat), x + 1 = 1 + x.
Proof.
  try reflexivity. (* só [reflexivity] iria falhar *)
  intros. Search (_ + _ = _ + _).
  rewrite Nat.add_comm.
  try reflexivity. (* equivalente à [reflexivity] *)
Qed.


(** Na sua forma mais básica, a tática [T;T'] recebe
    duas táticas [T] e [T'], primeiro realiza [T] e,
    em seguida, realiza [T'] em cada subjetivo
    gerado por [T]. *)

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros. destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* [destruct] o objetivo corrente *)
  destruct n ;
  (* então [simpl] em cada subjetivo *)
  simpl ;
  (* e [reflexivity] em cada subjetivo *)
  reflexivity.
Qed.

(** A forma mais geral de [;] é
    T ; [T1 | T2 | ... | Tn] onde a tática T1
    é executada no primeiro subjetivo gerado
    por [T], [T2] no segundo, e assim por diante.
    
    [T;T'] é uma abreviação de
    T ; [T' | T' | ... | T'] *)

(** A tática [repeat] repete outra tática
    até esta falhar. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  Print In.
  repeat (try (left; reflexivity); right).
Qed.

(** A tática [repeat T] nunca falha:
    se [T] não se aplica ao objetivo,
    a tática [repeat T] termina come
    sucesso, repetindo [T] 0 vezes. *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** A tática [repeat T] não possui um limite
    de repetições. Observe que [repeat simpl]
    entra em loop infinito. Enquanto todo termo
    em Gallina é garantido terminar, o mesmo não
    se aplica à avaliação de táticas. *)

(** A seguir, mais algumas táticas úteis:

    - [clear H]: apaga a hipótese [H] do contexto;
    
    - [subst x]: procura uma hipótese [x = e] ou
      [e = x] no contexto, e substitui [x] por [e]
      no contexto, no objetivo e apaga a hipótese;
      
    - [subst]: faz todas as substituições possíveis;
    
    - [rename ... into ...]: muda o nome de uma
      hipótese ou variável (e.g., [rename x into y],
      muda todas as ocorrências de [x] para [y],
      assumindo que [x] é uma variável definida
      no contexto);
      
    - [assumption]: procura uma hipótese [H]
      que casa com o objetivo; achando, faz
      [apply H];
      
    - [contradiction]: procura uma hipótese [H]
      que seja logicamente equivalente à [False];
      achando, conclui a prova;
      
    - [constructor]: procura um construtor [c]
      de uma alguma definição indutiva que pode
      ser aplicado para resolver o objetivo; achando,
      faz [apply c]. *)

(** **** Exercise: (not_even_auto)  *)
(** Automatize a prova do seguinte teorema.
    Dica: faça uso de inversion, subst,
          clear, rename, ; e repeat. *)
Theorem not_even_auto : ~ ev 101.
Proof.
  unfold not.
  intros H.
  repeat (inversion H; subst; clear H; rename H1 into H).
Qed.

(* ############################################### *)
(** * As táticas [auto], [omega] e [tauto] *)

(** Até então, scripts de prova aplicando
    hipóteses e lemmas por nome, um por um. *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(** A tática [auto] procura por uma sequência
    de aplicações que prova o objetivo. *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** A tática [auto] resolve objetivos que
    podem ser provados por uma combinação de
    [intros] e [apply] (por padrão, considerando
    hipóteses do contexto local).
    
    O uso de [auto] é "seguro", no sentido que
    nunca falha e nunca muda o objetivo de
    prova: ou resolve o objetivo atual, ou não
    faz nada. *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** Como a busca pode, em princípio, demorar muito,
    existem limites para a busca do [auto]. *)

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* Quando não pode provar, não faz nada. *)
  auto.
  (* Argumento opcional da busca (padrão é 5). *)
  auto 6.
Qed.

(* Além do contexto local, alguns lemmas comuns
   sobre igualdade e operadores lógicos são
   considerados. *)
   
Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(** A tática [omega] implementa um procedimento
    de decisão para um subconjunto da lógica de
    primeira ordem conhecido como aritmética de
    Presburger. Esta é baseada no algoritmo
    inventado por William Pugh em 1991.
    
    Se o objetivo é uma fórmula quantificada
    universalmente sobre:
    
    - constantes númericas, adição (+ e S),
      subtração (- e pred), e multiplicação
      por constantes;
    - igualdades (= e <>) e ordem (<=)
    - e conectivos lógicos /\, \/, not e ->,
    
    então, invocar [omega] irá ou concluir
    a prova ou falhar (quando o objetivo
    for falso ou quando o objetivo
    não satisfizer as condições anteriores). *)

Lemma le_antisym : forall n m: nat,
  (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

(** É possível estender a base de dicas sob demanda. *)

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

(** Também é possível adicionar dicas
    diretamente à base de dicas.
    
    - Hint Resolve T.
      onde [T] é um teorema ou construtor
      de uma proposição definida indutivamente;
    
    - Hint Constructors c.
      equivale a [Hint Resolve] para todos os
      construtores de uma definição indutiva [c];

    - Hint Unfold d.
      É outro comando que pode ser utilizado.

    Também é possível definir bases especializadas
    que podem ser atividadas sob demanda. *)

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* encontra le_antisym a partir da base *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* não faz nada *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Qed.

(** A tática [tauto] implementa um procedimento
    de decisão para cálculo proposicional
    intuicionista definido por Roy Dyckhoff.    
    Esta tática expande negações e equivalências.
    
    O próximo resultado não pode ser provado
    com [auto], mas sim com [tauto]. *)
  
Theorem tauto_example :
  forall (x:nat) (P:nat -> Prop),
    x = 0 \/ P x -> x <> 0 -> P x.
Proof.
  auto.
  tauto.
Qed.

(* ############################################### *)
(** * Definindo novas táticas *)

(** Coq permite definir novas táticas a partir de:
    - Notação [Tactic Notation];
    - Linguagem [Ltac];
    - OCaml API. *)

Tactic Notation "repeat_inv_subst" tactic(h) :=
  inversion h ; subst ; clear h ; rename H1 into h.

Theorem not_even_auto' : ~ ev 101.
Proof.
  unfold not. intros H.
  repeat (repeat_inv_subst H).
Qed.

(** **** Exercise: (bool_fn_applied_thrice_auto)  *)
(** Considerando "find_f_rewrite", reduza
    a prova de bool_fn_applied_thrice'
    (reproduzida abaixo). *)

Theorem bool_fn_applied_thrice' :
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b. destruct (f true) eqn:H1.
  - destruct b.
    + rewrite -> H1. rewrite -> H1.
      rewrite -> H1. reflexivity.
    + destruct (f false) eqn:H2.
      * rewrite -> H1. rewrite -> H1. reflexivity.
      * rewrite -> H2. rewrite -> H2. reflexivity.
  - destruct b.
    + rewrite -> H1. destruct (f false) eqn:H2.
      * rewrite -> H1. reflexivity.
      * rewrite -> H2. reflexivity.
    + destruct (f false) eqn:H2.
      * rewrite -> H1. rewrite -> H2. reflexivity.
      * rewrite -> H2. rewrite -> H2. reflexivity.
Qed.

Ltac find_f_rewrite b :=
  match goal with
    H : _ b = _ |- _ => rewrite -> H
  end.
  
Theorem bool_fn_applied_thrice'' :
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b. destruct (f true) eqn:HT; destruct (f false) eqn:HF; destruct b;
  repeat (repeat find_f_rewrite true; repeat find_f_rewrite false); reflexivity.
Qed.

(* ############################################### *)
(** * As táticas [eapply] e [eauto] *)

(** Em Coq, é possível retardar a instanciação
    de quantificadores através da tática
    [eapply]. Veja o exemplo a seguir. *)

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  try (apply trans_eq).
  (* alternativa vista antes:
     apply trans_eq with (m:=[c;d]). *)
  eapply trans_eq.
  apply eq1. apply eq2.
Qed.

(** Outras táticas como [auto], [exists],
    [constructor] possuem variantes [e...].
    
    Apesar destas variantes serem mais poderosas,
    elas são significamente mais lentas. *)

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Coq Automation
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
  - Auto
  https://softwarefoundations.cis.upenn.edu/lf-current/Auto.html
*)