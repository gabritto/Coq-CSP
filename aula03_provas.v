(** * Provas em Coq *)

(** - Require: carrega uma biblioteca
      e.g., Require Coq.Lists.List.
    - Import: coloca as definições em escopo
      (sem o Import: precisar referenciar
      os nomes pela identificação completa;
      i.e., fully qualified)
      e.g., Print List.map vs. Print map
    - Require Import: carrega e coloca em escopo
      Não se usa Require ao importar sub-módulos
      e.g., Import ListNotations
    - Require Export: carrega, coloca em escopo
      e torna o módulo visível onde o módulo
      atual for utilizado

  Mais informações:
  - https://coq.inria.fr/tutorial/3-modules
  - https://stackoverflow.com/questions/47973317/require-import-require-import
*)

(** Para importar o arquivo da aula passada,
    é preciso ter a versão compilada dele.
    Comando: coqc aula02_gallina.v *)

Require Export aula02_gallina.

(* ############################################### *)
(** * Prova por simplificação *)

(** Lidando com o quantificador universal:
    considerar a prova no contexto de um membro
    arbitrariamente escolhido no domínio.

    Exemplo:
    Todos os laboratórios possuem datashow.
    Se há datashow, há uma tela de projeção.
    Logo, há tela de projeção em todos os laboratórios.

    Formalização do argumento:
    1. forall l : lab, D(l)            [premissa]
    2. forall l : lab, D(l) -> T(l)    [premissa]
    3. D(a)         [Instanciação Universal em 1]
    4. D(a) -> T(a) [Instanciação Universal em 2]
    5. T(a)               [modus ponens em 3 e 4]
    6. forall l : lab, T(l) [Gen. Universal em 5]

    Idealmente, ao instanciar, devemos usar
    um símbolo diferente do ligado pela
    quantificação universal (e.g., x vs. a).
    Na prática, usa-se o mesmo símbolo.

    1. forall l : lab, D(l)            [premissa]
    2. forall l : lab, D(l) -> T(l)    [premissa]
    3. D(l)         [Instanciação Universal em 1]
    4. D(l) -> T(l) [Instanciação Universal em 2]
    5. T(l)               [modus ponens em 3 e 4]
    6. forall l : lab, T(l) [Gen. Universal em 5]    
    
    Em Coq, a tática [intro] ou [intros] realiza
    IU (instanciação universal), enquanto que
    [generalize dependent] realiza GU
    (generalização universal). A segunda tática
    veremos depois.

    Uma tática é um comando usado entre [Proof]
    e [Qed] para guiar o processo de provar
    alguma afirmação.

    Palavras [Theorem], [Example] e [Lemma]
    possuem praticamente o mesmo significado.
*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

(** [reflexivity] já realiza alguma simplificação
    automaticamente. Mesmo assim, o uso de [simpl]
    pode ser interessante para ver o estado
    intermediário da prova]. *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

(** Inclusive, [reflexivity] realiza algumas
    simplificações adicionais; por exemplo,
    expandindo definições (ver exercício nandb'
    da aula passada = aula02_gallina.v.

    [reflexivity] faz isto, pois se a tática
    funcionar, a prova é concluída e não
    precisaremos ver proposições eventualmente
    mais complicadas em função do processo
    de expansão. *)

(** Outros exemplos de prova *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.
Qed.

(** O sufixo [_l] significa "on the leflt" *)

(* ############################################### *)
(** * Prova por reescrita *)

(** Na próxima prova, a conclusão só é válida
    se [n] e [m] forem o mesmo número (i.e., [n = m]).
    
    A tática [intros] também permite mover para o
    contexto esta hipótese. Em seguida, a tática
    [rewrite] para reescrever o objetivo da prova
    a partir da igualdade descrita na hipótese.

    Por padrão, a reescrita é da esquerda para
    a direita: ->. Logo, pode-se omitir o ->.
    No entanto, da direita para a esquerda é
    necessário usar o símbolo <-.

*)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move [n] e [m] para o contexto *)
  intros n m.
  (* move o antecedente da implicação
     para o contexto sob o nome "H" *)
  intros H.
  (* reescreve o objetivo usando "H" *)
  rewrite -> H.
  reflexivity.
Qed.

(** **** Exercise: (plus_id_exercise)  *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H'.
  rewrite -> H.
  rewrite <- H'.
  reflexivity.
Qed.

(** Lembrando que o comando [Admitted] deve
    ser removido. Ele diz para aceitar,
    no momento, que a afirmação é verdadeira.
    Permite focar nos argumentos principais,
    para depois voltar para as provas auxiliares.
    Contudo, é preciso usar com cuidado
    para não introduzir afirmações falsas como
    verdadeiras *)

(** É possível usar [rewrite] considerando
    teoremas previamente provados. Se a afirmação
    prévia envolver variáveis quantificadas,
    Coq tenta instanciá-las considerando
    o objetivo de prova atual *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  Search (0 + _).
  rewrite -> plus_O_n.
  reflexivity.
Qed.

(** O exemplo anterior ilustra o quanto
    o comando Search pode ser útil.
    Contudo, só funciona nos módulos
    "Required".

    Possibilidades de uso:
    - procura pelo nome: Search "len".
      compare com o resultado de Search len.
    - procura por id: Search False.
    - procura por padrão: Search (0 + _).

    Outros comandos:
    - SearchPattern: somente na conclusão
    - SearchRewrite: conclusões _ = _
    
    Links:
    - https://quanttype.net/posts/2016-04-19-finding-that-lemma.html
    - https://coq.inria.fr/distrib/current/refman/proof-engine/vernacular-commands.html#coq:cmd.search  
*)

(** **** Exercise: (mult_S_1)  *)
(** Prove o seguinte teorema usando [rewrite] *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H1.
  rewrite -> H1.
  Search (1 + _).
  rewrite <- plus_1_l.
  reflexivity.
Qed.

(* ############################################### *)
(** * Prova por análise de casos *)

(** Nem tudo pode ser provado por simplificação e
    reescrita. Veja o caso a seguir. O comando
    [Abort] permite abortar uma prova *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* não faz nada! *)
Abort.

(** Tanto [beq_nat] como [+] faz casamento
    de padrão com o primeiro argumento *)

Print beq_nat.
Print NatPlayground2.plus.

(** Aqui, o primeiro argumento de [+] é [n];
    e de beq_nat, a expressão [n + 1].

    Para avançar, é preciso considerar as
    possíveis formas de [n] *)

Print nat.

(** Um número ou é O (zero) ou o sucessor
    de outro número. A tática [destruct]
    cria uma análise de casos.

    Observe que nesta prova, [0 + 1] pode
    ser simplificado, o que permite simplificar
    beq_nat. No outro caso, beq_nat (S _ + 1) 0
    também permite simplificação pela forma
    que beq_nat foi definido.
*)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** A tática [destruct] permite especificar
    um padrão de introdução (_intro pattern_)
    usando a anotação "[as [| n']]". Este
    padrão é opcional.

    O que vai entre [[]] é uma lista de lista
    de nomes, separadas por |, cada lista
    informando o nome dos elementos a serem
    introduzidos.

    No caso de nat, o primeiro construtor não
    recebe argumentos; logo, a lista vazia. O
    segundo construtor recebe um natural,
    denotado por n'.

    O símbolo [-] separa os casos (sub-objetivos
    de prova). A rigor, estes podem ser omitidos,
    e os comandos irão atuar nos sub-objetivos
    na ordem em que foram criados. No entanto,
    é uma boa prática usuar o símbolo [-].
*)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(** A prova a seguir mostra sub-objetivos
    de prova dentro de outros sub-objetivos
    de prova. *)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** Símbolos: [-], [+] e [*]. Se for preciso
    mais hierarquia, usar [{}]. *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** É possível combinar [intros] com [destruct].
    No exemplo a seguir, "intros [|n].", faz o mesmo
    que "intros x y. destruct y as [|y]." *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(** Se não houver argumentos para o [destruct],
    deve-se usar [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: (andb_true_elim2)  *)
(** Prova a seguinte afirmação usando [destruct] *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c.
  - destruct b.
    + reflexivity.
    + reflexivity.
  - destruct b.
    + simpl. intros H. rewrite H. reflexivity.
    + simpl. intros H. rewrite H. reflexivity.
Qed.

(** **** Exercise: (zero_nbeq_plus_1)  *)
(** Prova a seguinte afirmação usando [destruct] *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.

(* ############################################### *)
(** ** Fixpoints e recursão estrutural *)

(** Toda função em Coq precisa terminar. Para ter
    esta garantia, é necessário ter uma recursão
    estrutural em elementos progressivamente
    "menores". Veja a função "plus". *)

Print NatPlayground2.plus.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(** É possível ter funções que sempre
    terminam, mas que Coq não consegue
    perceber isto. *)

Fail Fixpoint f (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match evenb (S n') with
            | false => f (n'-1)
            | true  => f (n'+2)
            end
  end.

(** Uma alternativa neste caso *)

Fixpoint f'_aux (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f'_aux (n'-1)
  end.

Fixpoint f' (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match evenb (S n') with
            | false => f' (n'-1)
            | true => f'_aux (n'+2)
            end
  end.

(** Outra possibilidade. Qual a
    diferença? *)

Fixpoint f'' (n : nat) (qtd : nat) : bool :=
  match n, qtd with
  | O, _ => true
  | _, O => false
  | S n', S qtd' => match evenb (S n') with
                    | false => f'' (n'-1) qtd'
                    | true  => f'' (n'+2) qtd'
                    end
  end.

(** Entenda as diferenças observadas
    a seguir. *)

Compute (f' 4).
Compute (f'' 4 4).
Compute (f'' 4 3).

(** O comportamento de [f] pode ser resumido assim:
    - Se [n] for zero, então o retorno é true.
    - Se [n] for ímpar, então chama recursivamente
      f' (n'-1). Se [n] é ímpar, então [n'-1]
      também é ímpar, uma vez que [S n = n].
      Logo, todas as próximas chamadas fará [n'-1].
    - Se [n] for par, na primeira recursão
      chama [f] considerando [n'+2], que é sempre
      ímpar, uma vez que [S n = n] e [n] é par.
      Logo, caindo no caso anterior.

    Veja alguns exemplos:
    - [n = 0]
      true
    - [n = 1]
      - [f (1-1) = f 0]
      - true
    - [n = 2]
      - [f (1+2) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 4]
      - [f (3+2) = f 5]
      - [f (4-1) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 5]
      - [f (4-1) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 6]
      - [f (5+2) = f 7]
      - [f (6-1) = f 5]
      - [f (4-1) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    ...      

    Em resumo:
    - [n = 0], 0 recursão
    - [n = 1], 1 recursão
    - [n = 2], 3 recursões
    - [n = 3], 2 recursões
    - [n = 4], 4 recursões
    - [n = 5], 3 recursões
    - [n = 6], 5 recursões
    
    0, 3, 4, 5, 6, 7, ... recursões
    0, 2, 4, 6, 8, 10, ... valor de [n] par
    recursões para n = n/2 + 2, quando n > 0
    recursões para n = 0, quando n = 0

    1, 2, 3, 4, 5, 6, ... recursões
    1, 3, 5, 7, 9, 11, ... valor de [n] ímpar
    recursões para n = (n+1 / 2)

    Veja a próxima definição de [f'''].
    Entenda em como esta difere de chamar
    diretamente [f''].
*)

Definition f'''_aux (n : nat) : nat :=
  match n with
  | 0     => 0
  | S n'  => match evenb n with
             | false  => (Nat.div (n+1) 2)
             | true   => (Nat.div n 2) + 2
             end
  end.

Definition f''' (n : nat) : bool :=
  f'' n (f'''_aux n).

Example f'''_test0 : f''' 0 = true.
Proof. reflexivity. Qed.
Example f'''_test1 : f''' 1 = true.
Proof. reflexivity. Qed.
Example f'''_test2 : f''' 2 = true.
Proof. reflexivity. Qed.
Example f'''_test3 : f''' 3 = true.
Proof. reflexivity. Qed.
Example f'''_test4 : f''' 4 = true.
Proof. reflexivity. Qed.
Example f'''_test5 : f''' 5 = true.
Proof. reflexivity. Qed.
Example f'''_test6 : f''' 6 = true.
Proof. reflexivity. Qed.
Example f'''_test7 : f''' 7 = true.
Proof. reflexivity. Qed.
Example f'''_test8 : f''' 8 = true.
Proof. reflexivity. Qed.
Example f'''_test9 : f''' 9 = true.
Proof. reflexivity. Qed.
Example f'''_test10 : f''' 10 = true.
Proof. reflexivity. Qed.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Aspectos básicos (até o final de "Data and Functions")
  https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
*)
