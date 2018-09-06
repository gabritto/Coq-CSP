(** * Programação funcional em Coq *)

(* ############################################### *)
(** * Instalação *)

(** Passo-a-passo:
  1. Instalar OPAM: gerenciador de pacotes OCaml
  [passo já realizado pelo helpdesk no G3]
  Link: http://opam.ocaml.org/doc/Install.html
  a) wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin

  2. Instalar Coq 8.8.1
  Link: https://coq.inria.fr/opam/www/using.html
  a) abrir o terminal (ctrl + alt + t)
  b) export OPAMROOT=~/opam-coq.8.8.1
     # diretório de instalação no home do usuário
  c) opam init -n --comp=4.02.3 -j 4
     # 4 é o número de núcleos de processamento
  d) opam repo add coq-released http://coq.inria.fr/opam/released
  e) opam install coq.8.8.1 && opam pin add coq 8.8.1

  3. Instalar CoqIDE
  Link: https://coq.inria.fr/opam/www/using.html
  a) opam install coqide
  
  4. Para rodar a IDE, é preciso reexecutar os
  seguintes comandos sempre que abrir um novo
  terminal:
  a) abrir o terminal (ctrl + alt + t)
  b) export OPAMROOT=~/opam-coq.8.8.1
     # diretório em que instalou Coq
  c) eval `opam config env`
     # configurar ambiente
  d) coqide &

  5. Para testar a instalação, abrir o arquivo
  01-exemplo.v e processá-lo até o final
  (ctrl + end). O texto deve ficar todo verde.

  Outra opção de IDE: Emacs + ProofGeneral
  Link: https://proofgeneral.github.io/

  Links úteis:
  - https://github.com/coq/coq
  - https://github.com/coq/coq/wiki
  - https://github.com/coq/coq/wiki/The-Coq-FAQ
*)

(* ############################################### *)
(** * Prefácio *)

(** Material baseado na série Software Foundations
    https://softwarefoundations.cis.upenn.edu/. *)

(** Aspectos centrais deste material:
    - uso de lógica para definir e provar
      afirmações precisas sobre programas
    - uso de um assistente de prova (Coq)
      para construir argumentos lógicos rigorosos
    - programação funcional como ligação
      entre programação e lógica *)

(** Coq: aspectos históricos
    - Em desenvolvimento deste 1984
    - Possíveis origens do nome:
      - Tradição francesa: Caml, Elan, PhoX, etc.
      - Calculus of Constructions
      - Símbolo nacional da França
      - Primeiras três letras de Thierry Coquand *)

(** Coq: aplicações em CS e matemática:
    - Plataforma para modelar PLs
      [instruções x86, C, etc.]
    - Ambiente para desenvolver HW/SW certificado
      [CompCert, CertiKos, RISC-V, etc.]
    - Ambiente para programação funcional
      [Gallina]
    - Assistente de prova para lógica de alta ordem
      [Primeira prova verificada formalmente
       do Teorema das 4 cores] *)

(* ############################################### *)
(** * Gallina: introdução *)

(** Definindo novo tipo: conjunto de valores possíveis.
    - [day] é o nome do tipo
    - a definição [day] é um elemento de [Type]
    - [:=] usado para preceder a definição
    - [|] é usado para separar elementos de [day]
*)

Inductive day : Type :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

(** Definindo uma função que opera sobre dias.
    - [Definition] funções não-recursivas
    - Tipos dnão precisam ser explícitos
    - [:=] precede a definição da função
    - A definição pode ser feita por casamento
      de padrão, como também chamada a outras funções
    - [=>] representa o retorno quando [d]
      casa com uma das opções
 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** Validando a função definida:
    - [Compute]: avalia expressão
    - [Example]: define afirmação a ser verificada
      a) dá um nome à afirmação
      b) permite usar o modo de prova de Coq
         para verificar que a afirmação
         é verdadeira (como um teste unitário)
    - Extrair programa funcional em OCaml ou Haskell
*)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)
 
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (sinal) *)
(** Defina o tipo [sinal] que pode ser verde,
    amarelo ou vermelho. *)

(** **** Exercise: (next_sinal) *)
(** Defina a função [next_sinal] que muda a cor
    de um sinal para a próxima cor esperada *)

(** **** Exercise: (compute_sinal) *)
(** Use [Compute] para testar a definição
    de [next_sinal]. *)

(** **** Exercise: (test_sinal) *)
(** Use [Example] para testar a definição
    de [next_sinal]. Prove que sua
    afirmação é verdadeira usando *)

(* =============================================== *)
(** ** Booleans *)

(** De forma similar, podemos definir o tipo booleano.
    - Não confundir: booleano vs. True e False da lógica *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Definindo funções sobre booleanos
    - Observe a sintaxe para vários parâmetros *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Teste unitários *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.

Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.

Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.

Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** É possível definir uma sintaxe mais familiar
    usando [Notation] *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (nandb) *)
(** Defina nandb (usando casamento de padrão e,
    em seguida, complete os testes unitários. *)

Definition nandb (b1:bool) (b2:bool) : bool
  (* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

Example test_nandb1:
(nandb true false) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb2:
(nandb false false) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb3:
(nandb false true) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb4:
(nandb true true) = false.
(* COMPLETE AQUI *) Admitted.

(** **** Exercise: (nandb') *)
(** Defina nandb' usando as definições [andb] e [negb] *)

Definition nandb' (b1:bool) (b2:bool) : bool
  (* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

(** Nas próximas provas, observe o resultado do
    simpl. Tente antes desta tática, usar
    unfold nandb' (que obriga a expansão da definição
    de nandb'). *)

Example test_nandb'1:
(nandb' true false) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb'2:
(nandb' false false) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb'3:
(nandb' false true) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb'4:
(nandb' true true) = false.
(* COMPLETE AQUI *) Admitted.

(** **** Exercise: (andb3)  *)
(** Defina a função [andb3]. Esta função deve
    retornar [true] quando todas suas entradas
    são [true], e [false] caso contrário *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

Example test_andb31:
(andb3 true true true) = true.
(* COMPLETE AQUI *) Admitted.
Example test_andb32:
(andb3 false true true) = false.
(* COMPLETE AQUI *) Admitted.
Example test_andb33:
(andb3 true false true) = false.
(* COMPLETE AQUI *) Admitted.
Example test_andb34:
(andb3 true true false) = false.
(* COMPLETE AQUI *) Admitted.

(* =============================================== *)
(** ** Function Types *)

(** Toda expressão em Coq tem um tipo. O comando
    [Check] imprime o tipo de uma expressão. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** A função [negb] é também o valor de um dado, assim
    como [true] e [false]. Seu tipo é chamado
    _function types_, e escrito usando setas *)

Check negb.
(* ===> negb : bool -> bool *)

(** [negb] é uma função que dado um [bool],
    produz um [bool]. *)

Check andb.
(* ===> andb : bool -> bool -> bool *)

(** [andb] é uma função que a partir de dois [bool],
    produz um [bool]. *)

(* =============================================== *)
(** ** Tipos compostos *)

(** Tipos definidos até então: enumerações. Cada opção
    criada a partir de um certo _construtor_. *)

Inductive rgb : Type :=
  | red   : rgb
  | green : rgb
  | blue  : rgb.

(** A definição a seguir possui o construtor [primary]
    que recebe um [rgb] e produz um [color]. *)

Inductive color : Type :=
  | black     : color
  | white     : color
  | primary   : rgb -> color.

(** Definindo funções sobre tipos compostos *)

Definition monochrome (c : color) : bool :=
  match c with
  | black     => true
  | white     => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black       => false
  | white       => false
  | primary red => true
  | primary _   => false
  end.

(** No exemplo acima, [primary _] tem o mesmo
    efeito de [primary p]. *)

(* =============================================== *)
(** ** Módulos *)

(** Uma das maneiras de estruturar uma especificação
    em Coq é usar módulos. *)

Module NatPlayground.

(* =============================================== *)
(** ** Números *)

(** Definindo um tipo usando construtores que recebem
    argumentos do tipo sendo definido. *)

(** Números naturais
    - O: uma representação do número zero
    - S _: o sucessor de um número natural *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** Por isso que tipos são (potencialmente) indutivos:
    - [O] é um número natural
    - [S O] é um número natural
    - [S (S O)] é um número natural
    - [S (S false)] não é um número natural *)

(** Esta definição é uma representação estrutural
    sem significado. O significado vem do seu uso *)

Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

(** Exemplo: função [pred] *)

Definition pred (n : nat) : nat :=
  match n with
  | O     => O
  | S n'  => n'
  end.

End NatPlayground.

(** Coq possui definições para representar
    números de forma decimal *)

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

(** Definindo a função [minustwo]. Observe
    os dois primeiros casos *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

(** Tipos dos construtores e das funções
    para [nat] *)

Check S.
Check pred.
Check minustwo.

(** Apesar de todos serem valores, as duas
    últimas definições possuem uma noção
    de computabilidade associada *)

(** Definindo funções recursivas: [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** Definindo [oddb] em função de [evenb] e [negb]. *)

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(** Definindo funções recursivas com
    vários parâmetros *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(** Testando a definição *)
Compute (plus 3 2).
(* ===> 5 : nat *)

(** O passo-a-passo da computação seria: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      pela segunda clásula do [match]
==> [S (S (plus (S O) (S (S O))))]
      pela segunda clásula do [match]
==> [S (S (S (plus O (S (S O)))))]
      pela segunda clásula do [match]
==> [S (S (S (S (S O))))]
      pela primeira clásula do [match]
*)

(** Outra notação para vários parâmetros
    do mesmo tipo *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** Casamento de padrão múltiplo *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

(** Definindo exponenciação: [exp] *)

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O   => S O
  | S p => mult base (exp base p)
  end.

(** **** Exercise: 1(factorial)  *)
(** Defina a função fatorial em Coq
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)
                        (if n>0) *)

Fixpoint factorial (n:nat) : nat
  (* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

Example test_factorial1:
(factorial 3) = 6.
(* COMPLETE AQUI *) Admitted.

Example test_factorial2:
(factorial 5) = (mult 10 12).
(* COMPLETE AQUI *) Admitted.

(** As próximas definições definem uma sintaxe
    para adição, subtração e multiplicação
    - precedência: [at level n], onde n 0..100
      menor valor indica maior precedência      
    - associatividade: [left], [right] ou
                       [no] [associativity]
 *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(** Definindo se dois números são iguais: [beq_nat] *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** Definindo menor ou igual: [leb] *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: (blt_nat)  *)
(** A função [blt_nat] testa se um número é
    menor do que outro. Observe que a próxima
    definição não é recursiva. É preciso definir
    [blt_nat] a partir de definições passadas *)

Definition blt_nat (n m : nat) : bool
  (* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

Example test_blt_nat1:
(blt_nat 2 2) = false.
(* COMPLETE AQUI *) Admitted.

Example test_blt_nat2:
(blt_nat 2 4) = true.
(* COMPLETE AQUI *) Admitted.

Example test_blt_nat3:
(blt_nat 4 2) = false.
(* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Prefácio
  https://softwarefoundations.cis.upenn.edu/lf-current/Preface.html
  - Aspectos básicos (até o final de "Data and Functions")
  https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
*)
