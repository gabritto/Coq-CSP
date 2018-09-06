(** * Indução em Coq *)

Set Warnings "-notation-overridden,-parsing".
Require Export aula05_listas.


(* ############################################### *)
(** * Listas polimórficas *)

(** Polimorfismo permite criar definições abstraindo
    os tipos de dados que serão manipulados. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** Agora, [list] é uma função de [Type]s para
    [Type]s. Dado um tipo [X], [list X] é o conjunto
    de listas indutivamente definidas cujos elementos
    possuem tipo [X]. *)

Check list.
(* ===> list : Type -> Type *)
Check (nil nat).
(* ===> nil nat : list nat *)
Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)
Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** Funções sobre listas polimórficas. *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 =
  cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

Example test_repeat2 :
  repeat bool false 1 =
  cons bool false (nil bool).
Proof. reflexivity.  Qed.

(** Coq possui um mecanismo de inferência. *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(** É importante ter um equilíbrio entre o
    que é inferido e o que é informado:
    - inferido: + prática, dificultar entendimento
    - informado: - prático, facilitar entendimento. *)

(** É possível indicar argumentos implícitos: [_]. *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** É possível omitir até o [_]. A diretiva
    [Arguments] especifica o nome de uma função
    (ou construtor) e, em seguida, lista os nomes
    dos seus argumentos, com chaves limitando
    os argumentos que serão implícitos. Se a
    função tiver argumentos sem nome, usar [_]. *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** Agora é possível escrever o seguinte. *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** Também é possível usar chaves na própria
    definição da função. *)
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** Sugestão: usar a última opção para funções
    e a anterior para construtores indutivos.
    Em construtores, torna o tipo implícito
    até para o tipo sendo definido pelo construtor.

    Em alguns casos, será necessário informar
    explicitamente o tipo implícito: [@]. *)

Fail Definition mynil := nil.

(** Alternativas:
    - Declarar o tipo explicitamente
    - Tornar explícito o tipo implícito. *)

Definition mynil : list nat := nil.

Check @nil.
Definition mynil' := @nil nat.

(** Outras funções para listas polimórficas. *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) =
  (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) =
  cons true nil.
Proof. reflexivity.  Qed.

Example test_length1:
  length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(** Definindo uma sintaxe conveniente para listas. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Agora, podemos escrever listas da seguinte forma. *)

Definition list123''' := [1; 2; 3].
Check (list123''').

(** **** Exercise: (poly_exercises)  *)
(** Complete as provas a seguir. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (* COMPLETE AQUI *) Admitted.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* COMPLETE AQUI *) Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Pares polimórficos *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

(** A anotação [: type_scope] diz para Coq
    só usar esta abreviação ao processar tipos.
    Isto impede conflitos com o símbolo da
    multiplicação. *)

(** Algumas funções úteis. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** A função a seguir combina lista de pares. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Example combine_test1 :
  combine [1;2;3] [0;10]
  = [(1,0);(2,10)].
Proof. reflexivity. Qed.

(** **** Exercise: (split)  *)
(** A função [split] é a inversa direita de [combine]:
    dada uma lista de pares, retorna um par de listas. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
(* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

Example test_split:
  split [(1,false);(2,false)] =
  ([1;2],[false;false]).
Proof.
  (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Option polimórfico *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** Reescrevendo [nth_error]. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error l' (pred n)
  end.

Example test_nth_error1 :
  nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 :
  nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 :
  nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** Exercise: (hd_error_poly)  *)
(** Complete a definição polimórfica
    da função [hd_error]. *)

Definition hd_error {X : Type} (l : list X)
           : option X
(* SUBSTITUA COM ":= _sua_definição_ ." *). Admitted.

Example test_hd_error1 :
  hd_error [1;2] = Some 1.
Proof. (* COMPLETE AQUI *) Admitted.

Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof. (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Polymorphism
  https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html
*)
