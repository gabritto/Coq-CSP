(** * Indução em Coq *)

Require Export aula04_inducao.
Module NatList.

(* ############################################### *)
(** * Pares de números *)

(** A seguinte declaração pode ser lida como
    "só existe uma maneira de construir um
    par de números, que é aplicando o construtor
    [pair] a dois argumentos do tipo [nat]" *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

(** Definindo funções para pares.
    Observe o casamento de padrão. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(* Definindo uma notação mais conveniente. *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

(* Observe que é possível, inclusive,
   usar esta sintaxe no casamento de padrões. *)

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Algumas provas associadas a pares. *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  simpl. reflexivity.
Qed.

(** Observe que o próximo teorema representa
    o mesmo fato, mas [reflexivity] não
    é suficiente para concluir esta prova. *)

Theorem surjective_pairing_stuck :
  forall (p : natprod),
    p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** É preciso expor a estrutura de [p], tal
    que [simpl] possa realizar casamento de
    padrão. [destruct] permite fazer isto. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

(** **** Exercise: (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p as [x y]. simpl. reflexivity.
Qed.

(* ############################################### *)
(** * Lista de números *)

(** Definição de uma lista de números. *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(** Exemplo de uma lista com 3 elementos. *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Definindo uma notação mais conveniente. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** As definições a seguir são equivalentes. *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** Definindo funções para listas. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:
[1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2:
nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:
[1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(** Na definição a seguir, observe o
    valor [default]. *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:
hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:
hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:
tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(** **** Exercise: (list_funs)  *)
(** Complete as definições de [nonzeros],
    [oddmembers] e [countoddmembers]. Os testes
    mostram o comportamento esperado. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | n :: t => n :: nonzeros t
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint filter (p: nat -> bool)(l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if p h then h :: filter p t else filter p t
  end.

Fixpoint oddmembers (l:natlist) : natlist := filter oddb l.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l: natlist): nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* ############################################### *)
(** * Representando multiconjuntos como listas *)

Definition bag := natlist.

(** **** Exercise: (bag_functions)  *)
(** Complete as definições de: [count], [sum],
    [add], e [member] para multiconjuntos (bags).
    Os testes mostram o comportamento esperado. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match beq_nat v h with
              | true => 1 + count v t
              | false => count v t
              end
  end.

Example test_count1:
  count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2:
  count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

(** A operação [sum] em multiconjuntos é similar
    ao conceito de [union] de conjuntos: [sum a b]
    contém todos os elementos de [a] e [b].

    Observe que a próxima definição não possui
    nome para os parâmetros, mas somente seus tipos.
    Além disto, a definição não é recursiva. Portanto,
    [sum] precisa ser definida em função de definições
    passadas. *)

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1:
  count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  v :: s.

Example test_add1:
  count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:
  count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

(** Observe que a próxima definição
    também não é recursiva. *)

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat 0 (count v s)).

Example test_member1:
  member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2:
  member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(** **** Exercise: (bag_theorem)  *)
(** Prove o seguinte teorema. Talvez você
    precise provar um teorema auxiliar. *)

Lemma beq_n: forall n: nat,
  beq_nat n n = true.
Proof.
  induction n as [| n' IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

Theorem bag_theorem :
  forall (v : nat) (b : bag),
    (count v (add v b)) = (1 + (count v b)).
Proof.
  intros.
  simpl. try reflexivity.
  rewrite beq_n.
  reflexivity.
Qed.

(* ############################################### *)
(** * Raciocinando sobre listas *)

(** Algumas propriedades podem ser provadas
    somente com [reflexivity]. *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
  Print app. simpl. reflexivity.
Qed.

(** Às vezes, será preciso fazer análise de casos. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  (* Observe a quantidade de elementos
     da segunda lista do destruct. *)
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = cons n l' *)
    Print length. simpl. reflexivity.
Qed.

(** Às vezes, será preciso fazer indução. *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  Print app.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. reflexivity.
  - (* l1 = cons n l1' *)
    Print app. simpl.
    rewrite -> IHl1'. reflexivity.
Qed.

(** Considere a seguinte definição de [rev]. *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:
  rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:
  rev nil = nil.
Proof. reflexivity.  Qed.

(** Vamos tentar provar a seguinte afirmação.
    Observe que ficamos "travados" no segundo caso. *) 

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    simpl. rewrite <- IHl'.
    (* Como continuar a partir daqui? *)
Abort.

(** Vamos definir um teorema auxiliar a partir
    do ponto em que ficamos "travados" no
    teorema anterior. Contudo, vamos tornar
    o teorema auxiliar o mais geral possível:
    [l1] e [l2] no lugar de [rev l'] e [n]. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(** Agora concluimos a prova de [rev_length]. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    (* Observe o rewrite  com duas táticas *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(** **** Exercise: (list_exercises)  *)
(** Prove os seguintes teoremas. *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  induction l as [| n' l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [|n1 l1' IH].
  - intros l2. simpl. Search (_ ++ []). rewrite app_nil_r.
    reflexivity.
  - intros l2. simpl. rewrite IH, app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l' IH].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IH. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n1 l1' IH].
  - simpl. reflexivity.
  - simpl. destruct n1.
    + rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

(** **** Exercise: (beq_natlist)  *)
(** Complete a definição de [beq_natlist], que
    compara listas de números. Veja os exemplos.
    Em seguida, prove o teorema [beq_natlist_refl]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | [] =>
    match l2 with
    | [] => true
    | (n2 :: l2') => false
    end
  | (n1 :: l1') => 
    match l2 with
    | [] => false
    | (n2 :: l2') => beq_nat n1 n2 && beq_natlist l1' l2'
    end
  end.
  

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [| n l' IH].
  - reflexivity.
  - simpl. rewrite IH. Search beq_nat.
    rewrite beq_n. simpl. reflexivity.
Qed.

(* ############################################### *)
(** * Options *)

(** Considere a seguinte implementação de uma
    função que retorna o i-ésimo elemento
    de uma lista. *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* um valor arbitrário! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** Outra alternativa seria considerar um
    elemento padrão -- ver definição de [hd].

    Uma melhor solução é definir um "option".
    Similar ao conceito de "maybe" em Haskell. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** Veja agora a função [nth_error]. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 :
  nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 :
  nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 :
  nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** A seguir, uma outra possibilidade de
    implementação de [nth_error] usando "if". *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(** No entanto, cuidado com o "if". *)

Inductive tipo : Type :=
  | cons1 : tipo
  | cons2 : tipo.

Definition beq_tipo (n m : nat) : tipo :=
  if beq_nat n m then cons2 else cons1.

Definition teste_if (n m : nat) : bool :=
  if beq_tipo n m then true
  else false.

Compute (teste_if 2 2).

(** O "if" só pode ser aplicado a tipos
    indutivos com dois construtores. *)

(** A função a seguir retira o [nat] encapsulado
    no [natoption]. Observe aqui o uso do default. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: (hd_error)  *)
(** Use a ideia do "option" e atualize
    a definição da função [hd]. *)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof.
  reflexivity.
Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof.
  reflexivity.
Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof.
  reflexivity.
Qed.

(** **** Exercise: (option_elim_hd)  *)
(** Prove o seguinte teorema relacionando
    [hd_error] com [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End NatList.

(* ############################################### *)
(** * Mapeamentos parciais *)

(** Veja a seguinte definição de mapeamentos parciais,
    similar aos tipos map ou dictionary das
    principais linguagens de programação.

    Inicialmente, definimos a "chave": o [id]. *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: (beq_id_refl)  *)
Theorem beq_id_refl :
  forall x, true = beq_id x x.
Proof.
  intros x. destruct x. simpl.
  Search beq_nat. rewrite NatList.beq_n.
  reflexivity.
Qed.

(** Agora, o tipo de mapeamentos parciais *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** Logo, existem duas maneiras de construir
    [partial_map]: usando o construtor [empty],
    representando o mapeamento vazio; usando
    o construtor [record], passando uma chave,
    um número e um mapeamento existente.

    A função [update] atualiza um mapeamento.
    Observe que, conceitualmente, o valor antigo,
    caso exista, é mantido no mapeamento. O
    primeiro valor será o mais recente. *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Example test_partial_map1 :
  (update empty (Id 0) 3)
  = (record (Id 0) 3 empty).
Proof.
    simpl. reflexivity.
Qed.

Example test_partial_map2 :
  (update (record (Id 0) 2 empty) (Id 0) 3)
  = (record (Id 0) 3 (record (Id 0) 2 empty)).
Proof.
    simpl. reflexivity.
Qed.

(** A função [find] procura por um valor em
    um mapeamento. Se houver múltiplos mapeamentos,
    retorna o primeiro. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.



(** **** Exercise: (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. simpl. destruct x.
  - simpl. rewrite NatList.beq_n. reflexivity.
Qed.

(** **** Exercise: (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false ->
    find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros. simpl. rewrite H. reflexivity.
Qed.

End PartialMap.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Lists
  https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html
*)
(* Site legal: https://pjreddie.com/coq-tactics/*)