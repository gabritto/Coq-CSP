(** * Lógica em Coq *)

Set Warnings "-notation-overridden,-parsing".
Require Export aula08_taticas.

(* ############################################### *)
(** * Lógica em Coq *)

(** Em Coq, toda expressão possui um tipo.
    Afirmações lógicas são odo tipo [Prop]. *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** Ser uma proposição, não quer dizer que
    a afirmação pode ser provada verdadeira. *)

Check 2 = 2.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** Proposições são _first-class objects_; logo,
    podem ser manipuladas como outras entidades
    de Coq. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** É possível definir proposições parametrizadas. *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** Em Coq, funções que retornam proposições
    são tidas como definições de propriedades
    sobre seus argumentos. *)
    
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(** O operador [=] é uma função que retorna [Prop].
    Escrever [n = m] é um açúcar sintático para
    [eq n m]. *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(* ############################################### *)
(** * Conectivos lógicos: conjunção *)

(** Se escreve [A /\ B] para representar que [A] e
    [B] são afirmações verdadeiras. Na prova de
    tais afirmações, usa-se a tática split. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** Observe que [apply and_intro] tem o mesmo efeito
    de [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: (and_exercise)  *)
Example and_exercise :
  forall n m : nat,
    n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m. intros eq. split.
  - destruct n.
    + reflexivity.
    + inversion eq.
  - destruct m.
    + reflexivity.
    + Search "plus_n_Sm". rewrite <- plus_n_Sm in eq.
      inversion eq.
Qed.

(** Se no contexto temos [A /\ B], escrever
    [destruct H as [HA HB]] irá remover H e adicionar
    duas novas hipóteses HA e HB. *)

Lemma and_example2 :
  forall n m : nat,
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** É comum em algumas situações se saber que [A /\ B],
    mas precisarmos somente de [A] (ou [B]) para concluir
    a prova. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

(** **** Exercise: (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

(** Os próximos teoremas provam a comutatividade
    e associatividade da conjunção. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

(** **** Exercise: (and_assoc)  *)
(** Dica: É possível usar um padrão de destruct
    _aninhado_; ou seja, [destruct H as [HP [HQ HR]]]. *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split.
  - split. apply HP. apply HQ.
  - apply HR.
Qed.

(* ############################################### *)
(** * Conectivos lógicos: disjunção *)

(** Em Coq, escrevemos [A \/ B], e podemos usar as
    táticas [destruct] ou [intros]. *)

Lemma or_example :
  forall n m : nat,
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* Análise de casos em n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* [n = 0] *)
    rewrite Hn. reflexivity.
  - (* [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** Quando a disjunção está no objetivo,
    podemos usar as táticas [left] e [right]. *)

Lemma or_intro : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m,
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H0. destruct n as [|n'].
  - left. reflexivity.
  - right. simpl in H0. Search "and_exercise".
    apply and_exercise in H0. apply proj1 in H0. apply H0.
Qed.

(** **** Exercise: (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* ############################################### *)
(** * Conectivos lógicos: negação *)

(** Sintaxe em Coq: [~]. Em Coq, [~ P] é definido
    como [P -> False]; onde [False] é uma proposição
    básica contraditória. *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** Como [False] é uma contradição, se ele aparecer
    no contexto, também podemos usar [inversion]
    para concluir a prova. *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

(** Em Latim, ex falso quodlibet significa,
    literalmente, "from falsehood follows
    whatever you like"; outro nome para o
    princípio da explosão. *)
    
(** **** Exercise: (not_implies_our_not)  *)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P. intros NP. intros Q. intros HP. apply NP in HP.
  apply ex_falso_quodlibet. apply HP.
Qed.

(** Usamos a seguinte notação para representar
    o fato que dois naturais são diferentes. *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

(** Sintaxe alternativa. *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  unfold not. intros H. inversion H.
Qed.

(** É necessário um pouco de prática para
    se acostumar com o uso da negação em Coq. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything :
  forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G.
  apply G. apply H.
Qed.

(** **** Exercise: (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q PQ. unfold not. intros QF. intros HP.
  apply QF. apply PQ. apply HP.
Qed.

(** **** Exercise: (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros [HP PF]. apply PF. apply HP.
Qed.

(** Como desigualdades usam negação, é preciso prática
    para se acostumar com o seu uso em Coq. Ao tentar
    provar algo claramente absurdo (e.g., [false = true]),
    aplique [ex_falso_quodlibet] para mudar o objetivo
    da prova para [False]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Como uso de [ex_falso_quodlibet] é comum,
    há uma tática específica em Coq chamada
    [exfalso]. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso. apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

(** Em Coq, [True] define uma proposição básica
    que é trivialmente verdadeira. Para prová-la,
    usamos a constante predefinida [I : True]. *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(* ############################################### *)
(** * Equivalência lógica *)

(** Em Coq, o "se e somente se" é representado
    como a conjunção de duas implicações. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  unfold iff. split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *)
    apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'.
    inversion H'.
Qed.

(** **** Exercise: (iff_properties)  *)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P. split.
  - intros HP. apply HP.
  - auto.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R iffPQ iffQR.
  split.
  - Search (?E /\ _ -> ?E). apply proj1 in iffPQ. apply proj1 in iffQR.
    intros HP. apply iffQR. apply iffPQ. apply HP.
  - apply proj2 in iffPQ. apply proj2 in iffQR.
    intros HR. apply iffPQ. apply iffQR. apply HR.
Qed.

(** **** Exercise: (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  {
    intros [HP | [HQ HR]].
    {
      split.
      - left. apply HP.
      - auto.    
    }
    {
      split.
      - right. apply HQ.
      - auto.
    } 
  }
  {
    intros [[HP | HQ] [HP' | HR]].
    - left. apply HP.
    - auto.
    - auto.
    - auto.
  }
Qed.

(** As táticas [rewrite] e [reflexivity] podem
    ser usadas com afirmações se e somente se,
    não somente com igualdades. Isto é suportado
    pela biblioteca Setoid. *)

Require Import Coq.Setoids.Setoid.

(** Primeiro, provando algumas equivalências. *)

Lemma mult_0 : forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop,
    P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** Agora, podemos usar [rewrite] e [reflexivity]
    com as equivalências antes provadas. *)
    
Lemma mult_0_3 :
  forall n m p,
    n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0.
  rewrite or_assoc. reflexivity.
Qed.

(** A tática [apply] também pode ser usada com [<->].
    Nesses casos, a tática tenta advinhar qual
    lado da equivalência usar. *)

Lemma apply_iff_example :
  forall n m : nat,
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ############################################### *)
(** ** Quantificação existencial *)

(** Em Coq, escrevemos [exists x : T, P]. Assim como
    o [forall], a anotação [: T] pode ser omitida
    se Coq tiver como inferir o tipo de [x].
    
    Para provar uma afirmação usando [exists x], primeiro
    precisamos explicitamente dizer a Coq qual
    testemunha (witness) [t] deve ser usada para [x].
    Para tanto, usamos a tática [exists t].
    
    Em seguida, devemos provar que a afirmação é verdadeira
    com toda ocorrência de [x] substituída por [t]. *)

Lemma four_is_even :
  exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Se o [exists x] estiver no contexto, podemos
    destruir para obter uma testemunha [x] e
    uma hipótese afirmando que [P] é verdade. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intro n. intro H. destruct H as [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(** **** Exercise: (dist_not_exists)  *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P. intros H. unfold not. intros contra.
  destruct contra as [x' contra']. apply contra'. apply H.
Qed.

(** **** Exercise: (dist_exists_or)  *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <->
  (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [HP | HQ].
    + destruct HP as [x HP].
      exists x. left. apply HP.
    + destruct HQ as [x HQ].
      exists x. right. apply HQ.
Qed.

(* ############################################### *)
(** ** Programando com proposições *)

(** Podemos definir proposições complexas a partir
    de outras proposições simples. *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
  
(** Quando [In] é aplicado a uma lista concreta,
    sua aplicação expande para uma sequência de
    disjunções aninhadas. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

(** No exemplo a seguir, observe o uso do
    padrão vazio: []. *)

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(** Podemos definir e provar afirmações mais gerais.
    Observe que, inicialmente, [In] é aplicado a uma
    variável e só é expandido ao fazer análise
    de casos sobre esta variável. *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradição *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** Esta maneira de definir proposições recursivamente,
    apesar de conveniente, está sujeita à limitação
    de definição de funções recursivas em Coq. *)

(** **** Exercise: (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l. induction l as [|x l' IHl'].
  - simpl. intros y. split.
    + intros F. inversion F.
    + intros [x H]. apply proj2 in H. apply H.
  - intros y. split.
    + intros [H | H].
      * exists x. split. apply H. left. reflexivity.
      * simpl. apply IHl' in H. destruct H as [x' H].
        exists x'. split.
          { apply proj1 in H. apply H. }
          { destruct H as [H1 H2]. right. apply H2. }
    + intros He. simpl.
      destruct He as [x' H]. destruct H as [H1 H2]. simpl in H2.
        destruct H2 as [H2 | H2].
      * left. rewrite H2. apply H1.
      * right. apply IHl'. exists x'. split.
        { apply H1. }
        { apply H2. } 
Qed.

(** **** Exercise: (In_app_iff)  *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l'. induction l as [| a' l1 IHl1].
  - split.
    + simpl. intros H. right. apply H.
    + simpl. intros [contra | H].
      * inversion contra.
      * apply H.
  - split.
    + simpl. intros [H | H].
      * left. left. apply H.
      * apply IHl1 in H. destruct H as [H | H].
        { left. right. apply H. }
        { right. apply H. }
    + intros [H | H].
      * simpl in H. simpl. destruct H as [H | H].
        { left. apply H. }
        { right. apply IHl1. left. apply H. }
      * simpl. right. apply IHl1. right. apply H.
Qed.

(** **** Exercise: (All)  *)
(** Defina uma função recursiva [All] que retorna uma
    proposição afirmando que uma propriedade [P] é
    satisfeita por todos os elementos da lista. Em seguida,
    para provar que sua definição é correta, prove o
    lemma [All_In]. *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | (x :: l') => P x /\ All P l'
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. induction l as [| t l' IHl'].
  - split.
    + simpl. intros H. apply I.
    + simpl. intros H. intros x. intros false. inversion false.
  - split.
    + simpl. intros H. split.
      * apply H. left. reflexivity.
      * apply IHl'. intros x. intros Hin.
        apply H. right. apply Hin.
    + simpl. intros [H1 H2]. intros x.
      intros H.
      rewrite <- IHl' in H2.
      destruct H as [H | H].
      * rewrite <- H. apply H1.
      * apply H2. apply H.
Qed.

(* ############################################### *)
(** * Aplicando teoremas a argumentos *)

(** Em Coq, _provas_ são também "first-class objects".
    Mais informações em:
    https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
    https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html

    Veja o exemplo a seguir. *)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* voltamos ao ponto inicial *)
Abort.

(** Uma alternativa é criar uma versão
    especializada de [plus_comm] usando [assert]. *)

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** Ou, de forma mais elegante, aplicar [plus_comm]
    diretamente aos argumentos para os quais
    desejamos instanciar a prova [plus_comm]. *)

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

(** Logo, é possível usar teoremas como funções! *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  Print proj1.
  Print In_map_iff.
  Search "In_map_iff".
  Compute (proj1 _ _).
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm.
  rewrite <- Hm. reflexivity.
Qed.

(**
In_map_iff:
  forall (A B : Type) (f : A -> B) (l : list A) (y : B), In y (map f l) <-> (exists x : A, f x = y /\ In x l)

In_map_iff:
  f = fun m => m * 0
  y = n
  l = ns
result:
  In n (map (fun m => m * 0) ns) <-> (exists x: nat, x * 0 = n /\ In x ns)
result rewriten:
  In n (map (fun m => m * 0) ns) -> (exists x: nat, x * 0 = n /\ In x ns)
  /\ In n (map (fun m => m * 0) ns) <-> (exists x: nat, x * 0 = n /\ In x ns)

proj1 _ _ result:
  In n (map (fun m => m * 0) ns) -> (exists x: nat, x * 0 = n /\ In x ns)
applied to H:
  (exists x: nat, x * 0 = n /\ In x ns)
**)

(* ############################################### *)
(** * Coq vs. Teoria dos conjuntos *)

(** O core lógico de Coq é baseado no _Calculus of
    Inductive Constructions_, que, por sua vez,
    difere de outros sistemas formais como
    a teoria de conjuntos de Zermelo-Fraenkel (ZFC).

    Por exemplo, em ZFC, um elemento pode ser membro
    de vários conjuntos. Em Coq, um termo é membro
    de no máximo um tipo. Logo, no lugar de dizer
    que um número natural [n] pertence ao conjunto
    dos números pares, em Coq, dizemos que a
    afirmação [ev n] é verdadeira, onde
    [ev : nat -> Prop].

    Contudo, há casos em que expressar uma certa
    afirmação em Coq não é algo direto, às vezes,
    nem possível, exceto se enriquecermos a lógica
    suportada por Coq com axiomas adicionais. *)

(** ** Functional Extensionality *)

(** Duas funções [f] e [g] são consideradas iguais
    se elas produzem a mesma saída para toda
    entrada possível.

    (forall x, f x = g x) -> f = g
    
    Esta definição é conhecida como o princípio
    da _functional extensionality_, e ela não faz
    parte dos axiomas básicos definidos em Coq.
    Logo, proposições envolvendo este conceito
    não podem ser provadas. *)
    
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** Contudo, podemos axiomatizar esta definição
    usando o comando [Axiom]. *)

Axiom functional_extensionality :
  forall {X Y: Type} {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.

(** O efeito de [Axiom] é o mesmo de definir um
    Teorema e não prová-lo, através do uso
    de [Admitted]. Contudo, aqui, não existe
    a intenção de provar posteriormente a afirmação. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** É preciso ter cuidado ao adicionar novos
    axiomas para não introduzir inconsistências.
    Não é simples, em linhas gerais, provar
    a consistência lógica de um conjunto de axiomas.
    
    No caso particular do functional extensionality,
    este é consistente com o core lógico de Coq.
    
    O comando [Print Assumptions] imprime que
    axiomas adicionais foram utilizados em uma
    certa prova. *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** ** Proposições e Booleanos *)

(** Podemos definir fatos lógicos usando _booleanos_ 
    ou _proposições_. Por exemplo, dizer que [n] é
    par, pode ser representado dizendo que
    
    (1) [evenb n] retorna [true] ou
    (2) que existe um [k] tal que [n = double k]
    
    Estas duas definições são equivalentes. *)

(** Definindo lemmas auxiliares. *)

Theorem evenb_S :
  forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  intro n. induction n as [| n'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl.
    Search (negb (negb _)).
    rewrite negb_involutive.
    reflexivity.
Qed.

Theorem evenb_double :
  forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n. induction n as [| n'].
  - simpl. exists 0. reflexivity.
  - destruct IHn' as [k H].
    rewrite -> evenb_S. unfold negb.
    destruct (evenb n') eqn: H1.
    + exists k. rewrite H. reflexivity.
    + exists (S k). simpl. rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  induction n as [| n'].
  - simpl. split.
    + intros eq. exists 0. reflexivity.
    + intros ex. reflexivity.
  - split.
    + intros H. Compute (evenb_double_conv _).
      destruct (evenb_double_conv (S n')) as [k H0].
      rewrite H in H0. exists k. apply H0.
    + intros [k H0]. rewrite H0. apply evenb_double.
Qed.

(** Dizemos, portanto, que a computação de
    [evenb n] _reflete_ a proposição lógica
    [exists k, n = double k]. Veja outro exemplo
    a seguir. *)
    
Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intro n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'.
    reflexivity.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.

(** Em algumas situações, a definição proposicional
    é mais útil do que a booleana. Por exemplo,
    saber que [beqnat n m = true] pode não ser tão
    útil quanto saber que [n = m]; uma vez que,
    a segunda opção permite realizar reescrita.
    
    Contudo, em outras situações, a definição
    booleana é mais útil. Por exemplo, Coq
    não permite testar se uma proposição
    qualquer é verdadeira ou falsa na definição
    de uma função. Veja que o código abaixo
    não é aceito. *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq reclama que [n = 2] tem tipo [Prop],
    quando ele espera outro tipo indutivo com
    dois elementos (construtores). Isto está
    associado com o fato que em Coq toda função
    é total e precisa ser computável (em particular,
    para permitir a extração de código executável.
    
    Se fosse permitir usar [Prop] em uma análise
    de casos, seria possível escrever funções
    não computáveis.
    
    Em alguns casos, mesmo tendo uma propriedade
    computável, é mais fácil defini-la usando
    [Prop], uma vez que funções em Coq possuem
    restrições significativas na sua definição. 
    
    Por outro lado, um ponto positivo em definir
    fatos de forma computável é permitir certa
    automação através da computação de termos em
    Coq. Esta é uma técnica conhecida como _proof
    by reflection_. Veja o exemplo a seguir. *)

Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. simpl. reflexivity. Qed.

Example even_1000'' : exists k, 1000 = double k.
Proof.
  Print even_bool_prop.
  apply even_bool_prop.
  reflexivity.
Qed.

(** **** Exercise: (logical_connectives)  *)
(** Os próximos lemmas relacionam conectivos lógicos
    com as respectivas operações booleanas. *)
    
Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  - simpl. intros H. destruct b1.
    + destruct b2.
      * auto.
      * auto.
    + simpl in H. rewrite H. destruct b2.
      * auto.
      * auto.
  - intros [H1 H2]. rewrite H1. rewrite H2. simpl. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1.
    + left. reflexivity.
    + destruct b2.
      * right. reflexivity.
      * simpl in H. rewrite H. left. reflexivity.
  - intros [H | H].
    + rewrite H. simpl. reflexivity.
    + rewrite H. destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

(** ** Lógica clássica vs. construtivas *)

(** Anteriormente, vimos que não é possível
    verificar se uma proposição [P] é verdadeira
    ou não dentro da definição de uma função
    em Coq. O mesmo se aplica para provas. 
    O seguinte princípio não é possível derivar
    a partir dos axiomas definidos em Coq. *)

Definition excluded_middle :=
  forall P : Prop, P \/ ~ P.

(** Ao provar objetivos na prova [_ \/ _],
    usamos [left] ou [right] que, implicitamente,
    requer saber qual lado da disjunção é
    verdadeiro. Contudo, neste caso, nada se
    sabe sobre [P]. No entanto, se [P] for
    refletido em algum termo booleano [b],
    é possível realizar a prova; basta checar
    o valor de [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P b H. destruct b.
  - left. rewrite H. reflexivity.
  - right. rewrite H. unfold not.
    intros contra. inversion contra.
Qed.

(** Em particular, a propriedade de _excluded middle_
    é válida para equações [n = m] entre números
    naturais [n] e [m]. *)

Theorem restricted_excluded_middle_eq :
  forall (n m : nat), n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry. apply beq_nat_true_iff.
Qed.

(** Como consequência de não assumir o _excluded middle_,
    se existe uma prova para [exists x, P x], então é
    possível explicitar um valor para [x] tal que
    [P x] é verdade; em outras palavras, toda prova
    de existência é _construtiva_. Lógicas como ZFC
    são tidas como lógicas clássicas. *)

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Logic in Coq
  https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html
*)
