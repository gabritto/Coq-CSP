Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.String.

Module CSP_Syntax.

Set Implicit Arguments.
Import ListNotations.
Open Scope string_scope.

Definition Event: Type := string.

Theorem Event_eq_dec: forall (x y: Event), {x = y} + {x <> y}.
Proof.
  apply string_dec.
Qed.

Definition Alphabet: Type := set Event.

Inductive Proc: Type :=
  | Stop: Proc
  | Skip: Proc
  | ProcPref: Event -> Proc -> Proc
  | ProcExtChoice: Proc -> Proc -> Proc
  | ProcCond: bool -> Proc -> Proc -> Proc
  | ProcName: string -> Proc. 
  
Inductive DefProc: Type :=
  | Def: string -> Proc -> DefProc.

Inductive Spec: Type :=
  | SpecDef: Alphabet -> list DefProc -> Spec. 

Module CSP_Syntax_Notations.
(* set notations *)

(*TODO: Think about using list instead of set for convenience *)
(*
Notation "{ }" := nil (format "{ }").
Notation "{ x }" := (set_add _ x nil).
Notation "{ x ; y ; .. ; z }" := (set_add _ x (set_add _ y .. (set_add _ z nil) ..)).
*)

(* CSP *)
Notation "a -->> p" := (ProcPref a p)
  (at level 60, right associativity).
                      
Notation "p [-] q" := (ProcExtChoice p q)
  (at level 60, right associativity).
                     
Notation "'if' b 'then' p 'else' q" := (ProcCond b p q)
  (at level 60, right associativity).

Notation "p '" := (ProcName p)
  (at level 60, no associativity).

Notation "p ::= q" := (Def p q)
  (at level 99, no associativity).

Notation "'channel' a , 'definitions' ds" := (SpecDef a ds)
  (at level 99, no associativity).
  
Check "P"'.
(* Notation for lists that are sets using set_add *)

Example procTest := channel ["a"; "b"],
  definitions ["P" ::= ("a" -->> Stop) [-] ("b" -->> Stop)].

Check procTest.

End CSP_Syntax_Notations.

Import CSP_Syntax_Notations.

Fixpoint process_names (spec: Spec): list string :=
  match spec with (SpecDef a procs) =>
    map (fun d => match d with (Def s _) => s end) procs
  end.

Compute process_names procTest.

Search "distinct".
Search "unique".

Fixpoint distinct {T: Type}
  (T_eq_dec: forall (x y: T), {x = y} + {x <> y}) (l: list T): Prop :=
  match l with
  | [] => True
  | t :: l' => let t_unique := In t l' in
    t_unique /\ distinct T_eq_dec l'
  end.

Definition Trace: Type := list Event.

Theorem Trace_eq_dec: forall (x y: Trace), {x = y} + {x <> y}.
Proof.
  Search "list_eq_dec". apply list_eq_dec. apply Event_eq_dec.
Qed.

(* Trace and set of Traces definitions *)

Definition emptyTrace: Trace := nil.

Definition setAdd := set_add Trace_eq_dec.

Definition sngTrace (e: Trace) := setAdd e (empty_set _).

Definition setUnion := set_union Trace_eq_dec.

Definition setMap := @set_map Trace Trace Trace_eq_dec.

Lemma set_union_not_empty: forall {T: Type}
  {T_eq_dec: forall (x y: T), {x = y} + {x <> y}}
  (s t: set T),
  s <> empty_set T -> set_union T_eq_dec s t <> empty_set T.
Proof.
  intros T eq_dec s t.
  destruct t as [ |b t'].
  - unfold empty_set. intros H. simpl. apply H.
  - intros H. simpl. apply set_add_not_empty.
Qed.

Lemma sngTrace_not_empty: forall (t: Trace), [t] <> empty_set Trace.
Proof.
  intros t.
  unfold sngTrace.
  unfold empty_set. intros H. inversion H.
Qed.

(* Functional definition of the set of traces of a process*)
Fixpoint traces (p: Proc): set Trace :=
  match p with
  | Stop => [[]]
  | Skip => [[]]
  | ProcPref e q =>
    let qTraces := traces(q) in
    let qWithA := setMap (fun trace => e :: trace) qTraces in
      setUnion [[]] qWithA
  | ProcExtChoice p q => setUnion (traces p) (traces q)
  | ProcCond b p q => if b then (traces p) else (traces q)
  | _ => [[]]
  end.    

Theorem traces_non_empty: forall (p: Proc),
  traces p <> empty_set Trace.
Proof.
  intros p. induction p.
  - simpl. unfold empty_set. intros H. inversion H.
  - simpl. unfold empty_set. intros H. inversion H.
  - simpl. unfold setUnion. simpl. Search (_ <> empty_set).
    apply set_union_not_empty. apply sngTrace_not_empty.
  - simpl. apply set_union_not_empty. apply IHp1.
  - simpl. destruct b.
    + apply IHp1.
    + apply IHp2.
  - simpl. apply sngTrace_not_empty. 
Qed.

(* Maybe write Prop definition of what it means to be a prefix of a list *)
Fixpoint prefixes {T: Type} (s: list T): list (list T) :=
  match s with
  | nil => [nil]
  | a :: s' =>
    let ps' := prefixes s' in
    nil :: map (fun p => a :: p) ps'
  end.

Definition prefix_closed {T: Type} (tSet: set (list T)): Prop :=
  forall (tList: list T),
    In tList tSet ->
    forall (prefT: list T),
      In prefT (prefixes tList) ->
        In prefT tSet.

Check prefix_closed.

Theorem or_false: forall (P: Prop), P \/ False <-> P.
Proof.
  intros P.
  split.
  - intros. inversion H.
    + apply H0.
    + inversion H0.
  - intros HP. left. apply HP. 
Qed.

Theorem traces_prefix_closed: forall (p: Proc),
  prefix_closed (traces p).
Proof.
  intros p. induction p.
  - simpl. unfold prefix_closed.
    intros. simpl in H. rewrite -> or_false in H.
    subst tList. simpl in H0. rewrite -> or_false in H0.
    subst prefT. unfold emptyTrace. simpl. left. reflexivity.
  - simpl. unfold prefix_closed.
    intros. simpl in H. rewrite -> or_false in H.
    subst tList. simpl in H0. rewrite -> or_false in H0.
    subst prefT. unfold emptyTrace. simpl. left. reflexivity.
  - simpl. unfold prefix_closed. intros.
    unfold prefix_closed in IHp. apply set_union_intro.
    destruct tList.
    + simpl in H0. rewrite or_false in H0. left. rewrite <- H0.
      unfold emptyTrace. simpl. left. reflexivity.
    + simpl in H0.
Abort.
  
  


