Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import ListNotations.
Module CSP_Syntax.

(* Define Event type *)
Definition Event: Type := nat.

Theorem Event_eq_dec: forall (x y: Event), {x = y} + {x <> y}.
Proof.
Admitted.

(* A set of events should be in context? *)

Inductive Proc: Type :=
  | Stop: Proc
  | ProcPref: Event -> Proc -> Proc
  | ProcExtChoice: Proc -> Proc -> Proc
  | ProcCond: bool -> Proc -> Proc -> Proc
  | ProcRec: Proc -> Proc. 
  
Notation "a --> p" := (ProcPref a p)
  (at level 60, right associativity).
                      
Notation "p [] q" := (ProcExtChoice p q)
  (at level 60, right associativity).
                     
Notation "'if' b 'then' p 'else' q" := (ProcCond b p q)
  (at level 60, right associativity).

Definition Trace: Type := list Event.

Theorem Trace_eq_dec: forall (x y: Trace), {x = y} + {x <> y}.
Proof.
(* Utilizar prova de que se há uma igualdade para os elementos da lista, então pode-se
  definir uma igualdade para a lista
*)
Admitted.

Definition emptyTrace: Trace := nil.

Check set_add.

Definition setAdd := set_add Trace_eq_dec.

Check setAdd.

Definition sngTrace (e: Trace) := setAdd e (empty_set _).

Definition setUnion := set_union Trace_eq_dec.

Definition sngEmptyTrace := sngTrace emptyTrace.

Definition setMap := @set_map Trace Trace Trace_eq_dec.

Fixpoint traces (p: Proc): set Trace :=
  match p with
  | Stop => [emptyTrace]
  | ProcPref e q =>
    let qTraces := traces(q) in
    let qWithA := setMap (fun trace => e :: trace) qTraces in
      setUnion [emptyTrace] qWithA
  | ProcExtChoice p q => setUnion (traces p) (traces q)
  | ProcCond b p q => if b then (traces p) else (traces q)
  | _ => [emptyTrace]
  end.    

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

Theorem traces_non_empty: forall (p: Proc),
  traces p <> empty_set Trace.
Proof.
  intros p. induction p.
  - simpl. unfold empty_set. intros H. inversion H.
  - simpl. unfold setUnion. simpl. Search (_ <> empty_set).
    apply set_union_not_empty. apply sngTrace_not_empty.
  - simpl. apply set_union_not_empty. apply IHp1.
  - simpl. destruct b.
    + apply IHp1.
    + apply IHp2.
  - simpl. apply sngTrace_not_empty. 
Qed.

Fixpoint prefixes {T: Type} (s: list T): list (list T) :=
  match s with
  | nil => [nil]
  | a :: s' =>
    let ps' := prefixes s' in
    nil :: map (fun p => a :: p) ps'
  end.

(*
Definir prop prefixClosed e provar teorema abaixo.

Theorem traces_prefix_closed: forall (p: Proc),
  prefixClosed (traces p).
*)
  
  


