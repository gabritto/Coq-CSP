Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Module CSP_Syntax.

Set Implicit Arguments.
Import ListNotations.
Open Scope string_scope.

Inductive Event: Type :=
  | Name: string -> Event
  | Tick: Event.

Theorem Event_dec: forall (x y: Event), {x = y} + {x <> y}.
Proof.
  destruct x.
  {
    destruct y.
    {
      destruct (string_dec s s0).
      {
        subst. left. reflexivity.
      }
      {
        right.
        unfold not.
        intros. inversion H. apply n. apply H1.
      }
    }
    {
      right.
      unfold not.
      intros.
      inversion H.
    }
  }
  {
    destruct y.
    {
      right. unfold not. intros. inversion H.
    }
    {
      left. reflexivity.
    }
  }
Defined.

Definition Alphabet: Type := list Event.

Inductive Proc: Type :=
  | Stop: Proc
  | Skip: Proc
  | ProcPref: Event -> Proc -> Proc
  | ProcExtChoice: Proc -> Proc -> Proc
  | ProcCond: bool -> Proc -> Proc -> Proc
  | ProcName: string -> Proc. 
  
Inductive ProcDef: Type :=
  | Def: string -> Proc -> ProcDef.

Inductive Spec: Type :=
  | SpecDef: Alphabet -> list ProcDef -> Spec. 

Definition build_events :=
  map (fun str => Name str).

Module CSP_Syntax_Notations.
(* CSP *)
Notation "a ~> p" := (ProcPref a p)
  (at level 60, right associativity).
                      
Notation "p [-] q" := (ProcExtChoice p q)
  (at level 60, right associativity).
                     
Notation "p << b >> q" := (ProcCond b p q)
  (at level 60, right associativity).

Notation "'p'' p" := (ProcName p)
  (at level 60, no associativity).

Notation "'e'' e" := (Name e)
  (at level 60, no associativity).

Notation "p ::= q" := (Def p q)
  (at level 99, no associativity).

Notation "'channel' a , 'definitions' ds" := (SpecDef (build_events a) ds)
  (at level 99, no associativity).

End CSP_Syntax_Notations.

Import CSP_Syntax_Notations.
  
Check p'"P".

Example procTest := channel ["a"; "b"],
  definitions
    ["P" ::= (e'"a" ~> Stop) [-] (e'"b" ~> Stop);
     "Q" ::= (ProcName "R" << true >> Skip) ].

Check procTest.
Compute procTest.

Fixpoint extract_names (proc: Proc): list string :=
  match proc with
  | Skip => []
  | Stop => []
  | ProcPref _ proc'  => extract_names proc'
  | ProcExtChoice p q => extract_names p ++ extract_names q
  | ProcCond _ p q => extract_names p ++ extract_names q
  | ProcName name => [name]
  end.

Fixpoint extract_events (proc: Proc): list Event :=
  match proc with
  | Stop => []
  | Skip => []
  | ProcExtChoice p q => (extract_events p) ++ (extract_events q)
  | ProcPref e p => e :: (extract_events p)
  | ProcCond b p q => (extract_events p) ++ (extract_events q)
  | ProcName s => []
  end.

Definition events_used (procs: list ProcDef): list Event :=
  flat_map
    (fun def =>
      match def with (Def _ proc) => extract_events proc end)
    procs.

Definition process_names_used (procs: list ProcDef): list string :=
  flat_map
    (fun def => 
      match def with (Def _ proc) => extract_names proc end)
    procs.

Definition process_names_defined (procs: list ProcDef): list string :=
  map (fun d => match d with (Def s _) => s end) procs.

Example procs := match procTest with (SpecDef a ps) => ps end.

Compute process_names_defined procs.
Compute process_names_used procs.

(*
  Definição proposicional de que uma lista de elementos
  de um tipo T possui elementos distintos, dada uma evidência
  de que a igualdade é decidível para o tipo T.
*)
Fixpoint distinct {T: Type}
  (T_eq_dec: forall (x y: T), {x = y} + {x <> y}) (l: list T): Prop :=
  match l with
  | [] => True
  | t :: l' => let t_unique := ~In t l' in
    t_unique /\ distinct T_eq_dec l'
  end.

Definition well_formed_spec (spec: Spec): Prop :=
  match spec with (SpecDef alphabet procDefs) =>
    distinct string_dec (process_names_defined procDefs) /\
    incl (process_names_used procDefs) (process_names_defined procDefs) /\
    distinct Event_dec alphabet /\
    incl (events_used procDefs) alphabet
  end.
  
End CSP_Syntax.