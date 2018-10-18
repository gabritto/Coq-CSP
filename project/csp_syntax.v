Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.OrderedType.
Module CSP_Syntax.

Set Implicit Arguments.
Import ListNotations.
Open Scope string_scope.

Definition Event: Type := string.

Theorem Event_eq_dec: forall (x y: Event), {x = y} + {x <> y}.
Proof.
  apply string_dec.
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

Module CSP_Syntax_Notations.
(* CSP *)
Notation "a ~> p" := (ProcPref a p)
  (at level 60, right associativity).
                      
Notation "p [-] q" := (ProcExtChoice p q)
  (at level 60, right associativity).
                     
Notation "p << b >> q" := (ProcCond b p q)
  (at level 60, right associativity).

(* TODO: find notation for this
Notation "'var' p" := (ProcName p)
  (at level 60, no associativity).
*)

Notation "p ::= q" := (Def p q)
  (at level 99, no associativity).

Notation "'channel' a , 'definitions' ds" := (SpecDef a ds)
  (at level 99, no associativity).
  
Check ProcName "P".

Example procTest := channel ["a"; "b"],
  definitions
    ["P" ::= ("a" ~> Stop) [-] ("b" ~> Stop);
     "Q" ::= (ProcName "R" << true >> Skip) ].

Check procTest.
Compute procTest.

End CSP_Syntax_Notations.

Import CSP_Syntax_Notations.

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
  | ProcPref e proc' => e :: extract_events proc'
  | _ => []
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
    distinct string_dec alphabet /\
    incl (events_used procDefs) alphabet
  end.

(* Dealing with recursion *)

Fixpoint find_process (p: string) (procDefs: list ProcDef): Proc :=
  match procDefs with
  | [] => Stop
  | (Def q qbody) :: procDefs' =>
     if string_dec q p then qbody else find_process p procDefs' 
  end.

(* Graph auxiliar definition *)
Definition proc_dependency (spec: Spec) (p: string): list string :=
  match spec with (SpecDef a ps) =>
    let p_body := find_process p ps in
    extract_names p_body
  end.

(* Map *)
Module StringOT <: OrderedType.
  Definition t := string.
  
  Definition eq := @eq t.
  
  Fixpoint lt (s1: string) (s2: string): Prop :=
    match s1, s2 with
    | EmptyString, EmptyString => False
    | EmptyString, _ => True
    | _, EmptyString => False
    | (String ch1 s1'), (String ch2 s2') =>
      let c1 := nat_of_ascii ch1 in
      let c2 := nat_of_ascii ch2 in
        c1 < c2 /\ lt s1' s2'
    end.
  
  Definition eq_refl := @refl_equal t.
  
  Definition eq_sym := @sym_eq t.
  
  Definition eq_trans := @trans_eq t.
  
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x. induction x.
    - intros y z. intros H. intros Hyz.
      destruct y.
      + simpl in H. exfalso. apply H.
      + unfold lt. destruct z.
        * simpl in Hyz. apply Hyz.
        * apply I.
    - intros y z. intros H. intros Hyz. simpl.
      destruct z.
      + simpl in Hyz. destruct y.
        * simpl in Hyz. apply Hyz.
        * simpl in Hyz. apply Hyz.
      + destruct y.
        * simpl in H. exfalso. apply H.
        * simpl in H. simpl in Hyz. split.
          {
            apply proj1 in H. apply proj1 in Hyz.
            Search (_ < _ -> _ < _ -> _ < _).
            apply PeanoNat.Nat.lt_trans with (m := nat_of_ascii a1).
            - apply H.
            - apply Hyz.
          }
          {
            apply proj2 in H. apply proj2 in Hyz. apply IHx with (y := y).
            - apply H.
            - apply Hyz.
          }
  Qed.
  
  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. (* TODO *) Admitted.
  
  Check Compare.
  
  Check Compare lt eq.
   
  Definition compare: forall x y : string, Compare lt eq x y.
  Proof.
    intros x. induction x.
    - intros y. destruct y.
      + apply EQ. simpl. reflexivity.
      + apply LT. simpl. apply I.
    - intros y. destruct y.
      + apply GT. simpl. apply I.
      +
  Admitted.
  
  Definition eq_dec := string_dec.
  
End StringOT.


(* Graph cycle *)
(*TODO: DFS solution*)

(* Define non-recursive spec prop *)


(* Traces *)
(* TODO: define traces function up to a maximum size *)
Definition Trace: Type := list Event.

Theorem Trace_eq_dec: forall (x y: Trace), {x = y} + {x <> y}.
Proof.
  Search "list_eq_dec". apply list_eq_dec. apply Event_eq_dec.
Defined.

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

Definition get_alphabet (s: Spec): Alphabet :=
  match s with (SpecDef a _) => a end.  

Definition get_proc_defs (spec: Spec): list ProcDef :=
  match spec with (SpecDef _ procDefs) => procDefs end.

(* Functional definition of the set of traces of a process*)

Definition TracesMap := list (string * set Trace).

Fixpoint get_trace (procName: string) (tracesMap: TracesMap): set Trace :=
  match tracesMap with
  | [] => []
  | (name, traces) :: tracesMap' =>
    if string_dec procName name then traces else get_trace procName tracesMap'
  end.

Fixpoint build_traces (traces: TracesMap) (p: Proc): set Trace :=
  match p with
  | Stop => [[]]
  | Skip => [[]]
  | ProcPref e q =>
    let qTraces := build_traces traces q in
    let qWithA := setMap (fun trace => e :: trace) qTraces in
      setUnion [[]] qWithA
  | ProcExtChoice p q => setUnion (build_traces traces p) (build_traces traces q)
  | ProcCond b p q => if b then (build_traces traces p) else (build_traces traces q)
  | ProcName name => get_trace name traces
  end.

Check List.length.

Fixpoint bound_spec_traces (n: nat) (spec: Spec): TracesMap :=
  let defs := get_proc_defs spec in
  let procNames := process_names_defined defs in
  let size := List.length defs in
  match n with
  | O => map (fun name => (name, [[]])) procNames
  | S n' =>
    let tracesMap := bound_spec_traces n' spec in
    map
    (fun def =>
      match def with (Def name proc) =>
        (name, build_traces tracesMap proc)
      end)
    defs
  end.

(* Tests *)

Print procTest.

Compute bound_spec_traces 0 procTest.
Compute bound_spec_traces 1 procTest.
Compute bound_spec_traces 2 procTest.

Example around := channel ["up"; "down"],
  definitions
  ["around" ::=
    ("up" ~> ProcName "around") [-]
    ("down" ~> ProcName "around")].
Print well_formed_spec.    
Compute well_formed_spec around.

Example aroundDefs := get_proc_defs around.
Compute process_names_defined aroundDefs.
Compute distinct string_dec (process_names_defined aroundDefs).

Compute bound_spec_traces 0 around.
Compute bound_spec_traces 1 around.
Compute bound_spec_traces 2 around.
Compute bound_spec_traces 3 around.

Definition DefInSpec (def: ProcDef) (s: Spec): Prop :=
  let defs := get_proc_defs s in
  In def defs.

Definition EventInSpec (e: Event) (s: Spec): Prop :=
  let alpha := get_alphabet s in
  In e alpha.

Inductive TraceType: Type :=
  | EmptyTrace
  | ConcatTrace: Event -> TraceType -> TraceType. 

(* Inductive traces *)
Inductive IsProcTrace: Proc -> Spec -> TraceType -> Prop :=
  | AllEmptyTrace: forall (p: Proc) (s: Spec),
      IsProcTrace p s EmptyTrace
  | ExtChoiceTrace: forall (p q: Proc) (s: Spec) (t: TraceType),
      IsProcTrace p s t \/ IsProcTrace q s t ->
      IsProcTrace (ProcExtChoice p q) s t
  | PrefTrace: forall (p: Proc) (s: Spec) (t: TraceType) (e: Event),
      IsProcTrace p s t -> EventInSpec e s ->
      IsProcTrace (ProcPref e p) s (ConcatTrace e t)
  | NameTrace: forall (name: string) (p: Proc) (s: Spec) (t: TraceType),
      IsProcTrace p s t -> DefInSpec (Def name p) s ->
      IsProcTrace (ProcName name) s t
  | PrefCondFalse: forall (p q: Proc) (s: Spec) (t: TraceType) (b: bool),
      b = false ->
      IsProcTrace p s t ->
      IsProcTrace (ProcCond b p q) s t
  | ProcCondTrue: forall (p q: Proc) (s: Spec) (t: TraceType) (b: bool),
      b = true ->
      IsProcTrace q s t ->
      IsProcTrace (ProcCond b p q) s t.


(*TODO: More practical definition of NameTrace *)
Example traceAround:
  IsProcTrace
    (("up" ~> ProcName "around") [-] ("down" ~> ProcName "around"))
    around
    (ConcatTrace "up" (ConcatTrace "down" EmptyTrace)).
Proof.
  apply ExtChoiceTrace.
  left. apply PrefTrace.
  {
    try apply NameTrace. unfold around.
    apply NameTrace with (p := ("up" ~> ProcName "around") [-] ("down" ~> ProcName "around")).
    - apply ExtChoiceTrace. right. apply PrefTrace.
      + apply AllEmptyTrace.
      + unfold EventInSpec. simpl. right. left. reflexivity.
    - simpl. unfold DefInSpec. simpl. left. reflexivity.
  }
  {
    - unfold EventInSpec. simpl. left. reflexivity. 
  }
Qed.

(*
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
*)



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

(*
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
*)
  


