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
        c1 < c2 \/ (c1 = c2 /\ lt s1' s2')
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
        * simpl in H. simpl in Hyz.
          destruct H as [H | H].
          {
            destruct Hyz as [Hyz | Hyz].
            - left. apply PeanoNat.Nat.lt_trans with (m := nat_of_ascii a1).
              apply H. apply Hyz.
            - destruct Hyz as [H' Hyz].
              left. rewrite -> H' in H. apply H.
          }
          {
            destruct Hyz as [Hyz | Hyz].
            - apply proj1 in H.
              rewrite <- H in Hyz. left. apply Hyz.
            - right. destruct H as [H1 H2].
              destruct Hyz as [H3 H4].
              rewrite -> H3 in H1. split.
              + apply H1.
              + apply IHx with (y := y).
                apply H2. apply H4.
          }
  Qed.
  
  Theorem lt_not_eq : forall x y : string, lt x y -> ~ eq x y.
  Proof.
    intros x y. intros ltxy. unfold not. intros eqxy.
    unfold eq in eqxy. destruct x.
    - simpl in ltxy. destruct y.
      + apply ltxy.
      + inversion eqxy.
    - destruct y.
      + simpl in ltxy. apply ltxy.
      + simpl in eqxy.
  Admitted.
  
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

(* Traces *)
Definition Trace: Type := list Event.

Theorem Trace_eq_dec: forall (x y: Trace), {x = y} + {x <> y}.
Proof.
  Search "list_eq_dec". apply list_eq_dec. apply Event_eq_dec.
Defined.

(* Trace and set of Traces definitions *)

Definition emptyTrace: Trace := nil.

Definition get_alphabet (s: Spec): Alphabet :=
  match s with (SpecDef a _) => a end.  

Definition get_proc_defs (spec: Spec): list ProcDef :=
  match spec with (SpecDef _ procDefs) => procDefs end.

(* Functional definition of the set of traces of a process*)

Definition TracesMap := list (string * list Trace).

(* auxiliar definitions *)
Theorem or_false: forall (P: Prop), P \/ False <-> P.
Proof.
  intros P.
  split.
  - intros. inversion H.
    + apply H0.
    + inversion H0.
  - intros HP. left. apply HP. 
Qed.

Fixpoint find_key {A B: Type}
  (A_eq_dec: forall x y : A, {x = y} + {x <> y})
  (l: list (A*B)) (key: A): option B :=
  match l with
  | [] => None
  | (a, b) :: l' =>
    if A_eq_dec a key then Some b else find_key A_eq_dec l' key
  end.  
    
Definition get_trace (procName: string)
  (tracesMap: TracesMap): list Trace :=
  let optTraces := find_key string_dec tracesMap procName in
  match optTraces with
  | None => []
  | Some traces => traces
  end.

Fixpoint build_traces (traces: TracesMap) (p: Proc): list Trace :=
  match p with
  | Stop => [[]]
  | Skip => [[]]
  | ProcPref e q =>
    let qTraces := build_traces traces q in
    let qWithA := map (fun trace => e :: trace) qTraces in
      [[]] ++ qWithA
  | ProcExtChoice p q => (build_traces traces p) ++ (build_traces traces q)
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

Print Trace.

(* Inductive traces *)
Inductive IsProcTrace: Proc -> Spec -> Trace -> Prop :=
  | AllEmptyTrace: forall (p: Proc) (s: Spec),
      IsProcTrace p s []
  | ExtChoiceTrace: forall (p q: Proc) (s: Spec) (t: Trace),
      IsProcTrace p s t \/ IsProcTrace q s t ->
      IsProcTrace (ProcExtChoice p q) s t
  | PrefTrace: forall (p: Proc) (s: Spec) (t: Trace) (e: Event),
      IsProcTrace p s t -> EventInSpec e s ->
      IsProcTrace (ProcPref e p) s (e :: t)
  | NameTrace: forall (name: string) (p: Proc) (s: Spec) (t: Trace),
      IsProcTrace p s t -> DefInSpec (Def name p) s ->
      IsProcTrace (ProcName name) s t
  | CondFalse: forall (p q: Proc) (s: Spec) (t: Trace) (b: bool),
      b = false ->
      IsProcTrace q s t ->
      IsProcTrace (ProcCond b p q) s t
  | CondTrue: forall (p q: Proc) (s: Spec) (t: Trace) (b: bool),
      b = true ->
      IsProcTrace p s t ->
      IsProcTrace (ProcCond b p q) s t.


(*TODO: More practical definition of NameTrace? *)
Example traceAround:
  IsProcTrace
    (("up" ~> ProcName "around") [-] ("down" ~> ProcName "around"))
    around
    (["up" ; "down"]).
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

Lemma def_in_get_proc_def: forall (s: Spec) (procName: string) (procBody: Proc),
  DefInSpec (Def procName procBody) s -> In procName (process_names_defined (get_proc_defs s)).
Proof.
  intros. simpl in H. unfold DefInSpec in H.
  simpl. unfold process_names_defined. Print in_map.
  apply in_map with (f:= (fun d : ProcDef => match d with | s0 ::= _ => s0 end)) in H. apply H.
Qed.

Check string_dec.

Print get_trace.

Lemma get_empty_trace_well_formed_spec: forall (s: Spec) (procName: string) (procBody: Proc),
  well_formed_spec s ->
  DefInSpec (Def procName procBody) s ->
  (* In (procName, traceSet) traceMap -> *) get_trace procName ((map (fun name : string => (name, [[]]))
          (process_names_defined (get_proc_defs s)))) = [[]].
Proof.
  intros. simpl in H. unfold well_formed_spec in H.
  unfold DefInSpec in H0. unfold get_proc_defs in H0.
  destruct s. apply proj1 in H. simpl in H.
  simpl.
  induction l.
  - inversion H0.
  - simpl. destruct a0. destruct H0.
    + subst. inversion H0. destruct (string_dec procName procName).
      * simpl. unfold get_trace. simpl. unfold find_key. simpl.
        {
          destruct (string_dec procName procName).
          - reflexivity.
          - unfold not in n. exfalso. apply n. apply e.
        }
      * unfold not in n. exfalso. apply n. reflexivity.
    + simpl. simpl in H. apply proj2 in H. destruct (string_dec procName s).
      * simpl. unfold get_trace. simpl. unfold find_key. simpl.
        {
          destruct (string_dec s procName).
          - reflexivity.
          - unfold not in n. exfalso. apply n. symmetry. apply e.
        }
      * unfold get_trace. simpl. unfold find_key.
        {
          destruct (string_dec s procName).
          - reflexivity.
          - unfold not in n. unfold not in n0. simpl.
            apply IHl. apply H. apply H0.
        }
Qed.


Print distinct.
Print bound_spec_traces.

Definition distinct_proc_names (tracesMap: TracesMap) :=
  distinct
    string_dec
    (map
      (fun nameTrace => match nameTrace with (name, _) => name end)
      tracesMap).

Print distinct.

Print option.

Print prod.

Lemma distinct_traces_map: forall (s: Spec) (n: nat),
  well_formed_spec s -> distinct_proc_names (bound_spec_traces n s).
Proof.
  
Admitted.

Lemma get_trace_proc_name: forall (procName: string)
  (traceSet: list Trace) (tracesMap: TracesMap),
  distinct_proc_names tracesMap ->
  In (procName, traceSet) tracesMap ->
  get_trace procName tracesMap = traceSet.
Proof.
  intros. induction tracesMap.
  - inversion H0.
  - unfold get_trace. simpl. destruct a.
    simpl in H0. destruct H0.
    + inversion H0. clear H0.
      destruct (string_dec procName procName).
      * reflexivity.
      * subst.
        exfalso. unfold not in n. apply n. reflexivity.
    + unfold distinct_proc_names in H.
      destruct (string_dec s procName).
      * simpl in H.
        apply in_map with (f := (fun nameTrace : string * list Trace =>
          let (name, _) := nameTrace in name)) in H0. 
        subst. apply proj1 in H. unfold not in H. exfalso.
        apply H. apply H0.
      * simpl in H. apply proj2 in H.
        unfold distinct_proc_names in IHtracesMap.
        apply IHtracesMap in H.
        2: apply H0.
        unfold get_trace in H.
        apply H.
Qed.

Lemma get_trace_then_in_trace: forall (procName: string) 
  (traceSet: list Trace) (tracesMap: TracesMap),
  get_trace procName tracesMap = traceSet ->
  traceSet <> [] ->
  In (procName, traceSet) tracesMap.
Proof.
  intros. generalize dependent traceSet. induction tracesMap.
  - intros. unfold get_trace in H. simpl in H. unfold not in H0.
    exfalso. apply H0. symmetry. apply H.
  - intros. simpl. unfold get_trace in H. simpl in H.
    destruct a. destruct (string_dec s procName).
    + left. subst. reflexivity.
    + right. apply IHtracesMap.
      * unfold get_trace. apply H.
      * apply H0.
Qed.

Lemma not_empty_list_then_in:
  forall {A: Type} (l: list A),
  l <> [] -> exists a, In a l.
Proof.
  intros. destruct l.
  - unfold not in H. exfalso. apply H. reflexivity.
  - exists a. simpl. left. reflexivity.
Qed.

Theorem build_traces_correctness:
  forall (proc: Proc) (tracesMap: TracesMap) (spec: Spec) (trace: Trace) (traceSet: list Trace),
  well_formed_spec spec ->
  (forall (event: Event), In event (extract_events proc) -> EventInSpec event spec) ->
  traceSet = build_traces tracesMap proc ->
  In trace traceSet ->
  IsProcTrace proc spec trace.
Proof.
  Print well_formed_spec.
  induction proc.
  - intros. simpl in H1. subst. unfold In in H2.
    rewrite or_false in H2.
    subst. apply AllEmptyTrace.
  - intros. simpl in H1. subst. unfold In in H2.
    rewrite or_false in H2.
    subst. apply AllEmptyTrace.
  - intros. simpl in H1.
    destruct trace.
    + apply AllEmptyTrace.
    (* + apply PrefTrace. *)
    Print PrefTrace.
    + destruct (string_dec e0 e).
      * subst.
        intros.
        apply PrefTrace.
        {
          apply IHproc with (tracesMap := tracesMap)
            (trace := trace)
            (traceSet := (build_traces tracesMap proc)).
          - apply H.
          - simpl in H0.
            intros.
            apply H0.
            right.
            apply H1.
          - reflexivity.
          - simpl in H2.
            inversion H2.
            + inversion H1.
            + apply in_map_iff in H1.
              destruct H1.
              destruct H1.
              inversion H1.
              clear H1.
              subst. apply H3. 
        }
        {
          apply H0.
          simpl. left. reflexivity.
        }
        * unfold not in n.
          simpl.
          subst.
          simpl in H2.
          destruct H2.
          inversion H1.
          apply in_map_iff in H1.
          destruct H1. apply proj1 in H1.
          inversion H1. exfalso. apply n. symmetry. apply H3.
  - intros. apply ExtChoiceTrace.
    + simpl in H1. subst.
      apply in_app_or in H2.
      destruct H2.
      * left.
        apply IHproc1 with (tracesMap := tracesMap) (traceSet := (build_traces tracesMap proc1)).
        {
          apply H.
        }
        {
          simpl in H0.
          intros.
          apply H0.
          apply in_or_app.
          left. apply H2.
        }
        {
          reflexivity.
        }
        {
          apply H1.
        }
      * right.
        apply IHproc2 with (tracesMap := tracesMap) (traceSet := (build_traces tracesMap proc2)).
        {
          apply H.
        }
        {
          simpl in H0.
          intros.
          apply H0.
          apply in_or_app.
          right. apply H2.
        }
        {
          reflexivity.
        }
        {
          apply H1.
        }
  - intros. destruct b.
    + apply CondTrue.
      * reflexivity.
      * apply IHproc1 with (tracesMap := tracesMap)
          (traceSet := build_traces tracesMap proc1).
        {
          apply H.
        }
        {
          simpl in H0. intros.
          apply H0. apply in_or_app.
          left. apply H3.
        }
        {
          reflexivity.
        }
        { 
          simpl in H1. subst. apply H2.
        }
    + simpl. apply CondFalse.
      * reflexivity.
      * apply IHproc2 with (tracesMap := tracesMap)
          (traceSet := build_traces tracesMap proc2).
        {
          apply H.
        }
        {
          simpl in H0. intros.
          apply H0. apply in_or_app.
          right. apply H3.
        }
        {
          reflexivity.
        }
        { 
          simpl in H1. subst. apply H2.
        }
  - intros.
    simpl in H1.
Abort.

Print build_traces.

(*
Issues:
  - Induction needs a proof of correctness for a "procBody" that is not necessarily associated with
    a procName in the spec, such "procBody" could be a subterm of a larger process definition.
  - To state correctness of build_traces, as shown in above build_traces_correctness proof attempt,
    for cases where the process has the format e -> Proc (prefix operator), we need to know that the
    event e is defined in the spec. But in order to know that, we would need to know that such process
    appears as a subterm of another process body actually defined in the spec.
*)

(* Possibilities:
  - Assume 2 cases: proc = ProcName s
    and proc <> ProcName s
    + DefInSpec, correctness of proof.
    + 
*)

Theorem bound_spec_traces_correctness: forall (s: Spec) (n: nat)
  (procName: string) (procBody: Proc) (trace: Trace)
  (traceSet: list Trace),
  well_formed_spec s ->
  (
    (DefInSpec (Def procName procBody) s ->
    traceSet = get_trace procName (bound_spec_traces n s) ->
    In trace traceSet -> IsProcTrace procBody s trace) /\
    ((forall (event: Event), In event (extract_events procBody) -> EventInSpec event s) ->
    traceSet = build_traces (bound_spec_traces n s) procBody ->
    In trace traceSet -> IsProcTrace procBody s trace)
  ).
Proof.
  Print bound_spec_traces.
  intro s. induction n.
  - induction procBody.
        
    {
      intros.    
      simpl in H0.
      simpl in H1. assert (H0' := H0). apply def_in_get_proc_def in H0.
      Print get_trace. Check (process_names_defined (get_proc_defs s)).
      Check in_map.
      Print nil.
      apply in_map with (f := (fun name : string => (name, [@nil Event]))) (l := (process_names_defined (get_proc_defs s))) in H0.
      apply get_empty_trace_well_formed_spec with (procName := procName) (procBody := procBody) in H.
      rewrite H in H1. subst. inversion H2.
      + rewrite <- H1. apply AllEmptyTrace.
      + inversion H1.
      + simpl. apply H0'.
    }
    { generalize dependent trace.
      generalize dependent traceSet.
      induction procBody.
      - intros.
        simpl in H1. subst. simpl in H2. rewrite or_false in H2.
        subst. apply AllEmptyTrace.
      - intros. simpl in H1. subst. simpl in H2. rewrite or_false in H2.
        subst. apply AllEmptyTrace.
      - intros. simpl in H1. subst. simpl in H2.
        destruct H2.
        + subst. apply AllEmptyTrace.
        + apply in_map_iff in H1.
          destruct H1. destruct H1.
          subst.
          simpl in IHprocBody.
          simpl in H0.
          apply PrefTrace.
          * apply IHprocBody with (traceSet := (build_traces (map (fun name : string => (name, [[]])) (process_names_defined (get_proc_defs s)))
          procBody)).
            {
              intros.
              apply H0.
              right. apply H1.
            }
            {
              reflexivity.
            }
            {
              apply H2.
            }
          * apply H0.
            left. reflexivity.
      - intros. simpl in H1. subst. simpl in H2.
        apply in_app_or in H2.
        destruct H2.
        + apply ExtChoiceTrace. left.
          apply IHprocBody1 with (traceSet := build_traces (bound_spec_traces 0 s) procBody1).
          * intros. apply H0. simpl. apply in_or_app. left. apply H2.
          * simpl. reflexivity.
          * simpl. apply H1.
        + apply ExtChoiceTrace. right.
          apply IHprocBody2 with (traceSet := build_traces (bound_spec_traces 0 s) procBody2).
          * intros. apply H0. simpl. apply in_or_app. right. apply H2.
          * simpl. reflexivity.
          * simpl. apply H1.
      - intros. destruct b.
        + apply CondTrue.
          * reflexivity.
          * apply IHprocBody1 with (traceSet := build_traces (bound_spec_traces 0 s) procBody1).
              { intros. apply H0. simpl. apply in_or_app. left. apply H3. }
              { simpl. reflexivity. }
              { simpl. subst. apply H2. }
        + apply CondFalse.
          * reflexivity.
          * apply IHprocBody2 with (traceSet := build_traces (bound_spec_traces 0 s) procBody2).
              { intros. apply H0. simpl. apply in_or_app. right. apply H3. }
              { simpl. reflexivity. }
              { simpl. subst. apply H2. }
      - intros. simpl in H1. subst.
        
    }
  - assert (Hwf := H).
    induction procBody.
    { (* Begin Stop *)
      intros.
      unfold DefInSpec in H0.
      assert (Hdef := H0).
      apply in_map with (f := (fun def : ProcDef =>
       match def with
       | name ::= proc =>
           (name, build_traces (bound_spec_traces n s) proc)
       end)) in H0. simpl in H0.
      simpl in H1.
      apply distinct_traces_map with (n := S n) in H.
      apply get_trace_proc_name with (procName := procName)
      (traceSet := traceSet) in H.
      subst.
      simpl in H0.
      apply get_trace_proc_name in H0.
      rewrite H0 in H1.
      rewrite -> H1 in H2.
      simpl in H2. rewrite or_false in H2.
      subst.
      - apply AllEmptyTrace.
      - assert ((bound_spec_traces (S n) s) = (map
         (fun def : ProcDef =>
          match def with
          | name ::= proc =>
              (name, build_traces (bound_spec_traces n s) proc)
          end) (get_proc_defs s))).
        {
          simpl. reflexivity.
        }
        rewrite <- H. apply distinct_traces_map.
        apply Hwf.
      - assert ((bound_spec_traces (S n) s) = (map
         (fun def : ProcDef =>
          match def with
          | name ::= proc =>
              (name, build_traces (bound_spec_traces n s) proc)
          end) (get_proc_defs s))).
        {
          simpl. reflexivity.
        }
        rewrite <- H3 in H0.
        apply get_trace_then_in_trace.
        + symmetry. apply H1.
        + apply get_trace_proc_name with (procName := procName)(traceSet := [[]]) in H.
          * subst. rewrite <- H3. unfold not. intros.
            rewrite -> H in H1. inversion H1.
          * apply H0.
    } (* End Stop *)
    { (* Begin Skip *)
      intros.
      unfold DefInSpec in H0.
      assert (Hdef := H0).
      apply in_map with (f := (fun def : ProcDef =>
       match def with
       | name ::= proc =>
           (name, build_traces (bound_spec_traces n s) proc)
       end)) in H0. simpl in H0.
      simpl in H1.
      apply distinct_traces_map with (n := S n) in H.
      apply get_trace_proc_name with (procName := procName)
      (traceSet := traceSet) in H.
      subst.
      simpl in H0.
      apply get_trace_proc_name in H0.
      rewrite H0 in H1.
      rewrite -> H1 in H2.
      simpl in H2. rewrite or_false in H2.
      subst.
      - apply AllEmptyTrace.
      - assert ((bound_spec_traces (S n) s) = (map
         (fun def : ProcDef =>
          match def with
          | name ::= proc =>
              (name, build_traces (bound_spec_traces n s) proc)
          end) (get_proc_defs s))).
        {
          simpl. reflexivity.
        }
        rewrite <- H. apply distinct_traces_map.
        apply Hwf.
      - assert ((bound_spec_traces (S n) s) = (map
         (fun def : ProcDef =>
          match def with
          | name ::= proc =>
              (name, build_traces (bound_spec_traces n s) proc)
          end) (get_proc_defs s))).
        {
          simpl. reflexivity.
        }
        rewrite <- H3 in H0.
        apply get_trace_then_in_trace.
        + symmetry. apply H1.
        + apply get_trace_proc_name with (procName := procName)(traceSet := [[]]) in H.
          * subst. rewrite <- H3. unfold not. intros.
            rewrite -> H in H1. inversion H1.
          * apply H0.
    } (* End Skip *) 
    { (* Begin Prefix *)
      intros.
      assert (Hdef := H0).
      unfold DefInSpec in H0.
      apply in_map with (f := (fun def : ProcDef =>
       match def with
       | name ::= proc =>
           (name, build_traces (bound_spec_traces n s) proc)
       end)) in H0. simpl in H0.
      subst. simpl in H2.
      apply distinct_traces_map with (n := S n) in H.
      apply get_trace_proc_name with (procName := procName)
        (traceSet := [] :: map (fun trace : list Event => e :: trace) (build_traces (bound_spec_traces n s) procBody))
        in H.
      2: apply H0.
      simpl in H.
      rewrite -> H in H2.
      simpl in H2.
      destruct H2.
      - subst. apply AllEmptyTrace.
      - apply in_map_iff in H1. destruct H1.
        destruct H1.
        subst.
        apply PrefTrace.
        + simpl in IHprocBody.
          apply IHprocBody with (procName := p.
    } (* End Prefix *)
Admitted.

Lemma well_formed_not_empty_trace:
  forall (spec: Spec) (proc: Proc) (tracesMap: TracesMap),
  well_formed_spec spec ->
  (* proc != ProcName *)
  (build_traces tracesMap proc) <> [].
Proof.
  intro. induction proc.
  - intros. simpl. unfold not. intros.
    inversion H0.
  - intros. simpl. unfold not. intros.
    inversion H0.
  - intros. simpl. unfold not. intros.
    unfold setUnion in H0. unfold set_union in H0.
    destruct (setMap (fun trace : Trace => e :: trace)
          (build_traces tracesMap proc)).
    + inversion H0.
    + simpl in H0. apply set_add_not_empty in H0. apply H0.
  - intros. simpl. unfold setUnion. apply set_union_not_empty.
    apply IHproc1 with (tracesMap := tracesMap) in H.
    apply H.
  - intros. simpl. destruct b.
    + apply IHproc1 with (tracesMap := tracesMap) in H.
      apply H.
    + apply IHproc2 with (tracesMap := tracesMap) in H.
      apply H.
  - intros.
    simpl.
    unfold well_formed_spec in H.
    destruct spec.
Qed.

(*TODO: change correctness to include both functions (since they call each other *)


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
  


