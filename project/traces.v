Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import csp_syntax.

Module Traces.

Import CSP_Syntax.
Import CSP_Syntax_Notations.
Set Implicit Arguments.
Import ListNotations.
Open Scope string_scope.

(* Traces *)
Definition Trace: Type := list Event.

Theorem Trace_eq_dec: forall (x y: Trace), {x = y} + {x <> y}.
Proof.
  Search "list_eq_dec". apply list_eq_dec. apply Event_dec.
Defined.

Definition get_spec_alphabet (s: Spec): Alphabet :=
  match s with (SpecDef a _) => a end.  

Definition get_proc_defs (spec: Spec): list ProcDef :=
  match spec with (SpecDef _ procDefs) => procDefs end.

(*
  Tipo que representa um mapa de nomes de processos (strings)
  para listas de traces.
*)
Definition TracesMap := list (string * list Trace).

Fixpoint find_key {A B: Type}
  (A_eq_dec: forall x y : A, {x = y} + {x <> y})
  (l: list (A*B)) (key: A): option B :=
  match l with
  | [] => None
  | (a, b) :: l' =>
    if A_eq_dec a key then Some b else find_key A_eq_dec l' key
  end.  

(*
  Dado um nome de processo e um mapeamento de nomes para
  listas de traces, retorna a lista de traces associada ao nome,
  ou a lista vazia se o nome não está presente no mapeamento.
*)
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
  | Skip => [[]; [Tick]]
  | ProcPref e q =>
    let qTraces := build_traces traces q in
    let qWithA := map (fun trace => e :: trace) qTraces in
      [[]] ++ qWithA
  | ProcExtChoice p q => (build_traces traces p) ++ (build_traces traces q)
  | ProcCond b p q => if b then (build_traces traces p) else (build_traces traces q)
  | ProcName name => get_trace name traces
  end.

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

Compute bound_spec_traces 0 procTest.
Compute bound_spec_traces 1 procTest.
Compute bound_spec_traces 2 procTest.

Example around := channel ["up"; "down"],
  definitions
  ["around" ::=
    (e'"up" ~> p'"around") [-]
    (e'"down" ~> p'"around")].
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
  let alpha := get_spec_alphabet s in
  In e alpha.

(*
  Definição indutiva da relação IsProcTrace, que afirma que
  que um trace pertence ao conjunto de traces de um processo,
  no contexto de uma especificação.
*)
Inductive IsProcTrace: Proc -> Spec -> Trace -> Prop :=
  | AllEmptyTrace: forall (p: Proc) (s: Spec),
      IsProcTrace p s []
  | SkipTrace: forall (s: Spec), IsProcTrace Skip s [Tick]
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

Example traceAround:
  IsProcTrace
    ((e'"up" ~> p'"around") [-] (e'"down" ~> p'"around"))
    around
    ([e'"up" ; e'"down"]).
Proof.
  apply ExtChoiceTrace.
  left. apply PrefTrace.
  {
    try apply NameTrace. unfold around.
    apply NameTrace with (p := (e'"up" ~> ProcName "around") [-] (e'"down" ~> ProcName "around")).
    - apply ExtChoiceTrace. right. apply PrefTrace.
      + apply AllEmptyTrace.
      + unfold EventInSpec. simpl. right. left. reflexivity.
    - simpl. unfold DefInSpec. simpl. left. reflexivity.
  }
  {
    - unfold EventInSpec. simpl. left. reflexivity. 
  }
Qed.

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
  Definição proposicional de que os nomes presentes num
  'tracesMap' são distintos.
*)
Definition distinct_proc_names (tracesMap: TracesMap) :=
  distinct
    string_dec
    (map
      (fun nameTrace => match nameTrace with (name, _) => name end)
      tracesMap).

(*
  Esse lema afirma que se 's' é uma especificação bem formada,
  então os nomes de processo presentes no tracesMap retornado
  por bound_spec_traces são distintos.
  A prova é feita por análise de casos em n.
  A ideia utilizada é que os nomes presentes no tracesMap
  retornados por bound_spec_traces são os nomes de processos
  presentes na lista de definições em 's'. E, como 's' é bem
  formada, os nomes nas definições são distintos.
*)
Lemma distinct_traces_map: forall (s: Spec) (n: nat),
  well_formed_spec s -> distinct_proc_names (bound_spec_traces n s).
Proof.
  intros.
  destruct n.
  {
    simpl. destruct s. simpl. simpl in H.
    unfold distinct_proc_names.
    apply proj1 in H.
    assert
      ((map
     (fun nameTrace : string * list Trace =>
      let (name, _) := nameTrace in name)
     (map (fun name : string => (name, [[]]))
        (process_names_defined l))) = (process_names_defined l)).
    {
      induction (process_names_defined l).
      - simpl. reflexivity.
      - simpl. simpl in H. apply proj2 in H.
        apply IHl0 in H. rewrite -> H. reflexivity.
    }
    rewrite -> H0. apply H.
  }
  {
    simpl.
    unfold well_formed_spec in H.
    destruct s. apply proj1 in H.
    unfold process_names_defined in H.
    unfold get_proc_defs.
    unfold distinct_proc_names.
    assert
    (forall (spec: Spec) (defs: list ProcDef)
      (n: nat),
    ((map (fun nameTrace : string * list Trace => let (name, _) := nameTrace in name)
     (map
        (fun def : ProcDef =>
         match def with
         | name ::= proc =>
             (name,
             build_traces (bound_spec_traces n spec) proc)
         end) defs)) = (map (fun d : ProcDef => match d with
                               | s ::= _ => s
                               end) defs))).
    {
      clear H.
      induction defs.
      {
        simpl. intros. reflexivity.
      }
      {
        intros. simpl. destruct a0.
        rewrite IHdefs.
        reflexivity.
      }
    }
    rewrite H0. apply H.
  }
Qed.

(*
  Esse lema afirma que o comportamento de get_trace está
  correto. Assumindo que os nomes de processo presentes
  em 'tracesMap', que mapeia nomes (string) para listas de traces,
  são distintos, então se um nome 'procName' está associado
  ao conjunto de traces 'traceSet' (o par (procName, traceSet)
  está em 'tracesMap'), então get_trace procName tracesMap
  retorna 'traceSet'.
  
  A prova é feita por indução na lista 'tracesMap'.
*)
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

(*
  Esse teorema afirma a corretude das funções build_traces e
  bound_spec_traces, assumindo uma especificação bem formada 
  ('spec').
  A corretude de build_traces para um dado processo 'proc'
  como entrada assume que os nomes de processo utilizados em
  'proc' estão definidos na especificação 'spec', e que os
  eventos usados em 'proc' estão definidos no alfabeto de 'spec'.
  A corretude de bound_spec_traces é provada para um nome de
  processo'name' que está associado a 'procBody' nas definições
  de 'spec'.
  A prova é feita por indução em n.
  Para a prova do caso base e do caso indutivo, a corretude
  de build_traces e de bound_spec_traces são provadas
  separadamente.
  
  A prova do caso base da corretude de build_traces é feita por
  indução no processo em questão ('proc').
  
  A prova do caso base da corretude de bound_spec_traces é feita
  diretamente, utilizando o fato de que para n = 0, o retorno
  da função associa qualquer nome de processo ao trace vazio, que
  é um trace de qualquer processo conforme IsProcTrace.
  
  A prova do caso indutivo de build_traces é feita por indução
  no processo ('proc'). Na prova do caso em que 'proc' tem
  o formato ProcName s, ou seja, é um nome de processo,
  utilizamos o fato de que qualquer nome utilizado em 'proc'
  está definido na especificação 'spec', portanto podemos usar
  a hipótese indutiva da corretude de bound_spec_traces.
  
  A prova do caso indutivo de bound_spec_traces é feita
  usando o fato de que qualquer processo ('procBody') presente na
  especificação 'spec' tem seus eventos no alfabeto de 'spec'
  e os nomes de processos utilizados estão definidos em 'spec'.
  Portanto, utilizamos a hipótese indutiva da corretude de
  build_traces.
*)

Theorem functional_traces_correctness:
forall (spec: Spec) (n: nat),  
  well_formed_spec spec ->
  (forall (proc: Proc) (trace: Trace),
  incl
    (extract_names proc)
    (process_names_defined (get_proc_defs spec)) ->
  incl
    (extract_events proc)
    (get_spec_alphabet spec) ->
  In
    trace
    (build_traces (bound_spec_traces n spec) proc) ->
    IsProcTrace proc spec trace
  ) /\
  (
    forall (name: string) (procBody: Proc) (trace: Trace),
    DefInSpec (name ::= procBody) spec ->
    In trace (get_trace name (bound_spec_traces n spec)) ->
    IsProcTrace procBody spec trace
  ).
Proof.
  intros.
  induction n.
  { (* n = 0 *)
    split.
    { (* corretude de build_traces *)
      intro proc.
      induction proc.
      { (* Stop *)
        intros.
        simpl in H2. rewrite or_false in H2. subst.
        apply AllEmptyTrace.
      }
      { (* Skip *)
        intros.
        simpl in H2. rewrite or_false in H2. subst.
        destruct H2.
        - subst.
          apply AllEmptyTrace.
        - subst. apply SkipTrace. 
      }
      { (* ProcPref *)
        intros.
        simpl in H2. destruct H2.
        {
          subst. apply AllEmptyTrace.
        }
        {
          destruct trace.
          { apply AllEmptyTrace. }
          {
            apply in_map_iff in H2.
            repeat destruct H2.
            apply PrefTrace.
            apply IHproc.
            {
              simpl in H0. apply H0.
            }
            {
              simpl in H1.
              unfold incl.
              intros. apply H1.
              simpl. right. apply H2.
            }
            {
              apply H3.
            }
            {
              unfold EventInSpec.
              destruct spec. simpl.
              simpl in H1. apply H1.
              simpl. left. reflexivity.
            }
          }
        }
      }
      { (* ProcExtChoice *)
        intros.
        simpl in H2. apply in_app_or in H2. destruct H2.
        {
          apply ExtChoiceTrace.
          left. apply IHproc1.
          {
            simpl in H0.
            unfold incl. intros.
            apply H0. apply in_or_app. left. apply H3.
          }
          {
            simpl in H1. unfold incl. intros. apply H1.
            apply in_or_app. left. apply H3.
          }
          {
            apply H2.
          }
        }
        {
          apply ExtChoiceTrace.
          right. apply IHproc2.
          {
            simpl in H0.
            unfold incl. intros.
            apply H0. apply in_or_app. right. apply H3.
          }
          {
            simpl in H1. unfold incl. intros. apply H1.
            apply in_or_app. right. apply H3.
          }
          {
            apply H2.
          }
        }
      }
      { (* ProcCond *)
        intros.
        destruct b.
        { (* true *)
          apply CondTrue.
          reflexivity.
          apply IHproc1.
          {
            simpl in H0.
            unfold incl. intros.
            apply H0. apply in_or_app. left. apply H3.
          }
          {
            simpl in H1. unfold incl. intros. apply H1.
            apply in_or_app. left. apply H3.
          }
          {
            apply H2.
          }
        }
        { (* false *)
          apply CondFalse.
          reflexivity. apply IHproc2.
          {
            simpl in H0.
            unfold incl. intros.
            apply H0. apply in_or_app. right. apply H3.
          }
          {
            simpl in H1. unfold incl. intros. apply H1.
            apply in_or_app. right. apply H3.
          }
          {
            apply H2.
          }
        }
      }
      { (* ProcName *)
        intros.
        simpl in H2.
        simpl in H0.
        unfold incl in H0.
        simpl in H0.
        assert (s = s). { reflexivity. }
        rewrite <- or_false in H3.
        apply H0 in H3.
        unfold process_names_defined in H3.
        apply in_map_iff in H3.
        destruct H3. destruct x.
        destruct H3.
        subst.
        apply NameTrace with (p := p).
        simpl in H0. unfold incl in H0.
        simpl in H0.
        assert (s = s). { reflexivity. }
        rewrite <- or_false in H3.
        apply H0 in H3.
        apply in_map
          with (f := (fun name : string => (name, [@nil Event])))
          in H3.
        apply distinct_traces_map with (n := 0) in H.
        apply get_trace_proc_name
          with (procName := s) (traceSet := [[]])
          in H.
        {
          simpl in H.
          rewrite -> H in H2.
          simpl in H2. rewrite or_false in H2.
          subst. apply AllEmptyTrace.
        }
        {
          apply H3.
        }
        {
           apply H4.
        }
      }
    }
    { (* corretude de bound_spec_traces *)
      intros.
      simpl in H1.
      unfold DefInSpec in H0.
      unfold process_names_defined in H1.
      assert (Hwf := H).
      apply distinct_traces_map with (n := 0) in H.
      simpl in H.
      Search "get_trace_proc_name".
      apply in_map
        with (f := (fun d : ProcDef => match d with
                                      | s ::= _ => s end))
        in H0.
      apply in_map
        with (f := (fun name : string => (name, [@nil Event])))
        in H0.
      eapply get_trace_proc_name in H.
      rewrite -> H in H1.
      2: apply H0.
      simpl in H1. rewrite or_false in H1.
      subst. apply AllEmptyTrace.
    }
  }
  { (* n = S n *)
    split.
    { (* corretude de build_traces *)
      induction proc.
      { (* Stop *)
        intros.
        simpl in H2. rewrite or_false in H2. subst.
        apply AllEmptyTrace.
      }
      { (* Skip *)
        intros.
        simpl in H2. rewrite or_false in H2. subst.
        destruct H2.
        - subst. apply AllEmptyTrace.
        - subst. apply SkipTrace.
      }
      { (* ProcPref *)
        intros.
        simpl in H2.
        destruct H2.
        {
          subst.
          apply AllEmptyTrace.
        }
        {
          destruct trace.
          1: apply AllEmptyTrace.
          apply in_map_iff in H2.
          repeat destruct H2.
          apply PrefTrace.
          apply IHproc.
          {
            apply H0.
          }
          {
            simpl in H1.
            unfold incl.
            intros.
            apply H1.
            simpl. right. apply H2.
          }
          {
            apply H3.
          }
          {
            unfold EventInSpec.
            apply H1.
            simpl. left. reflexivity.
          }
        }
      }
      { (* ProcExtChoice *)
        intros.
        apply ExtChoiceTrace.
        simpl in H2.
        apply in_app_or in H2.
        destruct H2.
        {
          left.
          apply IHproc1.
          {
            simpl in H0. unfold incl. intros.
            unfold incl in H0.
            apply H0.
            apply in_or_app. left. apply H3.
          }
          {
            simpl in H1. unfold incl. intros.
            unfold incl in H1.
            apply H1.
            apply in_or_app. left. apply H3.
          }
          {
            apply H2.
          }
        }
        {
          right.
          apply IHproc2.
          {
            simpl in H0. unfold incl. intros.
            unfold incl in H0.
            apply H0.
            apply in_or_app. right. apply H3.
          }
          {
            simpl in H1. unfold incl. intros.
            unfold incl in H1.
            apply H1.
            apply in_or_app. right. apply H3.
          }
          {
            apply H2.
          }
        } 
      }
      { (* ProcCond *)
        intros.
        destruct b.
        {
          apply CondTrue.
          reflexivity.
          apply IHproc1.
          {
            simpl in H0.
            unfold incl.
            intros.
            unfold incl in H0.
            apply H0.
            Search "in_or_app".
            apply in_or_app.
            left. apply H3.
          }
          {
            simpl in H1.
            unfold incl.
            intros.
            unfold incl in H1.
            apply H1.
            Search "in_or_app".
            apply in_or_app.
            left. apply H3.
          }
          {
            apply H2.
          }
        }
        {
          apply CondFalse.
          reflexivity.
          apply IHproc2.
          {
            simpl in H0.
            unfold incl.
            intros.
            unfold incl in H0.
            apply H0.
            Search "in_or_app".
            apply in_or_app.
            right. apply H3.
          }
          {
            simpl in H1.
            unfold incl.
            intros.
            unfold incl in H1.
            apply H1.
            Search "in_or_app".
            apply in_or_app.
            right. apply H3.
          }
          {
            apply H2.
          }
        }
      }
      { (* ProcName *)
        intros.
        destruct IHn.
        simpl in H2.
        simpl in H0. unfold incl in H0.
        simpl in H0.
        assert (s = s). { reflexivity. }
        rewrite <- or_false in H5.
        apply H0 in H5.
        unfold process_names_defined in H5.
        unfold get_proc_defs in H5.
        apply in_map_iff in H5.
        destruct H5.
        destruct x.
        destruct H5.
        subst.
        destruct spec.
        apply NameTrace with (p := p).
        {
          unfold get_proc_defs in H2.
          assert (Hdf := H6).
          apply in_map
            with (f := (fun def : ProcDef =>
              match def with
              | name ::= proc => (name, build_traces (bound_spec_traces n (SpecDef a l)) proc)
              end))
            in H6.
          Search "get_trace_proc_name".
          assert (Hwf := H).
          apply distinct_traces_map with (n := S n) in H.
          apply get_trace_proc_name
            with (procName := s) (traceSet := build_traces (bound_spec_traces n (SpecDef a l)) p)
            in H.
          simpl in H. rewrite -> H in H2.
          2: simpl. 2: apply H6.
          apply H3.
          {
            unfold well_formed_spec in Hwf.
            apply proj2 in Hwf.
            apply proj1 in Hwf.
            unfold process_names_used in Hwf.
            simpl.
            unfold incl in Hwf.
            unfold incl.
            intros.
            apply Hwf.
            rewrite in_flat_map.
            exists (s ::= p).
            split.
            - apply Hdf.
            - apply H5.
          }
          {
            unfold well_formed_spec in Hwf.
            apply proj2 in Hwf.
            apply proj2 in Hwf.
            apply proj2 in Hwf.
            unfold events_used in Hwf.
            simpl.
            unfold incl in Hwf.
            unfold incl.
            intros.
            apply Hwf.
            rewrite in_flat_map.
            exists (s ::= p).
            split.
            - apply Hdf.
            - apply H5.
          }
          {
            apply H2.
          }
        }
        {
          unfold DefInSpec. simpl. apply H6.
        }
      }
    }
    { (* corretude de bound_spec_traces *)
      intros.
      simpl in H1.
      destruct IHn.
      apply H2.
      {
        assert (Hwf := H).
        unfold well_formed_spec in Hwf.
        destruct spec.
        apply proj2 in Hwf.
        apply proj1 in Hwf.
        unfold process_names_used in Hwf.
        simpl.
        unfold incl in Hwf.
        unfold incl.
        intros.
        apply Hwf.
        rewrite in_flat_map.
        exists (name ::= procBody).
        split.
        - apply H0.
        - apply H4.
      }
      {
        assert (Hwf := H).
        unfold well_formed_spec in Hwf.
        destruct spec.
        apply proj2 in Hwf.
        apply proj2 in Hwf.
        apply proj2 in Hwf.
        unfold events_used in Hwf.
        simpl.
        unfold incl in Hwf.
        unfold incl.
        intros.
        apply Hwf.
        rewrite in_flat_map.
        exists (name ::= procBody).
        split.
        - apply H0.
        - apply H4.
      }
      {
        unfold DefInSpec in H0.
        apply in_map
          with (f := (fun def : ProcDef =>
              match def with
              | name ::= proc => (name, build_traces (bound_spec_traces n spec) proc)
              end))
          in H0.
        assert (Hwf := H).
        apply distinct_traces_map with (n := S n) in H.
        simpl in H.
        apply get_trace_proc_name
          with (procName := name) (traceSet := build_traces (bound_spec_traces n spec) procBody)
          in H.
        rewrite -> H in H1.
        - apply H1.
        - apply H0.
      }
    }
  }
Qed.

(*
  Esse teorema segue diretamente do anterior e afirma a corretude
  da função bound_spec_traces.
*)
Theorem bound_spec_traces_correctness:
forall (spec: Spec) (n: nat) (name: string) (proc: Proc)
  (trace: Trace),
  well_formed_spec spec ->
  DefInSpec (name ::= proc) spec ->
  In trace (get_trace name (bound_spec_traces n spec)) ->
  IsProcTrace proc spec trace.
Proof.
  intros.
  Print functional_traces_correctness.
  pose proof functional_traces_correctness as Hfc.
  apply Hfc with (n := n) in H.
  apply proj2 in H.
  apply H with (procBody := proc) (name := name).
  apply H0.
  apply H1.
Qed.

End Traces.