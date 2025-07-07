(*! Properties about the spec based on the initial configuration. *)

From Stdlib Require Import List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Spec Utils Tactics SpecLemmas.

Create HintDb invariants.
Import ListNotations.

Set Nested Proofs Allowed.

(* Defining the valid initial states of a machine in terms of compartments and thread initialization. *)
Module Configuration.
  Import Separation.
  Section WithContext. 
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {capEncodeDecode: @CapEncodeDecode Byte Key}.
    Notation Cap := (@Cap Key).
    Notation CapOrBytes := (@CapOrBytes Byte Key).
    Notation FullMemory := (@FullMemory Byte).

    Record ExportEntry : Type := {
        exportEntryAddr: nat; (* TODO: check bounds *)
        exportEntryStackSize: nat;
        exportEntryNumArgs: nat;
        exportEntryInterruptStatus: InterruptStatus
    }.

    Inductive ImportEntry :=
    | ImportEntry_SealedCapToExportEntry (c: Cap)
    | ImportEntry_SentryToLibraryFunction (c: Cap).
    (* | ImportEntry_MMIOCap (c: Cap) *)
    (* | ImportEntry_SharedObject (c: Cap). *)

    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> @Inst _ _ _ capEncodeDecode}.
    Context {pccNotInBounds : @EXNInfo Byte}.
    Notation Machine := (@Machine Byte Key).
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Notation RegisterFile := (@RegisterFile Byte Key).
    Notation ThreadStep := (ThreadStep fetchAddrs decode pccNotInBounds).
    Notation Thread := (@Thread Byte Key).

    Record InitialThreadMetadata := {
        initThreadEntryPoint: Addr;
        initThreadRf : RegisterFile;
        initThreadStackSize: nat;
        initThreadStackAddr: Addr
    }.

    Record Compartment := {
        compartmentReadOnly: list Addr; (* Code and read-only data, including import entries *)
        compartmentGlobals: list Addr;
        compartmentExports: list ExportEntry;
        compartmentImports: list ImportEntry
    }.

    (* The initial state of a machine is defined in terms of its compartments,
       the trusted switcher, the initial state of the threads, and the initial
       memory. *)
    Record Config := {
        configCompartments: list Compartment;
        configSwitcher: nat; (* Index of the switcher compartment *)
        configThreads : list InitialThreadMetadata;
        configInitMemory: FullMemory
        (* configMMIOAddrs: list Addr; *)
    }.

    Definition compartmentFootprint (compartment: Compartment) : list Addr :=
        compartment.(compartmentReadOnly) ++ compartment.(compartmentGlobals).
    Definition stackFootprint (t: InitialThreadMetadata) : list Addr :=
        seq t.(initThreadStackAddr) t.(initThreadStackSize).

    (* TODO *)
    Record WFCompartment (c: Compartment) := {
        WFCompartment_DisjointCodeAndData: Disjoint c.(compartmentReadOnly) c.(compartmentGlobals)
    }.

    Definition WFSwitcher (c: Compartment) : Prop := True.

    Definition ConfigFootprints (config: Config) :=
        (* (configMMIOAddrs config) :: *)
          (map compartmentFootprint config.(configCompartments))
           ++ (map stackFootprint config.(configThreads)).

    Record WFConfig (config: Config) := {
        WFConfig_footprintDisjoint: Separated (ConfigFootprints config);
        WFConfig_compartments: forall c, In c config.(configCompartments) -> WFCompartment c;
        WFConfig_switcher: exists c, nth_error config.(configCompartments) config.(configSwitcher) = Some c /\
                                WFSwitcher c
        (* WFConfig_importEntriesOk: ImportEntriesOk config *)
    }.

    Record ThreadInv (t: InitialThreadMetadata) (t: Thread) : Prop :=
    { Inv_validRf : ValidRf t.(thread_userState).(thread_rf)
    }.

    Record GlobalInvariant (config: Config) (m: Machine) : Prop :=
    { Inv_curThread: m.(machine_curThreadId) < length m.(machine_threads)
    ; Inv_threads : Forall2 ThreadInv config.(configThreads) m.(machine_threads)
    }.

    Record ValidInitialState (config: Config) (m: Machine) : Prop :=
      { ValidInit_memory: m.(machine_memory) = config.(configInitMemory)
      ; ValidInit_invariant: GlobalInvariant config m
      }.

    Hint Resolve Inv_curThread : invariants.
    Hint Resolve Inv_validRf: invariants.

    Section Proofs.

      (* TODO: add MMIO and shared objects *)
      Inductive AddressProvenance :=
      | Provenance_Stack (tid: nat)
      | Provenance_Compartment (cid: nat).
     
      Inductive AddrHasProvenance : Config -> Addr -> AddressProvenance -> Prop :=
      | StackProvenance : forall config addr tid metaThread,
          nth_error config.(configThreads) tid = Some metaThread ->
          In addr (stackFootprint metaThread) ->
          AddrHasProvenance config addr (Provenance_Stack tid)
      | CompartmentCodeProvenance: forall config addr cid compartment,
          nth_error config.(configCompartments) cid = Some compartment ->
          In addr (compartmentFootprint compartment) ->
          AddrHasProvenance config addr (Provenance_Compartment cid).

Ltac simplify_nat :=
  repeat match goal with
  | H: _ <? _ = true |- _ => rewrite PeanoNat.Nat.ltb_lt in H
  | H: _ <? _ = false |- _ => rewrite PeanoNat.Nat.ltb_nlt in H
  | _ => lia                                                                       
  end.
Tactic Notation "learn_hyp" constr(p) "as" ident(H') :=
  let P := type of p in
  match goal with
  | H : P |- _ => fail 1
  | _ => pose proof p as H'
  end.
Tactic Notation "learn_hyp" constr(p) :=
  let H := fresh in learn_hyp p as H.

      Lemma threadInConfigFootprint:
        forall config metaThread tid addr,
          nth_error (configThreads config) tid = Some metaThread ->
          In addr (stackFootprint metaThread) ->
          nth_error (ConfigFootprints config) (length config.(configCompartments) + tid) = Some (stackFootprint metaThread).
      Proof.
        intros * hthread haddr.
        unfold ConfigFootprints.
        rewrite nth_error_app. rewrite length_map.
        case_match; simplify_nat.
        rewrite nth_error_map.
        replace (length (configCompartments config) + tid - length (configCompartments config)) with tid by lia.
        rewrite hthread. cbn. eexists; split; eauto.
      Qed.

Ltac simplify_Separated :=
  repeat match goal with
  | H: Separated ?xs,
    H1: nth_error ?xs ?t1 = Some ?s1,
    H2: nth_error ?xs ?t2 = Some ?s2,
    H3: In ?addr ?s1,
    H4: In ?addr ?s2 |- _ =>
      let Heq := fresh in   
      assert (t1 = t2) as Heq;
      [ destruct (PeanoNat.Nat.eq_dec t1 t2); auto; 
        exfalso; eapply H with (2 := H1) (3 := H2) (4 := H3) (5 := H4); by auto | ];
      rewrite Heq in *
  | _ => progress (option_simpl; try lia)
  end.
      Lemma compartmentInConfigFootprint:
        forall config compartment cid addr,
          nth_error (configCompartments config) cid = Some compartment ->
          In addr (compartmentFootprint compartment) ->
          nth_error (ConfigFootprints config) cid = Some (compartmentFootprint compartment).
      Proof.
        intros * hthread haddr.
        unfold ConfigFootprints.
        rewrite nth_error_app. rewrite length_map. repeat rewrite nth_error_map.
        rewrite hthread.
        case_match; simplify_nat; auto.
        exfalso. apply H. apply nth_error_Some. rewrite_solve.
      Qed.

      Lemma uniqueInitialProvenance:
        forall config addr prov1 prov2,
          WFConfig config ->
          AddrHasProvenance config addr prov1 ->
          AddrHasProvenance config addr prov2 ->
          prov1 = prov2.
      Proof.
        intros * WFConfig hprov1 hprov2.
        destruct WFConfig.
        inv hprov1; inv hprov2; auto.
        all: repeat match goal with
        | H: nth_error (configThreads _) _ = Some ?thread,
          H1: In ?addr (stackFootprint ?thread) |- _ =>
            learn_hyp (threadInConfigFootprint _ _ _ _ H H1)
        | H: nth_error (configCompartments _) _ = Some ?comp,
          H1: In ?addr (compartmentFootprint ?comp) |- _ =>
            learn_hyp (compartmentInConfigFootprint _ _ _ _ H H1)
        | |- ?x _ = ?x _ => f_equal                        
        end.                                                                    
        all: destruct_products; simplify_Separated.



      Lemma InvariantInitial :
        forall config m,
          ValidInitialState config m ->
          GlobalInvariant config m.
      Proof.
        intros * hvalid.
        constructor.
        - apply hvalid.
        - apply ValidInit_invariant. auto.
      Qed.

      Lemma GlobalInvariantImpliesValidRf:
        forall config m id thread,
          GlobalInvariant config m ->
          nth_error (machine_threads m) id = Some thread ->
          ValidRf (thread_rf (thread_userState thread)).
      Proof.
        intros * hinv hthread.
        apply Inv_threads in hinv.
        destruct (nth_error (configThreads config) id) eqn:hconfig.
        - apply Forall2_nth_error2 with (x := i) (y := thread) (idx := id) in hinv.
          all: auto.
          apply hinv.
        - apply nth_error_None in hconfig. apply Forall2_length in hinv.
          apply Some_not_None in hthread. apply nth_error_Some in hthread. lia.
      Qed.

      Lemma ThreadStep_ThreadInv:
        forall x thread mem istatus userSt' mem' sysSt' istatus' ev,
        ThreadInv x thread ->
        ThreadStep (thread_userState thread, mem, (thread_systemState thread, istatus))
                   (userSt', mem', (sysSt', istatus'), ev) ->
        ThreadInv x {| thread_userState := userSt'; thread_systemState := sysSt' |}.
      Proof.
        intros * hinv hstep.
        inv hstep.
        - constructor.
          consider threadStepFunction; cbn.
          repeat destruct_matches_in_hyp H0; cbv[exceptionState] in *; simplify_eq; cbn; cbv[rf uc sc fst snd ints] in *.
          all: repeat match goal with
                | H: WfGeneralInst ?generalInst,
                  H1: ?generalInst _ _ = Ok _ |- ValidRf _ =>
                    eapply generalInstOkCommon with (1 := H) (2 := H1); by (eauto with invariants)
                | H: WfCallSentryInst ?callSentryInst _ _ ,
                  H1: ?callSentryInst _ _ = Ok _ |- ValidRf _ =>
                    eapply callSentryOkCommon with (1 := H) (2 := H1); by (eauto with invariants)
                end; eauto with invariants.
        - constructor; cbn. apply hinv.
      Qed.

      Lemma SameThreadStep_ThreadInv:
        forall config m1 m2 ev,
          machine_curThreadId m1 < length (machine_threads m1) ->
          Forall2 ThreadInv (configThreads config) (machine_threads m1) ->
          SameThreadStep m1 m2 ev ->
          Forall2 ThreadInv (configThreads config) (machine_threads m2).
      Proof.
        intros * hidx hinv hstep.
        pose proof hstep as _hstep.
        inv hstep. destruct_products.
        apply Forall2_nth_error1.
        - apply Forall2_length in hinv. rewrite hinv.
          eapply SameThreadStep_lengthThreads; eauto.
        - intros * hconfig hthread.
          pose proof hinv as hinv0.
          eapply Forall2_nth_error2' with (idx := idx) in hinv.
          2: { apply nth_error_Some. eapply Some_not_None; eauto. }
          destruct_products. option_simpl.
          rewrite threadIdEq in *.
          destruct (PeanoNat.Nat.eq_dec idx (machine_curThreadId m1)); subst; option_simpl.
          + eapply ThreadStep_ThreadInv; eauto.
          + rewrite idleThreadsEq with (1 := n) in *. option_simpl. auto.
      Qed.

      Lemma SameThreadStepOk :
        forall config s s' ev,
        GlobalInvariant config s ->
        SameThreadStep s s' ev ->
        GlobalInvariant config s'.
      Proof.
        intros * hinv hstep.
        destruct hinv.
        constructor.
        - eapply SameThreadStep_curId; eauto.
        - eapply SameThreadStep_ThreadInv; eauto.
      Qed.

      (* Machine step preserves the inductive invariant. *)
      Lemma GlobalInvariantStep :
        forall config s tr s' tr',
        GlobalInvariant config s ->
        MachineStep (s, tr) (s',tr') ->
        GlobalInvariant config s'.
      Proof.
        intros * hinv hstep.
        pose proof hinv as hginv.
        destruct hinv.
        inv hstep.
        - constructor; cbv [setMachineThread machine_threads machine_curThreadId]; auto.
        - eapply SameThreadStepOk; eauto.
      Qed.

    End Proofs.

  End WithContext. 
  Hint Resolve Inv_curThread : invariants.
End Configuration.

(* From any valid initial state where threads are isolated (their reachable
   read/write caps are disjoint), for any sequence of same-domain (Ev_General)
   steps, the reachable caps in each thread do not increase. *)
Module ThreadIsolatedMonotonicity.
  Import ListNotations.
  Import Configuration.
  Import Separation.
  Section WithContext. 
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {capEncodeDecode: @CapEncodeDecode Byte Key}.
    Notation FullMemory := (@FullMemory Byte).
    Notation EXNInfo := (@EXNInfo Byte).
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> @Inst _ _ _ capEncodeDecode}.
    Context {pccNotInBounds : EXNInfo}.
    Notation Machine := (@Machine Byte Key).
    Notation Cap := (@Cap Key).
    Notation CapOrBytes := (@CapOrBytes Byte Key).
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation Thread := (@Thread Byte Key).
    Notation Trace := (@Trace Byte Key).
    Notation State := (Machine * Trace)%type.
    Notation Event := (@Event Byte Key).
    Notation Config := (@Config Byte Key).
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Notation ReachableCapSubset := (@ReachableCapSubset ISA Byte Key).
    Notation RWAddressesDisjoint := (@RWAddressesDisjoint ISA Byte Key).
    Notation WriteReadDisjoint := (@WriteReadDisjoint ISA Byte Key).

    Definition SameDomainEvent (ev: Event) : Prop :=
      match ev with
      | Ev_SwitchThreads _ => True
      | Ev_SameThread _ Ev_General => True
      | _ => False
      end.
    Definition SameDomainTrace (tr: Trace) : Prop :=
      Forall SameDomainEvent tr.

    Definition ThreadReachableCapSubset (m_init m_cur: FullMemory) (t_init t_cur: Thread) : Prop :=
      ReachableCapSubset m_init m_cur (capsOfThread t_init) (capsOfThread t_cur).

    (* Threads only have read/write access to disjoint addresses. *)
    Definition IsolatedThreads (machine: Machine) : Prop :=
      Pairwise (RWAddressesDisjoint machine.(machine_memory))
               (map capsOfThread machine.(machine_threads)).

    Definition ValidInitialMachine (config: Config) (st: Machine) : Prop :=
      ValidInitialState config st /\
      IsolatedThreads st.

    Section WithConfig.
      Variable config: Config.
      Variable initialMachine: Machine.
      Variable pfValidInitialMachine: ValidInitialMachine config initialMachine.

      Definition IsolatedMonotonicity (machine: Machine) :=
        Forall2 (ThreadReachableCapSubset initialMachine.(machine_memory) machine.(machine_memory))
                initialMachine.(machine_threads) machine.(machine_threads).

      (* A thread's caps are a subset of caps reachable from initial state. *)
      Definition PThreadIsolatedMonotonicity (st: State) : Prop :=
        let '(machine, tr) := st in
        SameDomainTrace tr ->
        IsolatedMonotonicity machine.

      Record Invariant' machine : Prop :=
        {
          Inv_Isolation: IsolatedThreads machine;
          Inv_Monotonicity: IsolatedMonotonicity machine
        }.
      Definition Invariant (st: State) :=
        GlobalInvariant config (fst st) /\
        (SameDomainTrace (snd st) -> Invariant' (fst st)).
      Hint Resolve Inv_Monotonicity : invariants.
      Hint Resolve Inv_Isolation: invariants.

      Lemma InvariantInitial  :
        Invariant (initialMachine, []).
      Proof.
        intros * .
        constructor.
        - apply Configuration.InvariantInitial.
          apply pfValidInitialMachine.
        - intros htr. constructor.
          + cbv [fst]. apply pfValidInitialMachine.
          + cbv [SameDomainTrace ThreadReachableCapSubset ReachableCapSubset ValidInitialMachine IsolatedMonotonicity].
            apply Forall2_refl. auto.
      Qed.
      Lemma GlobalInvariant_length:
        forall m,
          GlobalInvariant config m ->
          length (machine_threads initialMachine) = length (machine_threads m).
      Proof.
        intros. destruct H.
        apply Forall2_length in Inv_threads0.
        rewrite<-Inv_threads0. destruct pfValidInitialMachine.
        apply Configuration.InvariantInitial in H. destruct H.
        apply Forall2_length in Inv_threads1. auto.
      Qed.

      Ltac simplify_invariants :=
        repeat match goal with
          | H: GlobalInvariant _ ?m,
              H1: nth_error (machine_threads ?m) _ = Some ?thread
            |- ValidRf (thread_rf (thread_userState ?thread)) =>
              eapply GlobalInvariantImpliesValidRf with (1 := H) (2 := H1)
          end.

      Lemma InvariantImpliesThreadReachableCapSubset:
        forall m thread thread' id,
          Invariant' m ->
          nth_error (machine_threads initialMachine) id = Some thread ->
          nth_error (machine_threads m) id = Some thread' ->
          ThreadReachableCapSubset (machine_memory initialMachine) (machine_memory m) thread thread'.
      Proof.
        intros. eapply Forall2_nth_error2 with (1 := Inv_Monotonicity _ H); eauto.
      Qed.
      Lemma IsolatedImpliesWriteReadDisjoint:
        forall m i j x y,
        IsolatedThreads m ->
        i <> j ->
        nth_error (machine_threads m) i = Some x ->
        nth_error (machine_threads m) j = Some y ->
        WriteReadDisjoint (machine_memory m) (capsOfThread x) (capsOfThread y).
      Proof.
        cbv[IsolatedThreads Pairwise].
        intros * hisolated hdiff hi hj.
        apply RWDisjointImpliesWriteReadDisjoint.
        eapply hisolated; eauto; by (apply map_nth_error).
      Qed.

      Lemma SameDomainStepOk:
        forall m m' ev,
          GlobalInvariant config m ->
          Invariant' m ->
          GlobalInvariant config m' ->
          SameDomainEvent ev ->
          SameThreadStep m m' ev ->
          Invariant' m'.
      Proof.
        cbv [SameDomainEvent].
        intros * hginv hinv hginv' hev hstep.
        pose proof hstep as hstep'.
        inv hstep. destruct_products.
        inv stepOkrl.
        rename H0 into hstep.
        revert hstep. cbv [threadStepFunction exceptionState uc sc fst snd].
        repeat (case_match; simplify_eq); try congruence.
        intros; simplify_eq.
        specialize generalInstOkCommon with (1 := wf) (2 := H0); intros hok.
        assert_pre_and_specialize hok.
        { simplify_invariants. }
        cbn in hok. destruct_products.

        constructor; auto.
        (* IsolatedThreads preserved *)
        { cbv[IsolatedThreads Pairwise].
          intros * neq capsi capsj.
          rewrite nth_error_map in *;
          repeat match goal with
          | H: option_map _ _ = Some _ |- _ =>
              apply option_map_Some in H; destruct_products; subst
          end.
          destruct (PeanoNat.Nat.eq_dec i (m'.(machine_curThreadId)));
          destruct (PeanoNat.Nat.eq_dec j (m'.(machine_curThreadId)));
            try lia; subst;
            rewrite idleThreadsEq in * by lia;
            rewrite threadIdEq in *; option_simpl.
          - eapply RWAddressDisjointUpdate with (mem := machine_memory m); eauto.
            eapply Inv_Isolation with (i := machine_curThreadId m) (j := j); try lia; auto;
              erewrite map_nth_error; eauto; auto.
          - apply RWAddressDisjointUpdate_symmetry.
            eapply RWAddressDisjointUpdate with (mem := machine_memory m); eauto.
            eapply Inv_Isolation with (i := machine_curThreadId m) (j := i); try lia; auto;
              erewrite map_nth_error; eauto; auto.
          - eapply RWAddressDisjointUpdateUnchanged; eauto.
            eapply Inv_Isolation with (i := i) (j := j); try lia; auto;
              erewrite map_nth_error; eauto; auto.
            eapply Inv_Isolation with (i := i) (j := machine_curThreadId m); try lia; auto;
              erewrite map_nth_error; try reflexivity; auto.
            eapply Inv_Isolation with (i := j) (j := machine_curThreadId m); try lia; auto;
              erewrite map_nth_error; try reflexivity; auto.
        }
        (* IsolatedMonotonicity preserved. *)
        {
          apply Forall2_nth_error1; auto.
          - apply GlobalInvariant_length. auto.
          - intros * hx hy.
            destruct (PeanoNat.Nat.eq_dec idx (m'.(machine_curThreadId))); subst.
            + rewrite threadIdEq in *.
              rewrite stepOkrr in *. option_simpl.
              assert (ThreadReachableCapSubset (machine_memory initialMachine) (machine_memory m)
                                         x thread) as hsubset0.
              { eapply InvariantImpliesThreadReachableCapSubset; eauto. }
              eapply ReachableCapSubset_ValidUpdate with (mem := machine_memory m); cbv[capsOfThread]; eauto.
            + (* Separation *)
              rewrite idleThreadsEq in hy by lia.
              assert (ThreadReachableCapSubset (machine_memory initialMachine) (machine_memory m)
                                         x y) as hsubset0.
              { eapply InvariantImpliesThreadReachableCapSubset; eauto.
              }
              eapply ReachableCapSubsetUpdateDisjointUnchanged; eauto.

              eapply IsolatedImpliesWriteReadDisjoint with (m := m) (j := idx) (i := machine_curThreadId m);
                auto with invariants; lia.
        }
      Qed.

      Lemma InvariantStep (s: State) :
        forall t,
        Invariant s ->
        MachineStep s t ->
        Invariant t.
      Proof.
        cbv[Invariant SameDomainTrace].
        intros * hinv hstep. destruct s. destruct t.
        cbv [fst snd] in *.
        destruct_products.
        assert (GlobalInvariant config m0) as hglobal' by (eapply GlobalInvariantStep; eauto).
        split; auto.
        intros htr.
        inv hstep; inv htr; propositional.
        - constructor.
          + pose proof (Inv_Isolation _ hinvr) as hisolation. auto.
          + cbv [setMachineThread machine_threads].
            apply (Inv_Monotonicity _ hinvr).
        - eapply SameDomainStepOk with (m := m); eauto.
      Qed.

      Lemma InvariantUse (s: State) :
        Invariant s ->
        PThreadIsolatedMonotonicity s.
      Proof.
        cbv[PThreadIsolatedMonotonicity Invariant fst snd]. destruct s.
        intros * [hginv hinv] htr.
        eauto with invariants.
      Qed.
    End WithConfig.

    (* For any well-formed configuration `config` and initial_machine
       configured with `config` such that the reachable addresses with
       read/write permissions in each thread are isolated, after any
       sequence of same-domain steps, the reachable caps from each
       thread are a subset of the caps reachable from the initial
       state.
     *)
    Theorem ThreadIsolatedMonotonicity :
      forall config initial_machine,
      WFConfig config ->
      ValidInitialMachine config initial_machine ->
      Combinators.always MachineStep (PThreadIsolatedMonotonicity initial_machine) (initial_machine, []).
    Proof.
      intros * hwf_config hinit_ok.
      econstructor.
      - eapply InvariantInitial. eauto.
      - eapply InvariantStep; eauto.
      - eapply InvariantUse; eauto.
    Qed.
  End WithContext. 
End ThreadIsolatedMonotonicity.


(* Isolated compartment:
   - if a compartment has no export entries, and its import entries
     only consist of sentries to libraries, then no other compartment
     can access the isolated compartment's caps.
 *)
   


(* Invariant: if a (isolated) compartment always sanitizes its caps such that
   - as a caller, all arguments have LG unset
   - as a callee, it never passes caps that have access to its globals in the return argument
     --> how to enforce this?
   then other compartments should only have temporary access to its caps
   -> that is, the only caps a thread in a different compartment should have access to belonging to 
 *)
                                                                              
