(*! Properties about the spec based on the initial configuration. *)

From Stdlib Require Import String List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Spec Utils Tactics SpecLemmas.

Create HintDb invariants.
Import ListNotations.
Create HintDb lists.
Hint Resolve nth_error_In : lists.

Set Nested Proofs Allowed.
Import Separation.

(* Defining the valid initial states of a machine in terms of
   compartments and thread initialization. *)
Module Configuration.
  Section WithContext.
    Context [ISA: ISA_params].
    Context {machineTypeParams: MachineTypeParams}.
    Context {capEncodeDecode: CapEncodeDecode}.

    Record ExportEntry : Type := {
        exportEntryOffset: nat; 
        exportEntryStackSize: nat;
        exportEntryNumArgs: nat;
        exportEntryInterruptStatus: InterruptStatus
      }.

    Inductive handlerType :=
    | Stackful
    | Stackless.
    
    Record ErrorHandler := {
        errorHandlerOffset: nat; (* Offset from compartment's PCC *)
        errorHandlerType: handlerType
    }.

    (* Simplifying, for now, and eliding MMIO and shared objects. *)
    Inductive ImportEntry :=
    | ImportEntry_SealedCapToExportEntry (c: Cap)
    | ImportEntry_SentryToLibraryFunction (c: Cap).

    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> @Inst _ _ capEncodeDecode}.
    Context {pccNotInBounds : EXNInfo}.
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Notation ThreadStep := (ThreadStep fetchAddrs decode pccNotInBounds).

    Record InitialThreadMetadata := {
        (* initThreadEntryPoint: Addr; *)
        (* initThreadRf : RegisterFile; *)
        initThreadCSP: Cap;
        initThreadCompartment: nat
    }.

    (* TODO: MMIO *)
    Record Compartment := {
        compartmentPCC: Cap; (* Code and read-only data, including import entries *)
        compartmentCGP: option Cap; (* If None, then this compartment is a library. *)
        compartmentImports: list ImportEntry;
        compartmentErrorHandlers: list ErrorHandler; 
        compartmentExports: list ExportEntry;
        compartmentExportTableAddrs: list Addr; (* Addresses where export table entries are stored. *)
        compartmentSealingCaps: list Cap; (* Sealing and unsealing caps *)
      }.

    Definition isLibrary (c: Compartment) :=
      match c.(compartmentCGP) with
      | None => true
      | _ => false
      end.

    (* Compartments can have sealed forward sentries to
       compartment_switcher_entry. When in user mode, compartments'
       MEPCC points to exception_entry_asm. The switcher may pass
       sealed backwards sentries to switcher_after_compartment_call
       and error_handler_return.
     *)
    Record SwitcherConfig := {
        Switcher_compartmentIdx: nat;
        Switcher_AddrOf_compartment_switcher_entry: Addr;
        Switcher_AddrOf_exception_entry_asm : Addr;
        Switcher_AddrOf_switcher_after_compartment_call: Addr;
        Switcher_AddrOf_error_handler_return: Addr;
        Switcher_key: Key; (* The switcher's exclusive key *)
    }.

    (* The initial state of a machine is defined in terms of its
       compartments, libraries, the trusted switcher, the initial
       state of the threads, and the initial memory. *)
    Record Config := {
        configCompartments: list Compartment;
        configThreads : list InitialThreadMetadata;
        configInitMemory: FullMemory;
        configSwitcher: SwitcherConfig;
    }.
    Definition compartmentFootprint (compartment: Compartment) : list Addr :=
        compartment.(compartmentPCC).(capAddrs) ++
        (from_option capAddrs [] compartment.(compartmentCGP)).

    Definition stackFootprint (t: InitialThreadMetadata) : list Addr :=
      t.(initThreadCSP).(capAddrs).

    Definition exportTableFootprint (c: Compartment) :=
      c.(compartmentExportTableAddrs).

    Definition capsOfImportEntry (ie: ImportEntry) :=
      match ie with
      | ImportEntry_SealedCapToExportEntry c => c
      | ImportEntry_SentryToLibraryFunction c => c
      end.                                                    
    (* The set of capabilities a compartment initially has access to. *)
    Definition capsOfCompartment (c: Compartment) :=
      [c.(compartmentPCC)]
      ++ (from_option (fun cgp => [cgp]) [] c.(compartmentCGP))
      ++ (map capsOfImportEntry c.(compartmentImports))
      ++ (c.(compartmentSealingCaps)).

    Definition AddrInCompartment (config: Config) (cid: nat) (addr: Addr): Prop :=
      exists compartment,
        nth_error config.(configCompartments) cid = Some compartment /\
          In addr (compartmentFootprint compartment).

    Definition AddrInStack (config: Config) (tid: nat) (addr: Addr): Prop :=
      exists meta,
        nth_error config.(configThreads) tid = Some meta /\
        In addr (stackFootprint meta).

    (* The total set of capabilities reachable from a compartment are
       the PCC+CGP+imports. *)
    Definition AllReachableCaps (mem: FullMemory) (caps: list Cap) :=
      forall cap,
        ReachableCap mem caps cap ->
        forall mem',
        ReachableCap (mem', fun _ => false) caps cap.
    
    (* TODO: Not sufficient; need to include sealed caps. *)
    (* The addresses reachable from each compartment are all
       reachable from PCC or CGP.
     *)
    Definition InitialCompartmentAddressesOk (mem: FullMemory) (compartment: Compartment) : Prop :=
      forall a, ReachableRWXAddr mem (capsOfCompartment compartment) a ->
                    In a (compartmentFootprint compartment).
                
    Definition ValidUnsealedCap (c: Cap) : Prop :=
      In c.(capCursor) c.(capAddrs) /\ c.(capSealed) = None.

    (* Any sentries initially reachable from a compartment must be present in the import table. *)
    Definition SentriesOnlyFromImportTables (mem: FullMemory) (compartment: Compartment) : Prop :=
      forall cap,
        ReachableCap mem (capsOfCompartment compartment) cap ->
        isSentry cap = true ->
        In (ImportEntry_SentryToLibraryFunction cap) compartment.(compartmentImports).

    Definition SealedDataCapsOnlyFromImportTables (mem: FullMemory) (compartment: Compartment) : Prop :=
     forall cap,
       ReachableCap mem (capsOfCompartment compartment) cap ->
       isSealedDataCap cap = true ->
       In (ImportEntry_SealedCapToExportEntry cap) compartment.(compartmentImports).

    (* A capability is in a library of its addresses belong to a library *)
    Definition InLibraryFootprint (config: Config) (cap: Cap) :=
      exists library, In library config.(configCompartments) /\
                      isLibrary library = true /\
                        Subset cap.(capAddrs) (compartmentFootprint library).

    Definition InExportTableFootprint (config: Config) (cap: Cap) :=
      exists compartment, In compartment config.(configCompartments) /\
                          Subset cap.(capAddrs) (exportTableFootprint compartment).

    Definition ValidPCCPerms cap :=
      Subset cap.(capPerms) [Perm.Exec;Perm.System;Perm.Load;Perm.Cap] (* No store, sealing, unsealing *) 
      /\ ~(In Local cap.(capCanStore)). (* No SL *)

    Definition ValidCGPPerms cap :=
      Subset cap.(capPerms) [Perm.Exec;Perm.System;Perm.Load;Perm.Store;Perm.Cap] (* No sealing, unsealing *) 
      /\ ~(In Local cap.(capCanStore)). (* No SL *)

    Definition WFImportEntry (config: Config) (importEntry: ImportEntry) :=
        (* All sentries to library functions are indeed sentries to library functions. *)
        (forall cap, importEntry = ImportEntry_SentryToLibraryFunction cap ->
                     isForwardSentry cap = true /\
                     InLibraryFootprint config cap /\
                     ValidPCCPerms cap  
        ) /\
        (* All sealed caps to export entries are sealed with the switcher key and point to an export table.*)
        (forall cap, importEntry = ImportEntry_SealedCapToExportEntry cap ->
                     cap.(capSealed) = Some (inr config.(configSwitcher).(Switcher_key)) /\
                     InExportTableFootprint config cap
        ).

    Definition ValidSealingCap (c: Cap) :=
      Subset c.(capPerms) [Perm.Sealing;Perm.Unsealing].
    
    Record WFCompartment (config: Config) (c: Compartment) :=
      {
        (* All RWX addresses reachable by a compartment belong to the compartment's footprint. *)
        WFCompartment_ReachableRWXAddr: InitialCompartmentAddressesOk config.(configInitMemory) c
        (* All caps reachable by a compartment can be derived from its
           initial auditable set of capabilities (PCC, CGP, import
           entries, sealing caps). *)
      ; WFCompartment_InitialCaps: AllReachableCaps config.(configInitMemory) (capsOfCompartment c)
        (* Compartment's PCC is sensible. *)
      ; WFCompartment_PCC: c.(compartmentPCC).(capSealed) = None /\
                             ValidPCCPerms c.(compartmentPCC)
        (* Compartment's CGP is sensible. *)
      ; WFCompartment_CGP: forall cgp, c.(compartmentCGP) = Some cgp ->
                                       cgp.(capSealed) = None /\
                                       ValidCGPPerms cgp
        (* All sentries reachable by a compartment were declared in import tables. *) 
      ; WFCompartment_Sentries: SentriesOnlyFromImportTables config.(configInitMemory) c
        (* All sealed data caps were declared in import tables. *) 
      ; WFCompartment_SealedDataCap: SealedDataCapsOnlyFromImportTables config.(configInitMemory) c
      ; WFCompartment_ImportEntries: forall entry, In entry c.(compartmentImports) -> WFImportEntry config entry
        (* Valid sealing/unsealing caps *) 
      ; WFCompartment_SealingCaps: Forall ValidSealingCap c.(compartmentSealingCaps)
      ; (* No one has access to seal with the switcher's key *)
        WFCompartment_SwitcherSealingKey: Forall (fun c => ~(In Perm.Sealing c.(capPerms) /\
                                                             In config.(configSwitcher).(Switcher_key) c.(capSealingKeys)))
                                                 c.(compartmentSealingCaps)
      }.                                                                       

    Definition WFSwitcher (c: Compartment) : Prop := True.
    Definition switcherIdx config := (config.(configSwitcher).(Switcher_compartmentIdx)).
    
    Definition ConfigFootprints (config: Config) :=
        (* (configMMIOAddrs config) :: *)
          (map compartmentFootprint config.(configCompartments))
            ++ (map stackFootprint config.(configThreads))
            ++ (map exportTableFootprint config.(configCompartments)).

    Record WFConfig (config: Config) := {
        (* Compartments, stack, and export table occupy disjoint memory regions. *)
        WFConfig_footprintDisjoint: Separated (ConfigFootprints config);
        WFConfig_compartmentMemory: Forall (WFCompartment config) config.(configCompartments);
        WFConfig_switcher: exists c, nth_error config.(configCompartments) (switcherIdx config) = Some c /\
                                       WFSwitcher c;
        (* The switcher's unsealing key belongs only to the switcher's compartment *)
        WFConfig_switcherSecret: forall c id cap, nth_error config.(configCompartments) id = Some c /\
                                                In cap c.(compartmentSealingCaps) /\
                                                In config.(configSwitcher).(Switcher_key) cap.(capUnsealingKeys) ->
                                                id = switcherIdx config
    }.

    Record ThreadInv (meta: InitialThreadMetadata) (t: Thread) : Prop :=
    { Inv_validRf : ValidRf t.(thread_userState).(thread_rf)
    }.

    Inductive AddressProvenance :=
    | Provenance_Stack (tid: nat)
    | Provenance_Compartment (cid: nat)
    | Provenance_Library (lid: nat).                                 
     
    Inductive AddrHasProvenance : Config -> Addr -> AddressProvenance -> Prop :=
    | StackProvenance : forall config addr tid metaThread,
        nth_error config.(configThreads) tid = Some metaThread ->
        In addr (stackFootprint metaThread) ->
        AddrHasProvenance config addr (Provenance_Stack tid)
    | CompartmentCodeProvenance: forall config addr cid compartment,
        nth_error config.(configCompartments) cid = Some compartment ->
        In addr (compartmentFootprint compartment) ->
        AddrHasProvenance config addr (Provenance_Compartment cid).

    Record GlobalInvariant (config: Config) (m: Machine) : Prop :=
    { Inv_curThread: m.(machine_curThreadId) < length m.(machine_threads)
    ; Inv_threads : Forall2 ThreadInv config.(configThreads) m.(machine_threads)
    }.

    (* Based on the initial configuration, we can statically determine
       whether a capability corresponds to a compartment's export table
       entry and if so, which compartment and which entry.
       TOOD: add a well-formedness condition as below.
     *)
    Context (LookupExportTableCompartmentId: Config -> Cap -> option (nat * nat)).
    Definition WFLookupExportTableCompartmentId :=
      forall config cap cid eid,
        LookupExportTableCompartmentId config cap = Some (cid,eid) ->
        exists compartment entry,
          nth_error config.(configCompartments) cid = Some compartment /\
          Subset cap.(capAddrs) compartment.(compartmentExportTableAddrs) /\
          nth_error compartment.(compartmentExports) eid = Some entry.  

    Definition LookupExportTableCompartment (config: Config) (cap: Cap) :=
      match LookupExportTableCompartmentId config cap with
      | Some (cid, _) =>
          nth_error config.(configCompartments) cid
      | None => None
      end.

    Definition LookupExportTableCompartmentAndEntry (config: Config) (cap: Cap) :=
     match LookupExportTableCompartmentId config cap with
     | Some (cid, eid) =>
         match nth_error config.(configCompartments) cid with
         | Some compartment => 
             match nth_error compartment.(compartmentExports) eid with
             | Some entry => Some (compartment, entry)
             | None => None 
             end
         | None => None 
         end
     | None => None
     end.

    Definition mkCSP' (addrs: list Addr) (cursor: Addr) : Cap :=
      {| capSealed := None;
         capPerms := [Perm.Load;Perm.Store;Perm.Cap];
         capCanStore := [Local;NonLocal];
         capCanBeStored := [Local];
         capSealingKeys := [];
         capUnsealingKeys := [];
         capAddrs := addrs;
         capKeepPerms := [Perm.Exec;Perm.System;Perm.Load;Perm.Cap;Perm.Sealing;Perm.Unsealing];
         capKeepCanStore := [Local;NonLocal];
         capKeepCanBeStored := [Local;NonLocal]; 
         capCursor := cursor 
      |}. 

    Definition mkCSP (base: Addr) (len: nat) (cursor: Addr) : Cap :=
      mkCSP' (seq base len) cursor.

    Definition ValidCSP (csp: Cap) :=
      exists base len addr,
      In addr (seq base len) /\
      csp = mkCSP base len addr.

    Record ValidTrustedStackFrame
      (config: Config)
      (mem: FullMemory) (frame: TrustedStackFrame) (meta: InitialThreadMetadata)
      (cid: nat): Prop :=
      { (* Trusted stack frame should point to an export table. *)
        ValidTrustedStackFrame_calleeCap:
        exists eid, LookupExportTableCompartmentId config frame.(trustedStackFrame_calleeExportTable)
                    = Some (cid, eid)
        (* Trusted stack CSP should always be a valid CSP that's a subset of the initial CSP. *)
      ; ValidTrustedStackFrame_CSP :
          ValidCSP frame.(trustedStackFrame_CSP) /\
          Restrict meta.(initThreadCSP) frame.(trustedStackFrame_CSP)
      }.

    Record ValidInitialThread (config: Config) (meta: InitialThreadMetadata) (t: Thread) : Prop :=
      { ValidInitialThread_caps:
        (* Initially, a thread can only access the caps corresponding to its initial compartment along with the CSP *)
        exists compartment,
          nth_error config.(configCompartments) meta.(initThreadCompartment) = Some compartment /\
            forall c,
              ReachableCap config.(configInitMemory) (capsOfUserTS (thread_userState t)) c ->
              ReachableCap config.(configInitMemory)
                           (meta.(initThreadCSP)::capsOfCompartment compartment)
                           c
        (* Threads are initialized with an initial call frame belonging to the initial compartment. *)
      ; ValidInitialThread_trustedStack:
          exists frame, t.(thread_systemState).(thread_trustedStack).(trustedStack_frames) =
                          [frame] /\
                          ValidTrustedStackFrame config config.(configInitMemory) frame meta meta.(initThreadCompartment)
        (* No caps in initial stack --> TODO: fix spec *)
      ; ValidInitialThread_stackUntagged: 
        forall capa, Subset (seq (fromCapAddr capa) ISA_CAPSIZE_BYTES) (stackFootprint meta) ->
                     readTag config.(configInitMemory) capa = false
      ; ValidInitialCSP: ValidCSP meta.(initThreadCSP)
      }.

    Definition mkUnsealedPCC (addrs: list Addr) (cursor: Addr) := 
      {| capSealed := None;
         capPerms := [Perm.Exec;Perm.System;Perm.Load;Perm.Cap];
         capCanStore := [NonLocal];
         capCanBeStored := [Local]; 
         capSealingKeys := [];  
         capUnsealingKeys := [];
         capAddrs := addrs;          
         capKeepPerms := [Perm.Exec;Perm.System;Perm.Load;Perm.Cap;Perm.Sealing;Perm.Unsealing];
         capKeepCanStore := [Local;NonLocal];
         capKeepCanBeStored := [Local;NonLocal];
         capCursor := cursor; 
      |}.

    Definition switcherFootprint (config: Config) :=
      match nth_error config.(configCompartments) config.(configSwitcher).(Switcher_compartmentIdx) with
      | Some compartment => compartment.(compartmentPCC).(capAddrs)
      | None => []                                             
      end.

    Definition MEPCC (config: Config) : Cap :=
      mkUnsealedPCC (switcherFootprint config) config.(configSwitcher).(Switcher_AddrOf_exception_entry_asm). 

    (* MEPCC initially points to the switcher's exception entry path *)
    Record UserModeOk (config: Config) (t: Thread ) : Prop :=
      { MEPCC_ok: t.(thread_systemState).(thread_mepcc) = (MEPCC config)}.

    Definition ThreadHasSystemPerm (t: Thread) : Prop :=
      In Perm.System t.(thread_userState).(thread_pcc).(capPerms).

    Definition UserModeInvariant (config: Config) (m: Machine) : Prop :=
      forall thread, In thread m.(machine_threads) ->
                     (~ ThreadHasSystemPerm thread) ->
                     UserModeOk config thread.
                    
    Record ValidInitialState (config: Config) (m: Machine) : Prop :=
      { ValidInit_memory: m.(machine_memory) = config.(configInitMemory)
      ; ValidInit_threads: Forall2 (ValidInitialThread config) config.(configThreads) m.(machine_threads) 
      ; ValidInit_invariant: GlobalInvariant config m
      ; ValidInit_userMode: UserModeInvariant config m
      }.

    Hint Resolve Inv_curThread : invariants.
    Hint Resolve Inv_validRf: invariants.

    Definition dummy_memory (mem: Memory_t) : FullMemory :=
      (mem, fun _ => false).

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
      saturate_list.
      rewrite nth_error_app. rewrite length_map.
      replace (length (configCompartments config) + tid - length (configCompartments config)) with tid by lia.
      case_match; simplify_nat; auto.
      rewrite nth_error_map.
      rewrite hthread. auto.
    Qed.

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

    Section Proofs.

      Definition AddrInSwitcherFootprint (config: Config) (addr: Addr) :=
        AddrInCompartment config (switcherIdx config) addr.
      Definition AddrsInSwitcherFootprint (config: Config) (addr: list Addr) :=
        forall a, In a addr -> AddrInCompartment config (switcherIdx config) a.

      Ltac saturate_footprints := 
        repeat match goal with
          | H: nth_error (configThreads _) _ = Some ?thread,
              H1: In ?addr (stackFootprint ?thread) |- _ =>
              let H' := fresh H1 "footprint" in 
              learn_hyp (threadInConfigFootprint _ _ _ _ H H1) as H'
          | H: nth_error (configCompartments _) _ = Some ?comp,
              H1: In ?addr (compartmentFootprint ?comp) |- _ =>
              let H' := fresh H1 "footprint" in 
              learn_hyp (compartmentInConfigFootprint _ _ _ _ H H1) as H'
          end.     


      (* TODO: add MMIO and shared objects *)
      Lemma uniqueInitialProvenance:
        forall config addr prov1 prov2,
          WFConfig config ->
          AddrHasProvenance config addr prov1 ->
          AddrHasProvenance config addr prov2 ->
          prov1 = prov2.
      Proof.
        intros * WFConfig hprov1 hprov2.
        destruct WFConfig.
        inv hprov1; inv hprov2; auto; saturate_footprints;
        repeat match goal with
        | |- ?x _ = ?x _ => f_equal
        | |- Provenance_Stack _ = Provenance_Compartment _ => exfalso
        | |- Provenance_Compartment _ = Provenance_Stack _ => exfalso
        | |- Provenance_Stack _ = Provenance_Library _ => exfalso
        end.                                                                    
        all: destruct_products; simplify_Separated; saturate_list; try lia.
      Qed.

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

Module SwitcherProperty.
  Import ListNotations.
  Import Configuration.
  Import Separation.

  (* We focus on the following entry points of the switcher:
     - compartment_switcher_entry (we can assume compartments have a
       forward sentry to this point)
     - exception_entry_asm (in user mode, MEPCC should point here)

     The switcher passes backwards sentries to:
     - switcher_after_compartment_call
     - handle_error_handler_return:

     Notes:
     - We have specified the behavior of the interrupt handler as
       switching threads atomically.
     - The MTDC register nominally points to the trusted stack, which
       is a first-class citizen in our spec.
     - Instructions in the switcher might use the MTDC register (and
       other system registers). We'll probably want to add more system
       registers or register-spill-areas to the trusted
       stack. Instructions that clobber the MTDC or register spill
       area used in context switching should be viewed as atomic
       steps, with interrupts disabled.
   *)

  Section WithContext.
    Context [ISA: ISA_params].
    Context {machineTypeParams: MachineTypeParams}.
    Context {capEncodeDecode: CapEncodeDecode}.
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {fetchAddrsOk: FetchAddrsOk fetchAddrs}.
    Context {pccNotInBounds : EXNInfo}.
    Notation AddrOffset := nat (only parsing).
    Notation PCC := Cap (only parsing).
    Notation State := (Machine * Trace)%type.
    Context {LookupExportTableCompartmentId: Config -> Cap -> option (nat * nat)}.
    Notation LookupExportTableCompartment := (LookupExportTableCompartment LookupExportTableCompartmentId).
    Notation LookupExportTableCompartmentAndEntry := (LookupExportTableCompartmentAndEntry LookupExportTableCompartmentId).

    Notation ValidInitialState := (@ValidInitialState _ _ _ LookupExportTableCompartmentId).
    Notation ValidInitialThread := (@ValidInitialThread _ _ _ LookupExportTableCompartmentId).
    Context {decode: list Byte -> @Inst _ _ capEncodeDecode}.
    Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Notation ThreadStep := (ThreadStep fetchAddrs decode pccNotInBounds).
    Notation ThreadState := (UserContext * SystemContext)%type.

    Section Utils.
      Definition RfSpecT : Type := list (nat * (CapOrBytes -> Prop)).
      Definition RegProp (rf: RegisterFile) (idx : nat) (P: CapOrBytes -> Prop) :=
        exists v, nth_error rf idx = Some v /\ P v.

      (* A register file satisfies a spec if:
         - It's a valid rf.
         - All registers listed in the spec satisfy the listed property.
         - All other registers satisfy the default property.
       *)
      Record RfSpec (spec: RfSpecT) (rf: RegisterFile) (default: CapOrBytes -> Prop) : Prop :=
        { RfSpec_ValidRF: ValidRf rf
        ; RfSpec_props : forall idx p, In (idx, p) spec -> RegProp rf idx p
        ; RfSpec_other: forall idx, idx < ISA_NREGS ->
                                    (~(exists p, In (idx, p) spec)) ->
                                    RegProp rf idx default
        }.

    End Utils.
    
    Section WithConfig.
      Variable config: Config.
      Variable (pf_wf_config: WFConfig config).
      Notation MEPCC := (MEPCC config).
      Definition MemEquivalentAtAddr (mem1 mem2: FullMemory) (addr: Addr) :=
        readByte mem1 addr = readByte mem2 addr /\
        (readTag mem1 (toCapAddr addr) = readTag mem2 (toCapAddr addr)).
      Definition MemEquivalentAtThread (tid: nat) (mem1 mem2: FullMemory) : Prop :=
        forall addr, AddrInStack config tid addr ->
                     MemEquivalentAtAddr mem1 mem2 addr.

      Definition inSystemMode (st: ThreadState) : bool :=
        existsb (Perm.t_beq Perm.System) (pcc st).(capPerms).

      Definition InSystemMode (st: ThreadState) : Prop :=
        In Perm.System (Spec.pcc st).(capPerms).
      Definition ThreadInSystemMode (t: Thread) :=
        In Perm.System t.(thread_userState).(thread_pcc).(capPerms).

      Definition SwitcherCodeUnchanged (mem: FullMemory) : Prop :=
        forall addr, AddrInCompartment config
                       config.(configSwitcher).(Switcher_compartmentIdx) addr ->
                     MemEquivalentAtAddr config.(configInitMemory) mem addr.

      Definition ReadOnlyMemUnchanged (mem: FullMemory) : Prop :=
        forall addr compartment,
          In compartment config.(configCompartments) ->
          In addr compartment.(compartmentPCC).(capAddrs) ->
          MemEquivalentAtAddr config.(configInitMemory) mem addr.
      
      Record GlobalMemInvariants (mem: FullMemory) : Prop :=
        { Inv_ReadOnlyMem: ReadOnlyMemUnchanged mem}.



      (* TODO: check this. Probably wrong *)
      Definition CompartmentCallPCC : Cap :=
        mkUnsealedPCC (switcherFootprint config) config.(configSwitcher).(Switcher_AddrOf_compartment_switcher_entry).
      Definition CompartmentReturnPCC : Cap :=
        mkUnsealedPCC (switcherFootprint config) config.(configSwitcher).(Switcher_AddrOf_switcher_after_compartment_call).
      Definition ErrorHandlerReturnPCC : Cap :=
        mkUnsealedPCC (switcherFootprint config) config.(configSwitcher).(Switcher_AddrOf_error_handler_return). 

      Definition ValidTrustedStack (trustedStack: TrustedStack) : Prop :=
       (forall frame, In frame trustedStack.(trustedStack_frames) ->
                 ValidCSP frame.(trustedStackFrame_CSP) /\
                 (exists compartment entry, 
                     LookupExportTableCompartmentAndEntry config frame.(trustedStackFrame_calleeExportTable) = Some (compartment, entry) /\
                     compartment.(compartmentCGP) <> None)).
     
      Record UserModeInvariants (meta: InitialThreadMetadata) (t: Thread) : Prop :=
      { UserInv_MEPCC := t.(thread_systemState).(thread_mepcc) = MEPCC 
      ; UserInv_TrustedStack := ValidTrustedStack t.(thread_systemState).(thread_trustedStack)
      }.    
      
      Record ThreadInv' (meta: InitialThreadMetadata) (t: Thread) : Prop :=
      { Inv_validRf : ValidRf t.(thread_userState).(thread_rf)
      ; Inv_userMode: ~(ThreadInSystemMode t) -> UserModeInvariants meta t
      }.                                                                    

      Record GlobalInvariants (m: Machine) : Prop :=
      { Inv_Mem: GlobalMemInvariants m.(machine_memory)
      ; Inv_Threads: Forall2 ThreadInv' config.(configThreads) m.(machine_threads)
      }.

      Section WithSwitcherParams.
        Record ConcreteRf :=
          { rf_ra : nat;
            rf_gp : nat;
            rf_sp : nat;
            rf_tp: nat;
            rf_t0: nat;
            rf_t1: nat; (* Sealed cap to callee export table entry *)
            rf_t2: nat; 
            rf_s0: nat;
            rf_s1: nat;
            rf_a0 : nat;
            rf_a1 : nat;
            rf_a2 : nat;
            rf_a3 : nat;
            rf_a4 : nat;
            rf_a5 : nat;
          }.

        Definition SWITCHER_SEALED_ARG_REG := rf_t1.

        (* TODO: constrain spill slot size *)
        Class SWITCHER_PARAMS (rf: ConcreteRf) :=
          { SPILL_SLOT_cs0 : nat; (* < 4 *)
            SPILL_SLOT_cs1 : nat; (* < 4 *)
            SPILL_SLOT_pcc : nat; (* < 4 *)
            SPILL_SLOT_cgp : nat; (* < 4 *)
            (* SPILL_SLOT_SIZE : nat; (* #Bytes *) *)
            STACK_ENTRY_RESERVED_SPACE: nat;
            zeroByte: Byte;
            compartmentFailValue: list Byte;
            notEnoughStackValue: list Byte;
            exnDecode: ExnInfo -> (Bytes * Bytes) (* mcause * mtval *);
            capCursorOfBytes: Bytes -> Addr
          }.
        Definition SPILL_SLOT_SIZE := 4 * ISA_CAPSIZE_BYTES. 

        Definition rfidx :=
          {| rf_ra := 1; 
             rf_gp := 2;
             rf_sp := 3;
             rf_tp := 4;
             rf_t0 := 5;
             rf_t1 := 6;
             rf_t2 := 7;
             rf_s0 := 8;
             rf_s1 := 9;
             rf_a0 := 10;
             rf_a1 := 11;
             rf_a2 := 12;
             rf_a3 := 13;
             rf_a4 := 14;
             rf_a5 := 15 
          |}.

        (* Context {rfidx: ConcreteRf}. *)
        Context {switcher: SWITCHER_PARAMS rfidx}.
        Definition zeroBytes : list Byte := map (fun _ => zeroByte) (seq 0 ISA_CAPSIZE_BYTES). 

        Definition mtval exnInfo := snd (exnDecode exnInfo).
        Definition mcause exnInfo := fst (exnDecode exnInfo).

        (* The error handler returns a IRQ-enabling reverse sentry to
           the error handler return address of the switcher. *)
        Definition errorHandlerReturnCap : Cap :=
          setCapSealed ErrorHandlerReturnPCC (Some (inl RetEnableInterrupt)).

        (* After a compartment call, the switcher returns a backwards
           sentry to .Lswitcher_after_compartment_call. *)
        Definition switcherAfterCompartmentCallCap (istatus: InterruptStatus): Cap :=
          let sentry := match istatus with
                        | InterruptsEnabled => RetEnableInterrupt
                        | InterruptsDisabled => RetDisableInterrupt
                        end in 
          setCapSealed CompartmentReturnPCC (Some (inl sentry)).

        Record In_Switcher_Invariant
          (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
        { EE_Inv_Mode: InSystemMode st
        ; EE_Inv_SwitcherPCC: AddrsInSwitcherFootprint config (pcc st).(capAddrs)
        ; EE_Inv_fetchAddrs: fetchAddrsInBounds fetchAddrs st
        }.

        (* The switcher depends only on the thread's stack and read-only memory.
           TODO: scheduler? Could relax to make it depend on read-only memory + stack.
         *)
        Definition SwitcherMemEquivAtThread (tid: nat) (mem1 mem2: FullMemory) : Prop :=
          MemEquivalentAtThread tid mem1 mem2 /\
          SwitcherCodeUnchanged mem2.

        Definition ThreadStepOk st1 st2 :=
          exists ev, ThreadStep st1 (st2, ev).

        Section UnwindingStack.
          Definition BaseAddr (c: Cap) (addr: Addr) : Prop := 
            In addr c.(capAddrs) /\
            (forall a', In a' c.(capAddrs) -> addr <= a').

          Definition zeroedStack (base top: Addr) (mem: FullMemory) :=
            (forall addr, base <= addr < top ->
                     readByte mem addr = zeroByte /\
                     readTag mem (toCapAddr addr) = false).
 
          Definition unwindStackOk
            (csp: Cap) (mem: FullMemory) (mem': FullMemory) :=
            exists baseAddr,
            BaseAddr csp baseAddr /\
            (* Zero stack *)
            (zeroedStack baseAddr (csp.(capCursor) + SPILL_SLOT_SIZE) mem') /\
            (* Stack had permission to store in the range *)
            (forall addr, baseAddr < addr < (csp.(capCursor) + SPILL_SLOT_SIZE) ->
                     In addr csp.(capAddrs)) /\
            (* All other mem is unchanged. *)
            (forall addr, (baseAddr < addr < csp.(capCursor) + SPILL_SLOT_SIZE -> False) ->
                     readByte mem' addr = readByte mem addr /\
                     readTag mem' (toCapAddr addr) = readTag mem (toCapAddr addr)).

          (* TODO: check interrupt status *)
          (* TODO: permission to read stack *)
          (* TODO: CSR_MSHWM *)
          Definition PostRf_UnwindStack
            (tcsp: Cap) (* topmost trusted stack frame's csp *)
            (init_mem: FullMemory)
            (cgp: Cap)   (* cgp associated with error handler *)
            (ret0: CapOrBytes -> Prop)
            (ret1: CapOrBytes -> Prop)
            : RfSpecT :=
            let readCapAtCSPOffset offset :=
              readCap init_mem (toCapAddr (Nat.add tcsp.(capCursor) offset)) in 
            [ (rf_ra rfidx, eq (readCapAtCSPOffset SPILL_SLOT_pcc))
              (* TODO: check what ra is equal to? *)
            ; (rf_gp rfidx, eq (readCapAtCSPOffset SPILL_SLOT_cgp))
              (* Restore caller stack pointer and increment *)
            ; (rf_sp rfidx, eq (inl (updateCapCursor tcsp (Nat.add SPILL_SLOT_SIZE))))
            ; (rf_s0 rfidx, eq (readCapAtCSPOffset SPILL_SLOT_cs0))
            ; (rf_s1 rfidx, eq (readCapAtCSPOffset SPILL_SLOT_cs1))
            ; (rf_a0 rfidx, ret0)
            ; (rf_a1 rfidx, ret1)
            ].
  
          Definition PostRfSpec_UnwindStack
            (frame: TrustedStackFrame)
            (init_mem: FullMemory)
            (compartment: Compartment)
            (rf: RegisterFile)
            (ret0: CapOrBytes -> Prop)
            (ret1: CapOrBytes -> Prop)
            :=
            exists cgp, compartment.(compartmentCGP) = Some cgp /\
              RfSpec (PostRf_UnwindStack frame.(trustedStackFrame_CSP) init_mem cgp ret0 ret1)
              rf
              (eq (inr zeroBytes)).


          (* Ensure there's at least one stack frame left *)
          Definition Post_UnwindStackBase
            (ret0: RegisterFile -> CapOrBytes -> Prop)
            (ret1: RegisterFile -> CapOrBytes -> Prop)
            (tid: nat) (st_init: ThreadState) (st: ThreadState)
            : Prop :=
            exists frame frame' frames compartment exnInfo,
              let tcsp := frame.(trustedStackFrame_CSP) in
              trustedStack_frames (thread_trustedStack (sts st_init)) = frame::frame'::frames /\
              sc st = ({| thread_mepcc := MEPCC ;
                          thread_exceptionInfo := exnInfo;
                          thread_trustedStack := Build_TrustedStack (frame'::frames);
                          thread_alive := thread_alive (sts st_init)
                       |}, ints st_init) /\
              LookupExportTableCompartment config frame.(trustedStackFrame_calleeExportTable) = Some compartment /\
              (* mem *)
              unwindStackOk tcsp (mem st_init) (mem st) /\
              (* pcc *)
              (let readCapAtCSPOffset offset :=
                   readCap (mem st_init) (toCapAddr (tcsp.(capCursor) + offset)) in 
                 readCapAtCSPOffset SPILL_SLOT_pcc = inl (pcc st)) /\
              (* rf *)
              (PostRfSpec_UnwindStack frame (mem st_init) compartment (rf st)
                                      (ret0 (rf st_init)) (ret1 (rf st_init))
              ).

          Definition Post_UnwindStackForced
            (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            Post_UnwindStackBase
              (fun rf_init => eq (inr compartmentFailValue))
              (fun rf_init => eq (inr zeroBytes))
              tid st_init st.

          Definition Post_UnwindStackReturnOk
            (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            Post_UnwindStackBase
              (fun rf_init v => RegProp rf_init (rf_a0 rfidx) (eq v))
              (fun rf_init v => RegProp rf_init (rf_a1 rfidx) (eq v))
              tid st_init st.

          Definition ThreadDead (st: ThreadState) :=
            (sts st).(thread_alive) = ThreadDead.

          Definition SwitcherEntry_Invariant
            (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            forall mem',
            SwitcherMemEquivAtThread tid (mem st_init) mem' ->
            In_Switcher_Invariant tid st_init ((fst (uc st), mem'), sc st).

        End UnwindingStack.


        Section ExceptionHandler.
          (* While a thread is in the  the switcher:
             - The thread is in system mode.
             - The PCC points to addresses in the switcher.
               - TODO: scheduler??? could relax and allow library calls
             - Fetch succeeds.
           *)
          Definition ExceptionEntry_Invariant
            (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            SwitcherEntry_Invariant tid st_init st.

          (* Initially, the pcc should be equal to the user's MEPCC
             (which points to the exception entry point of the switcher)
             and the invariant should hold, for any memory that is
             equivalent at stack+switcher addresses.
           *)
          Record ExceptionEntry_Pre (tid: nat) (st: ThreadState) : Prop :=
            { EEPre_PCCAddr: pcc st = MEPCC 
            ; EEPre_TrustedStack: ValidTrustedStack (sts st).(thread_trustedStack)
            ; EEPre_Invariant: ExceptionEntry_Invariant tid st st 
            }.

          (* ---------------- POSTCONDITION ----------------------- *)
          (* If the switcher returns back to user mode after an exception, then either
             1) There was an error handler and the PCC points to the error handler entrypoint, and
                - ra: backwards sentry to switcher's error handler return
                - gp: target compartment cgp
                - sp: target compartment stack pointer at time of invocation
                - a0,a1,a2:
                  i) stackful: a0 = invocation stack with register spill frame there and above
                              a1 = mcause
                              a2 = mtval
                  ii) stackless: a0 = mcause
                               a1 = mtval
                               a2 = zero
                - mepcc initially contained PCC at exception time. spill onto stack
             2) An error handler does not exist and we are not the
                bottommost frame. We unwind the stack and return to the
                previous caller.
                - Zero the stack
                - Pop a frame from the trusted stack, leaving registers
                  in the state expected by the caller of a
                  cross-compartment call
                  + pcc := csp[SPILL_SLOT_PCC]
                  + cgp := csp[SPILL_SLOT_cgp]
                  + s0 := csp[SPILL_SLOT_cs0]
                  + s1 := csp[SPILL_SLOT_cs1]
                  + a0 = -ECOMPARTMENTFAIL
                  + other registers are zero
             3) An error handler does not exist and we are at the bottommost frame.
                - Defer interrupts, signal to the scheduler that the
                  current thread is finished.
                - TODO: restart a finished thread?
           *)

          Definition ExceptionEntry_PostRf_Stackful
            (tcsp: Cap) (* topmost trusted stack frame's csp *)
            (cgp: Cap)   (* cgp associated with error handler *)
            (exnInfo: ExnInfo)
            : RfSpecT :=
            [ (rf_ra rfidx, eq (inl errorHandlerReturnCap))
              ; (rf_gp rfidx, eq (inl cgp))
              ; (rf_sp rfidx, eq (inl tcsp))
              ; (rf_a0 rfidx, eq (inl tcsp))
              ; (rf_a1 rfidx, eq (inr (mcause exnInfo)))
              ; (rf_a2 rfidx, eq (inr (mtval  exnInfo)))
            ].
  
          Definition ExceptionEntry_PostRfSpec_Stackful
            (frame: TrustedStackFrame)                      
            (compartment: Compartment)
            (exnInfo: ExnInfo)
            (rf: RegisterFile) :=
            exists cgp, compartment.(compartmentCGP) = Some cgp /\
            RfSpec (ExceptionEntry_PostRf_Stackful frame.(trustedStackFrame_CSP) cgp exnInfo) rf
                   (eq (inr zeroBytes)).
  
          Definition ExceptionEntry_PostRf_Stackless
            (tcsp: Cap) (* topmost trusted stack frame's csp *)
            (cgp: Cap)   (* cgp associated with error handler *)
            (exnInfo: ExnInfo) 
            : RfSpecT :=
            [ (rf_ra rfidx, eq (inl errorHandlerReturnCap))
            ; (rf_gp rfidx, eq (inl cgp))
            ; (rf_sp rfidx, eq (inl tcsp))
            ; (rf_a0 rfidx, eq (inr (mcause exnInfo)))
            ; (rf_a1 rfidx, eq (inr (mtval  exnInfo)))
              (* a2 and other regs are zero *)
            ].

          Definition ExceptionEntry_PostRfSpec_Stackless
            (frame: TrustedStackFrame)                      
            (compartment: Compartment)
            (exnInfo: ExnInfo)
            (rf: RegisterFile) :=
            exists cgp, compartment.(compartmentCGP) = Some cgp /\
            RfSpec (ExceptionEntry_PostRf_Stackless frame.(trustedStackFrame_CSP) cgp exnInfo) rf
                   (eq (inr zeroBytes)).
  

          Definition ExceptionEntry_PostOk_Common
            (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            exists exnInfo',
              sc st = ({| thread_mepcc := MEPCC;
                          thread_exceptionInfo := exnInfo';
                          thread_trustedStack := thread_trustedStack (sts st_init);
                          thread_alive := thread_alive (sts st_init)
                       |}, InterruptsEnabled).

          Definition ValidErrorHandlerPCC (handlerT: handlerType) (compartment: Compartment) (pcc: Cap) : Prop :=
            exists offset,
              In (Build_ErrorHandler offset handlerT) compartment.(compartmentErrorHandlers) /\
              pcc = updateCapCursor compartment.(compartmentPCC) (Nat.add offset).

          Definition NREGS_TO_SPILL := 15.
          Definition SPILL_FRAME_SIZE := (NREGS_TO_SPILL + 1) * ISA_CAPSIZE_BYTES.

          (* Stack: 
           * - Only part of memory modified should be the stack
           * - stack should have a spill frame right above the tcsp
           * - TODO: what if CSP does not have Cap permission
           *)
          Definition spillRegisterFileForErrorHandlerOk 
            (csp: Cap) (rf: RegisterFile) (mepcc: Cap) (mem: FullMemory) (mem': FullMemory) :=
            (* Store PCC (mepcc) with clear tagged *)
            readCap mem' (toCapAddr csp.(capCursor)) = inr (capToBytes mepcc) /\
            (* Store all (15) registers *)
            Forall (fun idx => RegProp rf idx (eq (readCap mem' (toCapAddr (csp.(capCursor) + (idx * ISA_CAPSIZE_BYTES)))))) (seq 1 NREGS_TO_SPILL) /\
            (* Stack had permission to store in the range *)
            (forall addr, In addr (seq (csp.(capCursor)) SPILL_FRAME_SIZE) ->
                     In addr csp.(capAddrs)) /\
            (* All other mem is unchanged. *)
            (forall addr, (csp.(capCursor) < addr < csp.(capCursor) + SPILL_FRAME_SIZE -> False) ->
                     readByte mem' addr = readByte mem addr /\
                     readTag mem' (toCapAddr addr) = readTag mem (toCapAddr addr)).
         
          Definition increment_errorCounter (f: TrustedStackFrame) :=
            {| trustedStackFrame_CSP := f.(trustedStackFrame_CSP);
               trustedStackFrame_calleeExportTable := f.(trustedStackFrame_calleeExportTable);
               trustedStackFrame_errorCounter := S f.(trustedStackFrame_errorCounter)
            |}.
 
          Definition ExceptionEntry_Post_Stackful
            (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            (exists exnInfo' frame frames compartment mem',
              trustedStack_frames (thread_trustedStack (sts st_init)) = frame::frames /\
              sc st = ({| thread_mepcc := MEPCC;
                          thread_exceptionInfo := exnInfo';
                          thread_trustedStack := Build_TrustedStack ((increment_errorCounter frame)::frames);
                          thread_alive := thread_alive (sts st_init)
                       |}, InterruptsEnabled) /\
              LookupExportTableCompartment config frame.(trustedStackFrame_calleeExportTable) = Some compartment /\
              (* TODO: untrusted CSP? *)
              spillRegisterFileForErrorHandlerOk (trustedStackFrame_CSP frame) (rf st) (mepcc st) (mem st) (mem') /\
              (ValidErrorHandlerPCC Stackful compartment (pcc st)) /\
              (ExceptionEntry_PostRfSpec_Stackful frame compartment (sts st).(thread_exceptionInfo)) (rf st)
            ).
  
          Definition ExceptionEntry_Post_Stackless
            (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            (exists exnInfo' frame frames compartment mem',
              trustedStack_frames (thread_trustedStack (sts st_init)) = frame::frames /\
              sc st = ({| thread_mepcc := MEPCC;
                          thread_exceptionInfo := exnInfo';
                          thread_trustedStack := Build_TrustedStack ((increment_errorCounter frame)::frames);
                          thread_alive := thread_alive (sts st_init) 
                       |}, InterruptsEnabled) /\
              LookupExportTableCompartment config frame.(trustedStackFrame_calleeExportTable) = Some compartment /\
              mem' = mem st (* memory is unchanged *) /\
              (ValidErrorHandlerPCC Stackless compartment (pcc st)) /\
              (ExceptionEntry_PostRfSpec_Stackless frame compartment (sts st).(thread_exceptionInfo)) (rf st)).
     
          (* TODO: case for final frame? *)
          Record ExceptionEntry_Post (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            { EEPost_Mode: ~(InSystemMode st)
            ; EEPost_Cases: ExceptionEntry_Post_Stackful tid st_init st
                            \/ ExceptionEntry_Post_Stackless tid st_init st
                            \/ Post_UnwindStackForced tid st_init st
                            \/ ThreadDead st
            }.
  
  
          (* For all sequences of thread steps, the thread stays in *)
          (* system mode until it returns to user mode with the stated postcondition. *)
          (* - TODO: eventually it always returns? *)
          Definition ExceptionHandlerOk :=
           forall tid init,
            ExceptionEntry_Pre tid init ->
            Combinators.until
              ThreadStepOk
              (fun st => InSystemMode st /\ ExceptionEntry_Invariant tid init st)
              (fun st => ~(InSystemMode st) /\ ExceptionEntry_Post tid init st)
              init.

          (* TODO: lift thread-local property to machine *)
        End ExceptionHandler.

        (* Relaxing and allowing tags to be dropped here. *)
        Definition readMemTagCapOk (mem: FullMemory) (authCap: Cap) (res: CapOrBytes) : Prop :=
          authCap.(capSealed) = None /\
          In Perm.Load authCap.(capPerms) /\ 
          Subset (seq authCap.(capCursor) ISA_CAPSIZE_BYTES) authCap.(capAddrs) /\
          match readCap mem authCap.(capCursor) with
          | inl cap => 
             (In Perm.Cap authCap.(capPerms) ->
              res = inl (attenuate authCap cap)) /\
             ((In Perm.Cap authCap.(capPerms) -> False) ->
              res = inr (capToBytes cap))
          | inr bytes =>
             res = inr bytes 
          end.

        Section ExceptionReturn.
          Definition ExceptionReturn_Invariant (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            SwitcherEntry_Invariant tid st_init st.

          Record ExceptionReturn_Pre (tid: nat) (st: ThreadState) : Prop :=
          { ERPre_PCCAddr: pcc st = ErrorHandlerReturnPCC
          ; ERPre_TrustedStack: ValidTrustedStack (sts st).(thread_trustedStack)
          ; ERPre_Invariant: ExceptionReturn_Invariant tid st st
          }.
 
          Definition capCursorOfCapOrBytes (v: CapOrBytes) := 
            match v with
            | inl cap => cap.(capCursor)
            | inr bytes => capCursorOfBytes bytes 
            end.
                             
          (* Why does the code use the CSP from the argument rather than the trusted CSP? *)
          (* TODO!!!: needs interrupts disabled to install context; can read globals *)
          (* a0 = 0: argument is zero *)
          (* TODO: need to add trusted stack spill frame *)
          Definition ExceptionEntry_PostInstallContext
            (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            (* Precondition *)
            (RegProp (rf st_init) (rf_a0 rfidx) (eq (inr zeroBytes))) /\
            (* Postcondition *)
            exists exnInfo' cspCap frame frames compartment,
              trustedStack_frames (thread_trustedStack (sts st_init)) = frame::frames /\
              LookupExportTableCompartment config frame.(trustedStackFrame_calleeExportTable) = Some compartment /\
              RegProp (rf st_init) (rf_sp rfidx) (eq (inl cspCap)) /\
              sc st = ({| thread_mepcc := MEPCC;
                          thread_exceptionInfo := exnInfo';
                          thread_trustedStack := thread_trustedStack (sts st_init);
                          thread_alive := thread_alive (sts st_init)  
                       |}, ints st_init (* TODO: want to restore mstatus *)) /\
               (* mem is unchanged *)
               mem st = mem st_init /\
               (* csp is untrusted *)
               ValidCSP cspCap /\ (* TODO!!! not true in current switcher. *)
               (* pcc is compartment PCC set to address of mepcc stored on stack *)
               (exists mepcc, readMemTagCapOk (mem st_init) cspCap mepcc /\
                         pcc st = setCapCursor compartment.(compartmentPCC) (capCursorOfCapOrBytes mepcc)) /\
               (* load register file *)
               Forall (fun idx => RegProp (rf st) idx
                                       (readMemTagCapOk (mem st_init) (updateCapCursor cspCap (Nat.add (idx * ISA_CAPSIZE_BYTES)))))
                      (seq 1 NREGS_TO_SPILL).

          Record ExceptionReturn_Post (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            { ERPost_Mode: ~(InSystemMode st)
            ; ERPost_Cases: 
                (* Note: switcher will be rewritten. TODO: decrement fault path? Disable interrupts? *)
                ExceptionEntry_PostInstallContext tid st_init st \/
                Post_UnwindStackForced tid st_init st \/
                ThreadDead st
            }.

          Definition ExceptionReturnOk :=
           forall tid init,
            ExceptionReturn_Pre tid init ->
            Combinators.until
              ThreadStepOk
              (fun st => InSystemMode st /\ ExceptionReturn_Invariant tid init st)
              (fun st => ~(InSystemMode st) /\ ExceptionReturn_Post tid init st)
              init.
         
        End ExceptionReturn.

        Section CompartmentCall.
          Definition CompartmentCall_Invariant (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            SwitcherEntry_Invariant tid st_init st.

          Record CompartmentCall_Pre (tid: nat) (st: ThreadState) : Prop :=
          { CCallPre_PCCAddr: pcc st = CompartmentCallPCC
          ; CCallPre_TrustedStack: ValidTrustedStack (sts st).(thread_trustedStack)
          ; CCallPre_Invariant: CompartmentCall_Invariant tid st st
          (* ; CCallPre_RA: *) (* caller return address, because we entered via a forward sentry *)
          }.
          Definition ZeroArg (numArgs: nat) (regArgNum: nat) (init_rf: RegisterFile) (regIdx: nat) : CapOrBytes -> Prop :=
            fun v => RegProp init_rf regIdx (fun old => v = if Nat.leb numArgs regArgNum then
                                                              inr zeroBytes
                                                            else old).
          Definition CompartmentCall_PostRf_Ok
            (istatus: InterruptStatus) 
            (init_rf: RegisterFile)
            (* (tcsp: Cap) (* topmost trusted stack frame's csp *) *)
            (cgp: Cap)   (* cgp associated with new compartment *) 
            (csp: Cap)   (* csp associated with new compartment *) 
            (numArgs: nat)
            (* (exnInfo: ExnInfo) *)
            : RfSpecT :=
            [ (rf_ra rfidx, eq (inl (switcherAfterCompartmentCallCap istatus)))
            ; (rf_gp rfidx, eq (inl cgp))
            ; (rf_sp rfidx, eq (inl csp))    
            ; (rf_a0 rfidx, ZeroArg numArgs 0 init_rf (rf_a0 rfidx))
            ; (rf_a1 rfidx, ZeroArg numArgs 1 init_rf (rf_a1 rfidx))
            ; (rf_a2 rfidx, ZeroArg numArgs 2 init_rf (rf_a2 rfidx))
            ; (rf_a3 rfidx, ZeroArg numArgs 3 init_rf (rf_a3 rfidx))
            ; (rf_a4 rfidx, ZeroArg numArgs 4 init_rf (rf_a4 rfidx))
            ; (rf_a5 rfidx, ZeroArg numArgs 5 init_rf (rf_a5 rfidx))
            ; (rf_t0 rfidx, ZeroArg numArgs 6 init_rf (rf_t0 rfidx))
            ].

         (* (* TODO: alignment; check underflow  *) *)
         (* (* Alternatively, could define in terms of restricting the initial csp *) *)
         Definition postCompartmentCallCSP (init_csp: Cap) (newBase: Addr): Cap :=
           let newCursor := newBase - STACK_ENTRY_RESERVED_SPACE in
           mkCSP' (filter (Nat.ltb newBase) init_csp.(capAddrs)) newCursor.
          Definition CompartmentCall_PostRfSpec_Ok
            (init_rf: RegisterFile)                       
            (entry: ExportEntry)
            (csp: Cap)
            (compartment: Compartment) 
            (rf: RegisterFile) :=
            exists cgp , compartment.(compartmentCGP) = Some cgp /\
            RfSpec (CompartmentCall_PostRf_Ok entry.(exportEntryInterruptStatus) init_rf 
                                              cgp csp entry.(exportEntryNumArgs))
                   rf 
                   (eq (inr zeroBytes)).

      
          (* ---------------- POSTCONDITION ----------------------- *)
          (* If the switcher returns back to user mode after an compartment call, then either
           * 1) The call succeeded:
                - initial csp was ok
                - initial t1 points to sealed export table entry
                - spill registers below where csp points
                - add new frame to trusted stack (csp at time of invocation - spill slots)
                - chop off and zero stack from newCSPBase to base 
           * 2) Not enough stack; return to caller with a0 = -ENOTENOUGHSTACK; a1 = 0
                TODO: current code spills and then reloads registers? 
           * 3) Invalid CSP (or otherwise?): unwind the stack
           *)

          Definition compartmentCallStackOk 
            (csp: Cap) (mem: FullMemory) (mem': FullMemory) :=
            exists baseAddr,
            BaseAddr csp baseAddr /\
            (* Zero stack *)
            (forall addr, In addr csp.(capAddrs) ->
                     readByte mem addr = zeroByte /\
                     readTag mem (toCapAddr addr) = false) /\
            (* All other mem is unchanged. *)
            (forall addr, (In addr csp.(capAddrs) -> False) ->
                     readByte mem' addr = readByte mem addr /\
                     readTag mem' (toCapAddr addr) = readTag mem (toCapAddr addr)).

          (* TODO: check for stack size *)
          Definition CCall_Post_Ok
            (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            (exists sealedCapToExportTable compartment entry exnInfo' init_csp,  
              ValidCSP init_csp /\ 
              (RegProp (rf st_init) (SWITCHER_SEALED_ARG_REG rfidx) (eq (inl sealedCapToExportTable))) /\ 
              (sealedCapToExportTable.(capSealed) = Some (inr config.(configSwitcher).(Switcher_key))) /\
              let unsealedCapToExportTable := setCapSealed sealedCapToExportTable None in
              LookupExportTableCompartmentAndEntry config unsealedCapToExportTable = Some (compartment, entry) /\
              RegProp (rf st_init) (rf_sp rfidx) (eq (inl init_csp)) /\
              let newTCSPBase := init_csp.(capCursor) - SPILL_SLOT_SIZE  in
              let newTCSP := setCapCursor init_csp newTCSPBase in 
              let newFrame := {| trustedStackFrame_CSP := newTCSP;
                                 trustedStackFrame_calleeExportTable := unsealedCapToExportTable;
                                 trustedStackFrame_errorCounter := 0
                              |} in 
              sc st = ({| thread_mepcc := MEPCC;
                          thread_exceptionInfo := exnInfo';
                          thread_trustedStack := Build_TrustedStack (newFrame::(sts st).(thread_trustedStack).(trustedStack_frames));
                          thread_alive := thread_alive (sts st_init) 
                       |}, entry.(exportEntryInterruptStatus)) /\
              (* PCC *)
              pcc st = updateCapCursor compartment.(compartmentPCC) (Nat.add entry.(exportEntryOffset)) /\
              (* RF *)
              let csp' := (postCompartmentCallCSP init_csp newTCSPBase)  in
              (CompartmentCall_PostRfSpec_Ok (rf st_init) entry csp' compartment (rf st)) /\
              (* MEM *)
              compartmentCallStackOk newTCSP (mem st_init) (mem st)).

          (* TODO: check this. Also too strong.
             We could relax this to say they're all caller-reachable caps or values 
           *)
          Definition CCall_PostRf_NotEnoughStack
            (rf_init: RegisterFile)
            : RfSpecT :=
            let eq_rf_init idx := fun v => RegProp rf_init (rf_sp rfidx) (eq v) in 
            [ (rf_ra rfidx, eq_rf_init (rf_ra rfidx)) (* TODO *)
            ; (rf_gp rfidx, eq_rf_init (rf_gp rfidx))
            ; (rf_sp rfidx, eq_rf_init (rf_sp rfidx))
            ; (rf_tp rfidx, eq_rf_init (rf_tp rfidx))
            ; (rf_t0 rfidx, eq_rf_init (rf_t0 rfidx))
            ; (rf_t1 rfidx, eq_rf_init (rf_t1 rfidx))
            ; (rf_t2 rfidx, eq_rf_init (rf_t2 rfidx))
            ; (rf_s0 rfidx, eq_rf_init (rf_s0 rfidx))
            ; (rf_s1 rfidx, eq_rf_init (rf_s1 rfidx))
            ; (rf_a0 rfidx, eq (inr notEnoughStackValue))
            ; (rf_a1 rfidx, eq (inr zeroBytes))
            ; (rf_a2 rfidx, eq_rf_init (rf_a2 rfidx))
            ; (rf_a3 rfidx, eq_rf_init (rf_a3 rfidx))
            ; (rf_a4 rfidx, eq_rf_init (rf_a4 rfidx))
            ; (rf_a5 rfidx, eq_rf_init (rf_a5 rfidx))
            ].

          (* Trusted stack and interrupt status is not changed. *)
          Definition CCall_Post_NotEnoughStack
            (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
            (exists exnInfo',
              sc st = ({| thread_mepcc := MEPCC;
                          thread_exceptionInfo := exnInfo';
                          thread_trustedStack := thread_trustedStack (sts st_init);
                          thread_alive := thread_alive (sts st_init)  
                       |}, ints st_init)) /\
            (* mem is unchanged *)
            mem st = mem st_init /\
            (* TOOD: pcc points to initial ra? *)
            (RegProp (rf st_init) (rf_ra rfidx) (eq (inl (pcc st)))) /\ 
            (* rf is mostly unchanged, other than return values *)
            RfSpec (CCall_PostRf_NotEnoughStack (rf st_init)) (rf st) (eq (inr zeroBytes)).

          Record CompartmentCall_Post (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
          { CCPost_Mode: ~(InSystemMode st)
          ; CCPost_Cases: CCall_Post_Ok tid st_init st \/
                          CCall_Post_NotEnoughStack tid st_init st \/
                          Post_UnwindStackForced tid st_init st \/
                          ThreadDead st
          }.

          (* For all sequences of thread steps, the thread stays in *)
          (* system mode until it returns to user mode with the stated postcondition. *)
          (* - TODO: eventually it always returns? *)
          Definition CompartmentCallOk :=
           forall tid init,
            CompartmentCall_Pre tid init ->
            Combinators.until
              ThreadStepOk
              (fun st => InSystemMode st /\ CompartmentCall_Invariant tid init st)
              (fun st => ~(InSystemMode st) /\ CompartmentCall_Post tid init st)
              init.

        End CompartmentCall.


        (* Pop a frame from the trusted stack, leaving registers in
           the state expected by the caller of a cross-compartment
           call. The callee is responsible for zeroing unused return
           registers; the switcher will zero other non-return argument
           and temporary registers.
        *)
        Section CompartmentReturn.
          Definition CompartmentReturn_Invariant (tid: nat) (st_init: ThreadState) (st: ThreadState) :=
            SwitcherEntry_Invariant tid st_init st.

          Record CompartmentReturn_Pre (tid: nat) (st: ThreadState) : Prop :=
          { CRetReturn_PCCAddr: pcc st = CompartmentCallPCC
          ; CRetReturn_TrustedStack: ValidTrustedStack (sts st).(thread_trustedStack)
          ; CRetReturn_Invariant: CompartmentCall_Invariant tid st st
          }.

          Record CompartmentReturn_Post (tid: nat) (st_init: ThreadState) (st: ThreadState) : Prop :=
          { CRetPost_Mode: ~(InSystemMode st)
          ; CRetPost_Cases: Post_UnwindStackReturnOk tid st_init st \/
                            ThreadDead st
          }.

          Definition CompartmentReturnOk :=
          forall tid init,
           CompartmentReturn_Pre tid init ->
           Combinators.until
             ThreadStepOk
             (fun st => InSystemMode st /\ CompartmentReturn_Invariant tid init st)
             (fun st => ~(InSystemMode st) /\ CompartmentReturn_Post tid init st)
             init.
         
        End CompartmentReturn.
      
      (* (* We want to define the behavior of the switcher as a function *)
      (*    of thread-local state (register file, CSP-region of memory, *)
      (*    system thread state) + read-only switcher state. We want to *)
      (*    guarantee disjointness of other threads updates from *)
      (*    thread-local memory regions. *)

      (*    Then if we jump to the switcher's exception handler: *)
      (*    - For some sequence of thread steps, P UNTIL Q *)
      (*      - Q (Post): returns to usermode /\ R holds *)
      (*      - P (Invariant): - it should act as a function of thread-local + read-only switcher state *)
      (*           - not usermode  *)
      (*      - R: post condition of exception handler, in terms of initial state *)
      (*        - A good exception handler was found and we jumped to it *)
      (*    - No guarantee of availability unless we add EVENTUALLY Q *)
      (*  *) *)

      (* (* TODO: fetchAddrs *) *)
     
   
      End WithSwitcherParams.
    End WithConfig.
  End WithContext.
End SwitcherProperty.
(* If a (malicious) compartment is not transitively-reachable from a
   protected compartment, then it should never have access to the
   protected compartment's memory regions.

   This module just validates the initial configuration setup, by
   proving that isolated compartments do not share addresses,
   sentries, or switcher-sealed data caps in the initial state.
 *)
Module CompartmentIsolationValidation.
  Import ListNotations.
  Import Configuration.
  Import Separation.
  Section WithContext.
    Context [ISA: ISA_params].
    Context {machineTypeParams: MachineTypeParams}.
    Context {capEncodeDecode: CapEncodeDecode}.
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {pccNotInBounds : EXNInfo}.
    Notation AddrOffset := nat (only parsing).
    Notation PCC := Cap (only parsing).
    Notation State := (Machine * Trace)%type.
    Context {LookupExportTableCompartmentId: Config -> Cap -> option (nat * nat)}.
    Notation ValidInitialState := (@ValidInitialState _ _ _ LookupExportTableCompartmentId).
    Notation ValidInitialThread := (@ValidInitialThread _ _ _ LookupExportTableCompartmentId).

    (* Compartments are connected on the audit graph.
       - Compartments can share libraries without being connected.
       - C1/L1 --> C2/L2 if c1/l1 can call c2/l2 via a sealed cap (cross-compartment calls add a bidirectionaly edge on the graph)
       - C1/L1 --> L1 if c1/l1 can call l1 via a sentry to a library function 
       - Reflexive
       - C1 --> C2 if C2 --> C1 (if C1 can reach C2, then C2 can reach C1)
       This allows C1 --> L1 and C2 --> L1, but not C1 --> C2 (libraries can be shared)
       But if C1 --> L1 <--> C2, then C1 <--> C2.
     *)
    Inductive ReachableCompartment : Config -> nat -> nat -> Prop :=
    | ReachableCaller:
        forall config idx1 idx2 c1 cap addr,
          nth_error config.(configCompartments) idx1 = Some c1 ->
          In (ImportEntry_SealedCapToExportEntry cap) c1.(compartmentImports) ->
          In addr cap.(capAddrs) ->
          AddrHasProvenance config addr (Provenance_Compartment idx2) ->
          ReachableCompartment config idx1 idx2
    | ReachableCallee:
        forall config idx1 idx2 c1 cap addr,
          nth_error config.(configCompartments) idx1 = Some c1 ->
          In (ImportEntry_SealedCapToExportEntry cap) c1.(compartmentImports) ->
          In addr cap.(capAddrs) ->
          AddrHasProvenance config addr (Provenance_Compartment idx2) ->
          ReachableCompartment config idx2 idx1
    | ReachableLibrary:
        forall config idx1 idx2 c1 cap addr,
          nth_error config.(configCompartments) idx1 = Some c1 ->
          In (ImportEntry_SentryToLibraryFunction cap) c1.(compartmentImports) ->
          In addr cap.(capAddrs) ->
          AddrHasProvenance config addr (Provenance_Compartment idx2) ->
          ReachableCompartment config idx1 idx2
    | ReachableCompartmentRefl:
        forall config idx,
          idx < length config.(configCompartments) ->
          ReachableCompartment config idx idx
    | ReachableCompartmentTrans:
        forall config idx1 idx2 idx3,
          ReachableCompartment config idx1 idx2 ->
          ReachableCompartment config idx2 idx3 ->
          ReachableCompartment config idx1 idx3.

    Definition threadHasSystemPerm (t: Thread) : bool :=
      existsb (Perm.t_beq Perm.System)
           (t.(thread_userState).(thread_pcc).(capPerms)).
            
    Definition ThreadInUserCompartment (config: Config) (mem: FullMemory) (t: Thread) (cid: nat) : Prop :=
      (~ ThreadHasSystemPerm t) /\
      exists frame eid,
        hd_error t.(thread_systemState).(thread_trustedStack).(trustedStack_frames) = Some frame /\
        LookupExportTableCompartmentId config frame.(trustedStackFrame_calleeExportTable) = Some (cid, eid).

    Definition MutuallyIsolatedCompartment (config: Config) (idx1 idx2: nat) : Prop :=
      exists c1 c2,
        nth_error config.(configCompartments) idx1 = Some c1 /\
        nth_error config.(configCompartments) idx2 = Some c2 /\
        isLibrary c1 = false /\
        isLibrary c2 = false /\
          (ReachableCompartment config idx1 idx2 -> False).

    Section WithConfig.
      Variable config: Config.
      Variable (pf_wf_config: WFConfig config).

      (* Properties that imply isolation:
         - Mutually isolated compartments at the start of the world
           should remain mutually isolated.
           - The addresses (and therefore caps) reachable from the PCC
             and CGP of mutually isolated compartments should be isolated.
           - The sentries reachable from PCC and CGP of mutually
             isolated compartments should be isolated
           - The "sealedCapToExportEntries" 
             reachable from PCC/CGP should be isolated
         - The caps reachable from user-mode threads in a compartment should follow the above restrictions
         Extra invariants:
         - Only the switcher should have the unsealing key to sealedCapToExportEntries

         NB: for inductive proof, we likely want make these transitively closed properties.
       *)
      Definition AddrsIsolatedFromCompartment
        (mem: FullMemory) (srcCaps: list Cap) (cid: nat): Prop :=
        (forall addr,
           ReachableRWXAddr mem srcCaps addr ->
           AddrInCompartment config cid addr ->
           False).
      Definition SentriesIsolatedFromCompartment
        (mem: FullMemory) (srcCaps: list Cap) (cid: nat): Prop :=
        (forall cap addr,
            ReachableCap mem srcCaps cap ->
            isSentry cap = true ->
            In addr cap.(capAddrs) ->
            AddrHasProvenance config addr (Provenance_Compartment cid) ->
            False).
      Definition SealedDataCapsIsolatedFromCompartment
        (mem: FullMemory) (srcCaps: list Cap) (cid: nat): Prop :=
        (forall cap addr,
            ReachableCap mem srcCaps cap ->
            cap.(capSealed) = Some (inr config.(configSwitcher).(Switcher_key)) ->
            In addr cap.(capAddrs) ->
            AddrHasProvenance config addr (Provenance_Compartment cid) ->
            False).

      Definition IsolatedFromCompartment
        (mem: FullMemory) (srcCaps: list Cap) (cid: nat) : Prop :=
        AddrsIsolatedFromCompartment mem srcCaps cid /\
        SentriesIsolatedFromCompartment mem srcCaps cid /\
        SealedDataCapsIsolatedFromCompartment mem srcCaps cid.

      Definition CompartmentIsolation (m: Machine) : Prop :=
        forall idx1 idx2 c1 c2,
          idx1 <> idx2 ->
          MutuallyIsolatedCompartment config idx1 idx2 ->
          nth_error config.(configCompartments) idx1 = Some c1 ->  
          nth_error config.(configCompartments) idx2 = Some c2 ->
          IsolatedFromCompartment m.(machine_memory)
                                  (capsOfCompartment c1) idx2.                                       
      Definition CompartmentIsolatedThreads (m: Machine) : Prop :=
        forall idx1 idx2,
        idx1 <> idx2 ->
        MutuallyIsolatedCompartment config idx1 idx2 ->
        forall thread,
        In thread m.(machine_threads) ->
        ThreadInUserCompartment config m.(machine_memory) thread idx1 ->
        IsolatedFromCompartment m.(machine_memory)
                                (capsOfUserTS thread.(thread_userState))
                                idx2.

      Definition PIsolation (st: State) : Prop :=
        CompartmentIsolatedThreads (fst st).


      Record InitialProperty' (st: State) : Prop :=
        { Inv_UserMode: UserModeInvariant config (fst st)
        ; Inv_CompartmentIsolation: CompartmentIsolation (fst st)
        ; Inv_IsolatedThreads: CompartmentIsolatedThreads (fst st)
        }.                                                           
      
      Definition InitialProperty (st: State) : Prop :=
        GlobalInvariant config (fst st) /\
          InitialProperty' st.

      Ltac simplify_invariants :=
        repeat match goal with
          | H: GlobalInvariant _ ?m,
              H1: nth_error (machine_threads ?m) _ = Some ?thread
            |- ValidRf (thread_rf (thread_userState ?thread)) =>
              eapply GlobalInvariantImpliesValidRf with (1 := H) (2 := H1)
          end.

      Ltac init_invariant_proof :=
        repeat match goal with
        | H: WfGeneralInst ?generalInst,
          H1: ?generalInst _ _ = Ok _ |- _=>
            let Hok := fresh "HgeneralOk" in
            mark (MkMark "generalInstOkCommon");
            specialize generalInstOkCommon with (1 := H) (2 := H1) as Hok;
            assert_pre_and_specialize Hok; [simplify_invariants | ];
            cbn in Hok; destruct_products
        | H : InitialProperty'  _ |- _ =>
            mark (MkMark "InvCompartmentIsolation");
            let H' := fresh "HCompartmentIsolation" in 
            pose proof (Inv_CompartmentIsolation _ H) as H';
            cbv [CompartmentIsolation] in H'
        | H : InitialProperty'  _ |- _ =>
            mark (MkMark "InvIsolatedThreads");
            let H' := fresh "HIsolatedThreads" in 
            pose proof (Inv_IsolatedThreads _ H) as H';
            cbv [CompartmentIsolatedThreads] in H'
        | H : InitialProperty' _ |- _ =>
            mark (MkMark "InvUserMode");
            let H' := fresh "HUserMode" in 
            pose proof (Inv_UserMode _ H) as H'
        end.

      Lemma ThreadInUserCompartmentDoesNotHaveSystemPerm:
        forall config mem thread id,
          ThreadInUserCompartment config mem thread id ->
          ThreadHasSystemPerm thread ->
          False.
      Proof.
        cbv[ThreadInUserCompartment]. intros. destruct_products. congruence.
      Qed.

      Lemma ExceptionStepOk__User :
        forall m tr m' thread exn status,
          GlobalInvariant config m ->
          InitialProperty' (m, tr) ->
          GlobalInvariant config m' ->
          (forall n : nat,
              n <> machine_curThreadId m ->
              nth_error (machine_threads m') n = nth_error (machine_threads m) n) ->
          nth_error (machine_threads m) (machine_curThreadId m) = Some thread ->
          (~ThreadHasSystemPerm thread) ->
          nth_error (machine_threads m') (machine_curThreadId m) =
            Some (Build_Thread
                    (Build_UserThreadState
                       (thread_rf (thread_userState thread))
                       (thread_mepcc (thread_systemState thread)))
                    (Build_SystemThreadState
                       (thread_pcc (thread_userState thread))
                       exn 
                       (thread_trustedStack (thread_systemState thread))
                       status 
                    )
              ) ->
          machine_memory m = machine_memory m' ->
          InitialProperty' (m',(Ev_SameThread (machine_curThreadId m) Ev_Exception::tr)).
      Proof.
        intros * hginv hinv hginv' hsame hthread hmode huserhupdate hMemEq.
        init_invariant_proof. cbn [fst] in *.
        rewrite hMemEq in *.
        assert (CompartmentIsolatedThreads m') as hiso_thread.
        { cbv[CompartmentIsolatedThreads].
          intros * hneq hiso * hthread' hcompartment'.
          unsafe_saturate_list. destruct_products; option_simpl.
          destruct (PeanoNat.Nat.eq_dec (machine_curThreadId m) n); subst; option_simpl; cbn.
          { exfalso.
            eapply ThreadInUserCompartmentDoesNotHaveSystemPerm; eauto.
            cbv[ThreadHasSystemPerm]; cbn.
            erewrite MEPCC_ok by (eapply HUserMode; eauto).
            cbn. eauto.
          }
          { rewrite hsame in * by lia.
            eapply HIsolatedThreads; eauto with lists.
          }
        }
        assert (CompartmentIsolation m') as hiso.
        { cbv[CompartmentIsolation]. eauto. }

        assert (UserModeInvariant config m') as huserMode.
        { cbv[UserModeInvariant].
          intros * ht ht_userMode. 
          unsafe_saturate_list; destruct_products; option_simpl.
          destruct (PeanoNat.Nat.eq_dec (machine_curThreadId m) n); subst; option_simpl; cbn.
          { exfalso. apply ht_userMode.
            cbn.
            erewrite MEPCC_ok by (eapply HUserMode; eauto).
            cbn. eauto.
          }
          { rewrite hsame in * by lia.
            eapply HUserMode; eauto with lists.
          }
        }
        constructor; auto; cbn.
      Qed.

      Definition ReachableViaCallRet (caps caps': list Cap) :=
        forall cap, In cap caps' ->
                    In cap caps \/
                      (* Seal *)
                      (exists c, In c caps
                                 /\ isSealed c = false
                                 /\ RestrictUnsealed c (setCapSealed cap None)
                                 /\ isSentry cap = true) \/
                      (* Unseal *)
                      (exists c, In c caps /\ isSentry c = true /\ cap = setCapSealed c None).
      
      
      Hint Resolve RestrictRefl: ReachableCap.
      Hint Resolve Refl: ReachableCap.
      Hint Resolve StepRestrict: ReachableCap.
      Hint Resolve StepLoadCap: ReachableCap.
      Hint Resolve StepSeal: ReachableCap.
      Hint Resolve StepUnseal: ReachableCap.
      Hint Resolve RestrictUnsealedOk: ReachableCap.
      Ltac simplify_ReachableCap :=
        repeat match goal with
          | H: ReachableCap ?mem ?caps ?y,
              H1: Restrict ?y ?z
            |- ReachableCap ?mem ?caps ?z =>
              eapply StepRestrict with (1 := H) (2 := H1)
          | H: ReachableCap ?mem ?caps (setCapSealed ?y None),
              H1: Restrict ?y ?z
            |- ReachableCap ?mem ?caps (setCapSealed ?z None) =>
              eapply StepRestrict with (1 := H)
          | H : isSentry ?y = true, H1: Restrict ?y ?z |- isSentry ?z = true =>
              unfold isSentry;
              rewrite<-RestrictSealedEq with (1 := H1)
          | H: Restrict ?x ?y, H1: Restrict ?y ?z |-  Restrict ?x ?z =>
              apply RestrictTrans with (1 := H) (2 := H1)
          | H : isSentry ?x = true, H1: capSealed ?x = None |- _ =>
              exfalso; clear - H H1; cbv[isSentry] in *; simpl_match; discriminate
          | _ => progress (auto with ReachableCap)
          end.

      Lemma ThreadInUserCompartmentSystemEquiv:
        forall config mem thread thread' idx,
          ~ ThreadHasSystemPerm thread' ->
          thread.(thread_systemState) = thread'.(thread_systemState) ->
          ThreadInUserCompartment config mem thread idx ->
          ThreadInUserCompartment config mem thread' idx.
      Proof.
        cbv[ThreadInUserCompartment]. intros. rewrite<-H0. destruct_products; eauto.
      Qed.

      Lemma WfCallSentryInst_CapsReached :
        forall callSentryInst srcReg optLink userCtx mem istatus pcc' rf' istatus',
        ValidRf (thread_rf userCtx) ->
        WfCallSentryInst callSentryInst srcReg optLink ->
        isSealed (thread_pcc userCtx) = false ->
        callSentryInst (userCtx, mem) istatus = Ok(pcc', rf', istatus') ->
        ReachableViaCallRet (capsOfUserTS userCtx) (pcc' :: capsOfRf rf'). 
      Proof.
        cbv[ReachableViaCallRet].
        intros * hrf hwf hpcc_unsealed hcall * hin'.
        match goal with
        | H: ?callSentryInst ?userCtx ?istatus = Ok (?pcc', ?rf', ?istatus'),
            H1: WfCallSentryInst ?callSentryInst ?srcReg ?optLink |- _ =>
            cbv[WfCallSentryInst] in *;
            specialize H1 with (rf := thread_rf (fst userCtx))
                               (pcc := thread_pcc (fst userCtx))
                               (ints := istatus)
                               (mem := snd userCtx); cbn in H1;
            setoid_rewrite H in H1
        end; propositional.
        destruct_products. subst.
        inv hin'.
        - destruct (isSentry src_cap) eqn:hsrc_cap.
          + right. right. exists src_cap. split_and?; auto.
            cbv[capsOfUserTS]. right.
            saturate_list. apply In_listSumToInl. auto.
          + left. cbv[capsOfUserTS]. right.
            rewrite setCapSealedNoneEq.
            2: { cbv[isSentry] in *. by (bash_destruct hsrc_cap). }
            saturate_list. apply In_listSumToInl. auto.
        - destruct_with_eqn optLink; destruct_products; subst.
          + apply listSumToInl_In in H.
            rewrite In_iff_nth_error in H. destruct_products.
            fold (CapOrBytes) in *.
            destruct (PeanoNat.Nat.eq_dec n n0); subst; option_simpl.
            * inv H. right. left. exists (thread_pcc userCtx); split_and?; auto.
              { left; auto. }
              { cbv [isSentry]. by simpl_match. }
            * left. right.
              match goal with
              | H: forall _, _ <> _ -> nth_error _ _ = nth_error _ _ |- _ =>
                  rewrite H in * by lia
              end.
              saturate_list.
              apply listSumToInl_iff. auto.
          + left. right. auto.
      Qed.

      Lemma threadHasSystemPerm_false_iff:
        forall thread,
          threadHasSystemPerm thread = false <-> ~(ThreadHasSystemPerm thread).
      Proof.
        cbv[threadHasSystemPerm ThreadHasSystemPerm]. unfold not.
        intros. split. intros.
        - match goal with
          | H: ?x = false |- _ =>
              assert (x = true); [ | congruence]
          end.
          rewrite existsb_exists. eexists; split; eauto.
        - intros.
          match goal with
          | |- ?x = false =>
              destruct x eqn:?; auto
          end.
          rewrite existsb_exists in *. destruct_products.
          apply Perm.internal_t_dec_bl in Heqbr. subst. congruence.
      Qed.

      Context {decode: list Byte -> @Inst _ _ capEncodeDecode}.
      Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
      Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).

      (* TODO: duplicated *)
      Ltac saturate_footprints := 
       repeat match goal with
              | H: nth_error (configThreads _) _ = Some ?thread,
                H1: In ?addr (stackFootprint ?thread) |- _ =>
                  let H' := fresh H1 "footprint" in 
                  learn_hyp (threadInConfigFootprint _ _ _ _ H H1) as H'
              | H: nth_error (configCompartments _) _ = Some ?comp,
              H1: In ?addr (compartmentFootprint ?comp) |- _ =>
                  let H' := fresh H1 "footprint" in 
                  learn_hyp (compartmentInConfigFootprint _ _ _ _ H H1) as H'
         end.

            
      Ltac saturate_invariants :=
        repeat match goal with
        | H: WFConfig _ |- _ =>
            mark (MkMark "WFConfig");
            destruct_and_save H
        | H: ValidInitialState _ _ |- _ =>
            mark (MkMark "ValidInitialState");
            destruct_and_save H
        | H: Forall _ _ |- _ => rewrite Forall_forall in H
        | H: forall x, In x _ -> _,
          H1: In _ _ |- _ =>
            learn_hyp (H _ H1)
        | H : machine_memory _ = configInitMemory _ |- _ =>
            rewrite H in *
        | _ => progress (saturate_list; repeat simpl_match)
        end; auto.

      Lemma AddressesInitiallyIsolated:
        forall idx1 idx2 initial_machine c1 c2,
          ValidInitialState config initial_machine ->
          idx1 <> idx2 ->
          nth_error (configCompartments config) idx1 = Some c1 ->
          nth_error (configCompartments config) idx2 = Some c2 ->
          AddrsIsolatedFromCompartment (machine_memory initial_machine)
            (capsOfCompartment c1) idx2.
      Proof.
        cbv[AddrsIsolatedFromCompartment AddrInCompartment].
        intros * hinit hneq hc1 hc2 * hrwx haddr. destruct_products; option_simpl.
        saturate_invariants.
        assert (In addr (compartmentFootprint c1)).
        { eapply WFCompartment_ReachableRWXAddr; eauto. }
        saturate_footprints.
        simplify_Separated.
      Qed.
      Ltac saturate_subset:=
        repeat match goal with
        | H: Subset ?x ?y,
          H1: In ?z ?x |- _ =>
            learn_hyp (H _ H1)
          end.

      Lemma PCompartmentIsolation_InitCompartments:
        forall initial_machine,
          ValidInitialState config initial_machine ->
          CompartmentIsolation initial_machine.
      Proof.
        cbv[CompartmentIsolation IsolatedFromCompartment].
        intros * hvalid * hneq hisolated * hc1 hc2.
        repeat split_and.
        - eapply AddressesInitiallyIsolated with (3 := hc1) (4 := hc2); eauto.
        - consider MutuallyIsolatedCompartment.
          cbv[SentriesIsolatedFromCompartment].
          intros. destruct_products; option_simpl. eapply hisolatedrrrr.
          eapply ReachableLibrary; eauto.
          eapply WFCompartment_Sentries with (config := config);
            saturate_invariants.
        - consider MutuallyIsolatedCompartment.
          cbv[SealedDataCapsIsolatedFromCompartment].
          intros. destruct_products; option_simpl. eapply hisolatedrrrr; eauto.
          eapply ReachableCaller; eauto.
          eapply WFCompartment_SealedDataCap with (config := config); cbv[isSealedDataCap];
            saturate_invariants.
      Qed.

      Lemma AddrsIsolatedFromCompartmentSubset:
        forall mem caps idx caps',
        AddrsIsolatedFromCompartment mem caps idx ->
        Subset caps' caps ->
        AddrsIsolatedFromCompartment mem caps' idx.
      Proof.
        cbv[AddrsIsolatedFromCompartment].
        intros. eapply H; eauto. eapply ReachableRWXAddrSubset; eauto.
      Qed.

      Lemma SentriesIsolatedFromCompartmentSubset:
        forall mem caps idx caps',
        SentriesIsolatedFromCompartment mem caps idx ->
        Subset caps' caps ->
        SentriesIsolatedFromCompartment mem caps' idx.
      Proof.
        cbv[SentriesIsolatedFromCompartment].
        intros. eapply H; eauto. eapply ReachableCapIncrease; eauto.
      Qed.
      Lemma SealedDataCapsIsolatedFromCompartmentSubset:
        forall mem caps idx caps',
        SealedDataCapsIsolatedFromCompartment mem caps idx ->
        Subset caps' caps ->
        SealedDataCapsIsolatedFromCompartment mem caps' idx.
      Proof.
        cbv[SealedDataCapsIsolatedFromCompartment].
        intros. eapply H; eauto. eapply ReachableCapIncrease; eauto.
      Qed.

      Lemma IsolatedFromCompartmentSubset:
        forall mem caps caps' idx,
          IsolatedFromCompartment mem caps idx ->
          Subset caps' caps ->
          IsolatedFromCompartment mem caps' idx.
      Proof.
        cbv[IsolatedFromCompartment]. intros. destruct_products. split_ands.
        - eapply AddrsIsolatedFromCompartmentSubset; eauto.
        - eapply SentriesIsolatedFromCompartmentSubset; eauto.
        - eapply SealedDataCapsIsolatedFromCompartmentSubset; eauto.
      Qed.

      Ltac simplify_provenance :=
        repeat match goal with
        | H: AddrHasProvenance _ _ (Provenance_Compartment _) |- _ =>
            inv H
        | H: AddrInCompartment _ _ _ |- _ =>
            inv H
        | H: ReachableAddr _ _ _ _ _ _ _ |- _ =>
            inv H
          end.

      Lemma InitialThreadCapSubset:
        forall thread cap meta compartment ,
          ValidInitialThread config meta thread ->
          ReachableCap (configInitMemory config) (capsOfUserTS (thread_userState thread)) cap ->
          nth_error (configCompartments config) (initThreadCompartment meta) = Some compartment ->
          ReachableCap (configInitMemory config) (meta.(initThreadCSP)::capsOfCompartment compartment) cap.
      Proof.
        intros * hvalid hcompartment hcap. destruct hvalid. destruct_products.
        cbv[ReachableCapSubset ReachableCaps] in *.
        option_simpl.
        eapply ValidInitialThread_caps0r; eauto.
      Qed.

      (* For CSP *)
      Lemma ReachableCapRestrictCSP:
        forall mem (cap: Cap) caps x,
          x.(capSealingKeys) = [] ->
          x.(capUnsealingKeys) = [] ->
          x.(capSealed) = None ->
          (forall capa, Subset (seq (fromCapAddr capa) ISA_CAPSIZE_BYTES) x.(capAddrs) ->
                       readTag mem capa = false) ->
          (Restrict x (setCapSealed cap None) -> False) ->
          ReachableCap mem (x::caps) cap ->
          ReachableCap mem caps cap.
      Proof.
        intros * hseal hunseal hunsealed huntagged hnotSelf.
        induction 1.
        - inv inPf.
          + rewrite setCapSealedNoneEq in * by auto.
            exfalso. apply hnotSelf. apply RestrictRefl.
          + apply Refl. auto.
        - eapply StepRestrict; eauto.
          eapply IHReachableCap. intros.
          apply hnotSelf. eapply RestrictTrans; eauto.
          apply RestrictSetCapUnsealed; auto.
        - eapply StepLoadCap; eauto.
          eapply IHReachableCap. inv xyz; destruct_products.
          rewrite setCapSealedNoneEq by auto. intros.
          specialize @RestrictCapAddrsSubset with (1 := H0); intros.
          cbv[readCap readMemTagCap readTag] in *.
          rewrite huntagged in *.
          { cbn in *. discriminate. }
          cbv[Subset]; intros.
          eapply H1. eapply loadFromAuthl. auto.
        - eapply StepSeal; eauto; inv xyz; destruct_products; repeat simpl_match; subst.
          + eapply IHReachableCap1; eauto; cbn in *; intros.
            eapply RestrictCapSealingKeysSubset in H1l; eauto.
            * rewrite hseal in *. contradiction.
            * rewrite setCapSealedNoneEq in * by auto. auto.
          + eapply IHReachableCap2. intros. cbn in *.
            rewrite setCapSealedNoneEq in * by auto.
            apply hnotSelf.
            rewrite setCapSealed_inv. rewrite setCapSealedNoneEq; auto.
        - eapply StepUnseal; eauto; inv xyz; destruct_products; repeat simpl_match; subst.
          + eapply IHReachableCap1; auto; cbn in *; intros.
            rewrite setCapSealedNoneEq in * by auto.
            eapply RestrictCapUnsealingKeysSubset in H1l; eauto. rewrite hunseal in *. 
            contradiction. 
          + eapply IHReachableCap2; auto; cbn in *; intros.
      Qed.
      
      Lemma IsolatedFromCompartmentInitialThread:
        forall c1 idx2 x y threadId,
        Separated (ConfigFootprints config) ->
        IsolatedFromCompartment (configInitMemory config) (capsOfCompartment c1) idx2 ->
        ValidInitialThread config x y ->
        nth_error (configThreads config) threadId = Some x ->
        (ReachableCompartment config (initThreadCompartment x) idx2 -> False) ->
        nth_error (configCompartments config) (initThreadCompartment x) = Some c1 ->
        IsolatedFromCompartment (configInitMemory config) (capsOfUserTS (thread_userState y)) idx2.
      Proof.
        cbv[IsolatedFromCompartment].
        intros * hseparated (haddr & hsentries & hdata) hinit hthread hnot_reachable hmeta.
        pose proof (ValidInitialCSP _ _ _ _ hinit) as hvalidcsp. consider @ValidCSP.
        destruct_products.
        split_ands.
        - cbv[AddrsIsolatedFromCompartment]. intros.
          eapply haddr; eauto. simplify_provenance; destruct_products.
          consider ReachableRWXAddr. destruct_products. simplify_provenance.
          do 3 eexists; split; eauto.
          constructor; auto.
          assert ((capAddrs (mkCSP base len addr)) = stackFootprint x) as hfootprint.
          { unfold stackFootprint. rewrite_solve. }
          eapply ReachableCapRestrictCSP with (x := x.(initThreadCSP)); try rewrite hvalidcspr; auto.
          + intros. eapply ValidInitialThread_stackUntagged; eauto.
            unfold stackFootprint. rewrite hvalidcspr. auto.
          + rewrite setCapSealedNoneEq by auto. intros hrestrict.
            apply RestrictCapAddrsSubset in hrestrict. cbv[Subset] in *.
            assert (In addr0 (stackFootprint x)).
            { rewrite<-hfootprint. apply hrestrict. apply ina. constructor. auto. }
            saturate_footprints; saturate_list; simplify_Separated.
          + rewrite<-hvalidcspr. eapply InitialThreadCapSubset; eauto.
        - cbv[SentriesIsolatedFromCompartment]. intros.
          eapply hsentries; eauto; simplify_provenance; destruct_products.
          assert ((capAddrs (mkCSP base len addr)) = stackFootprint x) as hfootprint.
          { unfold stackFootprint. rewrite_solve. }
          eapply ReachableCapRestrictCSP with (x := x.(initThreadCSP)); try rewrite hvalidcspr; auto.
          + intros. eapply ValidInitialThread_stackUntagged; eauto.
            unfold stackFootprint. rewrite hvalidcspr. auto.
          + intros hrestrict. apply RestrictCapAddrsSubset in hrestrict. 
            fold (stackFootprint x) in *.
            assert (In addr0 (stackFootprint x)).
            { rewrite<-hfootprint. apply hrestrict. auto. }
            saturate_footprints; saturate_list; simplify_Separated.
          + rewrite<-hvalidcspr. eapply InitialThreadCapSubset; eauto.
        - cbv[SealedDataCapsIsolatedFromCompartment]. intros.
          eapply hdata; eauto; simplify_provenance; destruct_products.
          assert ((capAddrs (mkCSP base len addr)) = stackFootprint x) as hfootprint.
          { unfold stackFootprint. rewrite_solve. }
          eapply ReachableCapRestrictCSP with (x := x.(initThreadCSP)); try rewrite hvalidcspr; auto.
          + intros; eapply ValidInitialThread_stackUntagged; eauto.
            rewrite<-hfootprint. auto.
          + intros hrestrict. apply RestrictCapAddrsSubset in hrestrict.
            fold (stackFootprint x) in *.
            assert (In addr0 (stackFootprint x)).
            { rewrite<-hfootprint. apply hrestrict; auto. }
            saturate_footprints; saturate_list; simplify_Separated.
          + rewrite<-hvalidcspr. eapply InitialThreadCapSubset; eauto.
       Qed.

        Lemma ValidInitialThreadImpliesCompartment:
          forall config meta thread cid frame compartment eid,
          ValidInitialThread config meta thread ->
          hd_error (trustedStack_frames (thread_trustedStack (thread_systemState thread))) =
            Some frame ->
          LookupExportTableCompartmentId config (trustedStackFrame_calleeExportTable frame)  = Some (cid, eid) ->
          nth_error (configCompartments config) cid = Some compartment ->
          cid = initThreadCompartment meta.
        Proof.
          intros * hvalid hframe hcompartment hid.
          destruct hvalid. destruct_products. unfold hd_error in *.
          simpl_match; option_simpl.
          match goal with
          | H: ValidTrustedStackFrame _ _ _ _ _ _ |- _ => destruct H
          end; destruct_products; option_simpl; simplify_tupless; eauto.
        Qed.

      Lemma PCompartmentIsolation_InitThreads:
        forall initial_machine,
          ValidInitialState config initial_machine ->
          CompartmentIsolation initial_machine ->
          CompartmentIsolatedThreads initial_machine.
      Proof.
        cbv[CompartmentIsolation CompartmentIsolatedThreads ThreadInUserCompartment].
        intros * init hiso * hneq hisolated * hthread hcthread.
        destruct_products.
        specialize hiso with (1 := hneq) (2 := hisolated).
        cbv[MutuallyIsolatedCompartment] in *. destruct_products.
        specialize hiso with (1 := hisolatedl) (2 := hisolatedrl).
        saturate_invariants. 
        match goal with
        | H: Forall2 (ValidInitialThread _) _ ?xs,
            H1: In _ ?xs |- _ =>
            let H' := fresh H in pose proof H as H';
            mark (MkMark "Forall2_ValidInitialThread");
            let n := fresh "n" in let rest := fresh in
            apply In_nth_error in H1; destruct H1 as (n & rest);
            eapply Forall2_nth_error2' with (idx := n) in H; eauto; saturate_list; try lia
        end.
        destruct_products; option_simpl.
        assert (idx1 = x.(initThreadCompartment)); try subst idx1.
        { simplify_provenance; option_simpl.
          eapply ValidInitialThreadImpliesCompartment; eauto.
        }
        eapply IsolatedFromCompartmentInitialThread; eauto.
      Qed.
        
      Lemma InitialPropertyHolds :
        forall initial_machine,
        ValidInitialState config initial_machine ->
        InitialProperty (initial_machine, []).
      Proof.
        intros * hvalid.
        constructor.
        - apply hvalid.
        - pose proof (PCompartmentIsolation_InitCompartments _ hvalid) as hiso.
          pose proof (PCompartmentIsolation_InitThreads _ hvalid hiso) as hthread.
          constructor; auto.
          eapply ValidInit_userMode; eauto.
      Qed.
    End WithConfig.
  End WithContext.
End CompartmentIsolationValidation.

(* From any valid initial state where threads are isolated (their reachable
   read/write caps are disjoint), for any sequence of same-domain (Ev_General)
   steps, the reachable caps in each thread do not increase. *)
Module ThreadIsolatedMonotonicity.
  Import ListNotations.
  Import Configuration.
  Import Separation.
  Section WithContext. 
    Context [ISA: ISA_params].
    Context {machineTypeParams: MachineTypeParams}.
    Context {capEncodeDecode: CapEncodeDecode}.
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> @Inst _ _ capEncodeDecode}.
    Context {pccNotInBounds : EXNInfo}.
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation State := (Machine * Trace)%type.
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Context {LookupExportTableCompartmentId: Config -> Cap -> option (nat*nat)}.
    Notation ValidInitialState := (@ValidInitialState _ _ _ LookupExportTableCompartmentId).
    Notation ValidInitialThread := (@ValidInitialThread _ _ _ LookupExportTableCompartmentId). 

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
        - eapply Configuration.InvariantInitial.
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
        inv stepOkrrl.
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
              rewrite stepOkrrr in *. option_simpl.
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
   - intermediate lemma: on a compartment call, we
 *)
   


(* Invariant: if a (isolated) compartment always sanitizes its caps such that
   - as a caller, all arguments have LG unset
   - as a callee, it never passes caps that have access to its globals in the return argument
     --> how to enforce this?
   then other compartments should only have temporary access to its caps
   -> that is, the only caps a thread in a different compartment should have access to belonging to 
 *)
                                                                              
(* (* Let's keep caps in a canonical form... *) *)
(* Record CapEquiv (c1 c2: Cap) := { *)
(*     capEquiv_Sealed: c1.(capSealed) = c2.(capSealed); *)
(*     capEquiv_Perms:  EqSet c1.(capPerms) c2.(capPerms); *)
(*     capEquiv_capCanStore: EqSet c1.(capCanStore) c2.(capCanStore); *)
(*     capEquiv_capCanBeStored: EqSet c1.(capCanBeStored) c2.(capCanBeStored); *)
(*     capEquiv_capSealingKeys: EqSet c1.(capSealingKeys) c2.(capSealingKeys); *)
(*     capEquiv_capAddrs: EqSet c1.(capAddrs) c2.(capAddrs); *)
(*     capEquiv_capKeepPerms: EqSet c1.(capKeepPerms) c2.(capKeepPerms); *)
(*     capEquiv_capKeepCanStore: EqSet c1.(capKeepCanStore) c2.(capKeepCanStore); *)
(*     capEquiv_capKeepCanBeStored: EqSet c1.(capKeepCanBeStored) c2.(capKeepCanBeStored); *)
(*     capEquiv_capCursor: c1.(capCursor) = c2.(capCursor) *)
(* }. *)

