(*! Properties about the spec based on the initial configuration. *)

From Stdlib Require Import String List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Spec Utils Tactics SpecLemmas.

Create HintDb invariants.
Import ListNotations.
Create HintDb lists.
Hint Resolve nth_error_In : lists.

Inductive MARK : string -> Type :=
| MkMark : forall s, MARK s.
Tactic Notation "mark" constr(p) :=
  let H := fresh "Mark" in
  learn_hyp p as H.

Set Nested Proofs Allowed.

Import Separation.
Ltac finish_Separated :=
  match goal with
  | H: Separated ?xs,
    H1: nth_error ?xs ?t1 = Some ?s1,
    H2: nth_error ?xs ?t2 = Some ?s2,
    H3: In ?addr ?s1,
    H4: In ?addr ?s2,
    H5: ?t1 <> ?t2 |- _ =>
      exfalso; eapply H with (2 := H1) (3 := H2) (4 := H3) (5 := H4);
      solve[option_simpl; auto; lia]
  | _ => progress(option_simpl; lia)
  end.

Ltac prepare_Separated :=
  try match goal with
      | H1: nth_error ?xs ?t1 = Some ?s1,
        H2: nth_error ?xs ?t2 = Some ?s2,
        H3: In ?addr ?s1,
        H4: In ?addr ?s2
        |- _ =>
        let Heq := fresh in   
        assert (t1 = t2) as Heq;
        [ destruct (PeanoNat.Nat.eq_dec t1 t2); [ by auto | ]  | subst ]
    end.

Ltac simplify_Separated :=
  prepare_Separated; try solve[finish_Separated].

(* Defining the valid initial states of a machine in terms of
   compartments and thread initialization. *)
Module Configuration.
  Section WithContext. 
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {capEncodeDecode: @CapEncodeDecode Byte Key}.
    Notation Cap := (@Cap Key).
    Notation CapOrBytes := (@CapOrBytes Byte Key).
    Notation FullMemory := (@FullMemory Byte).
    Notation TrustedStackFrame := (@TrustedStackFrame Key).

    Record ExportEntry : Type := {
        exportEntryOffset: nat; 
        exportEntryStackSize: nat;
        exportEntryNumArgs: nat;
        exportEntryInterruptStatus: InterruptStatus
    }.

    Record ExportTable := {
        exportTablePCC: Cap;
        exportTableCGP: Cap;
        exportTableErrorHandlerOffsets: list nat; 
        exportTableEntries: list ExportEntry
    }.
    
    (* Simplifying, for now, and eliding MMIO and shared objects. *)
    Inductive ImportEntry :=
    | ImportEntry_SealedCapToExportEntry (c: Cap)
    | ImportEntry_SentryToLibraryFunction (c: Cap).

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
        (* initThreadEntryPoint: Addr; *)
        (* initThreadRf : RegisterFile; *)
        initThreadCSP: Cap;
        initThreadCompartment: nat
    }.

    (* TODO: sealing keys *)
    Record Compartment := {
        compartmentPCC: Cap; (* Code and read-only data, including import entries *)
        compartmentCGP: Cap; 
        compartmentExports: list ExportEntry;
        compartmentImports: list ImportEntry
      }.

    Record Library :=
      { libraryReadOnly: list Addr
      ; libraryImports: list ImportEntry
      }.                            

    (* The initial state of a machine is defined in terms of its
       compartments, libraries, the trusted switcher, the initial
       state of the threads, and the initial memory. *)
    Record Config := {
        configCompartments: list Compartment;
        configLibraries: list Library;
        configSwitcher: nat; (* Index of the switcher library *)
        configThreads : list InitialThreadMetadata;
        configInitMemory: FullMemory;
        configSwitcherKey: Key
    }.

    Definition compartmentFootprint (compartment: Compartment) : list Addr :=
        compartment.(compartmentPCC).(capAddrs) ++ compartment.(compartmentCGP).(capAddrs).
    Definition stackFootprint (t: InitialThreadMetadata) : list Addr :=
        t.(initThreadCSP).(capAddrs).
    Definition libraryFootprint (l: Library) : list Addr :=
      l.(libraryReadOnly).

    Definition capsOfImportEntry (ie: ImportEntry) :=
      match ie with
      | ImportEntry_SealedCapToExportEntry c => c
      | ImportEntry_SentryToLibraryFunction c => c
      end.                                                    
    Definition baseCapsOfCompartment (c: Compartment) :=
      [c.(compartmentPCC);c.(compartmentCGP)]. 

    (* The set of capabilities a compartment initially has access to.
       TODO: sealing keys 
     *)
    Definition capsOfCompartment (c: Compartment) :=
      c.(compartmentPCC)::c.(compartmentCGP)::(map capsOfImportEntry c.(compartmentImports)).
    Definition AddrInCompartment (config: Config) (cid: nat) (addr: Addr): Prop :=
      exists compartment,
        nth_error config.(configCompartments) cid = Some compartment /\
        In addr (compartmentFootprint compartment).

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
                
    (* TODO *)
    Definition ValidUnsealedCap (c: Cap) : Prop :=
      In c.(capCursor) c.(capAddrs) /\ c.(capSealed) = None.

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

     Definition InLibraryFootprint (config: Config) addr :=
       exists library, In library config.(configLibraries) /\
                       In addr (libraryFootprint library).
     
     Definition WFImportEntry (config: Config) (importEntry: ImportEntry) :=
         ( forall cap, importEntry = ImportEntry_SentryToLibraryFunction cap ->
           isSentry cap = true /\
           (forall addr, In addr cap.(capAddrs) ->
                         InLibraryFootprint config addr)) /\
         (forall cap, importEntry = ImportEntry_SealedCapToExportEntry cap ->
                      cap.(capSealed) = Some (inr config.(configSwitcherKey))).
   
    Record WFCompartment (config: Config) (c: Compartment) :=
      { WFCompartment_ReachableRWXAddr:
          InitialCompartmentAddressesOk config.(configInitMemory) c
      ; WFCompartment_InitialCaps:
          AllReachableCaps config.(configInitMemory) (capsOfCompartment c)
      ; WFCompartment_PCC: c.(compartmentPCC).(capSealed) = None
      ; WFCompartment_Sentries: SentriesOnlyFromImportTables config.(configInitMemory) c
      ; WFCompartment_SealedDataCap: SealedDataCapsOnlyFromImportTables config.(configInitMemory) c
      ; WFCompartment_ImportEntries: forall entry, In entry c.(compartmentImports) -> WFImportEntry config entry
      }.                                                                       

    Definition WFSwitcher (c: Library) : Prop := True.

    Definition ConfigFootprints (config: Config) :=
        (* (configMMIOAddrs config) :: *)
          (map compartmentFootprint config.(configCompartments))
            ++ (map stackFootprint config.(configThreads))
            ++ (map libraryFootprint config.(configLibraries)).

    Record WFConfig (config: Config) := {
        WFConfig_footprintDisjoint: Separated (ConfigFootprints config);
        WFConfig_compartmentMemory: Forall (WFCompartment config) config.(configCompartments);
        WFConfig_switcher: exists c, nth_error config.(configLibraries) config.(configSwitcher) = Some c /\
                                WFSwitcher c
        (* WFConfig_importEntriesOk: ImportEntriesOk config *)
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
        AddrHasProvenance config addr (Provenance_Compartment cid)
    | LibraryCodeProvenance: forall config addr lid library,
        nth_error config.(configLibraries) lid = Some library ->
        In addr (libraryFootprint library) ->
        AddrHasProvenance config addr (Provenance_Library lid).

    Record GlobalInvariant (config: Config) (m: Machine) : Prop :=
    { Inv_curThread: m.(machine_curThreadId) < length m.(machine_threads)
    ; Inv_threads : Forall2 ThreadInv config.(configThreads) m.(machine_threads)
    }.

    (* TODO *)
    Context {LookupExportTableCompartment: Config -> Cap -> FullMemory -> option nat}.

    Record ValidTrustedStackFrame
      (config: Config)
      (mem: FullMemory) (frame: TrustedStackFrame) (meta: InitialThreadMetadata)
      (cid: nat): Prop :=
      { ValidTrustedStackFrame_calleeCap:
        LookupExportTableCompartment config
          frame.(trustedStackFrame_calleeExportTable)
          mem = Some cid
      ; ValidTrustedStackFrame_CSP :
          Restrict meta.(initThreadCSP) frame.(trustedStackFrame_CSP)
      }.                                                                                 

    Definition ValidCSP (csp: Cap) :=
      csp.(capSealingKeys) = [] /\
      csp.(capUnsealingKeys ) = [] /\
      csp.(capSealed) = None.
    Record ValidInitialThread (config: Config) (meta: InitialThreadMetadata) (t: Thread) : Prop :=
      { ValidInitialThread_caps:
        exists compartment,
          nth_error config.(configCompartments) meta.(initThreadCompartment) = Some compartment /\
            forall c,
              ReachableCap config.(configInitMemory) (capsOfUserTS (thread_userState t)) c ->
              ReachableCap config.(configInitMemory)
                           (meta.(initThreadCSP)::capsOfCompartment compartment)
                           c
      ; ValidInitialThread_trustedStack:
          exists frame, t.(thread_systemState).(thread_trustedStack).(trustedStack_frames) =
                          [frame] /\
                          ValidTrustedStackFrame config config.(configInitMemory) frame meta meta.(initThreadCompartment)
      ; ValidInitialThread_stackUntagged: (* No caps in initial stack --> TODO: fix spec*)
        forall capa, Subset (seq (fromCapAddr capa) ISA_CAPSIZE_BYTES) (stackFootprint meta) ->
                     readTag config.(configInitMemory) capa = false
      ; ValidInitialCSP: ValidCSP meta.(initThreadCSP)
      }.                         
                    
    Record ValidInitialState (config: Config) (m: Machine) : Prop :=
      { ValidInit_memory: m.(machine_memory) = config.(configInitMemory)
      ; ValidInit_threads: Forall2 (ValidInitialThread config) config.(configThreads) m.(machine_threads) 
      ; ValidInit_invariant: GlobalInvariant config m
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
        case_match; simplify_nat.
        rewrite nth_error_map.
        replace (length (configCompartments config) + tid - length (configCompartments config)) with tid by lia.
        rewrite hthread. cbn. eexists; split; eauto.
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

      Lemma libraryInConfigFootprint:
        forall config library lid addr,
          nth_error (configLibraries config) lid = Some library ->
          In addr (libraryFootprint library) ->
          nth_error (ConfigFootprints config) (length config.(configCompartments) + length config.(configThreads) + lid) = Some (libraryFootprint library).
      Proof.
        intros * hlib haddr.
        unfold ConfigFootprints.
        repeat rewrite nth_error_app. repeat rewrite length_map.
        saturate_list.
        case_match; simplify_nat.
        case_match; simplify_nat.
        rewrite nth_error_map.
        match goal with
        | |- context[nth_error _ ?x] => replace x with lid by lia
        end.
        rewrite_solve.
      Qed.
    Section Proofs.
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
          | H: nth_error (configLibraries _) _ = Some ?comp,
              H1: In ?addr (libraryFootprint ?comp) |- _ =>
              let H' := fresh H1 "footprint" in 
              learn_hyp (libraryInConfigFootprint _ _ _ _ H H1) as H'
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

(* If a (malicious) compartment is not transitively-reachable from a
   protected compartment, then it should never have access to the
   protected compartment's memory regions.
 *)
Module CompartmentIsolation.
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
    Context {LookupExportTableCompartment: Config -> Cap -> FullMemory -> option nat}.
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Notation ValidInitialState := (@ValidInitialState _ Byte Key _ LookupExportTableCompartment).
    Notation ValidInitialThread := (@ValidInitialThread _ Byte Key _ LookupExportTableCompartment). 

    (* Compartments are connected on the callgraph *)
    Inductive ReachableCompartment : Config -> nat -> nat -> Prop :=
    | ReachableSelf:
        forall config idx,
          WFConfig config ->
          idx < length config.(configCompartments) ->
          ReachableCompartment config idx idx
    | ReachableCaller:
        forall config idx1 idx2 c1 cap addr,
          WFConfig config ->
          nth_error config.(configCompartments) idx1 = Some c1 ->
          In (ImportEntry_SealedCapToExportEntry cap) c1.(compartmentImports) ->
          In addr cap.(capAddrs) ->
          AddrHasProvenance config addr (Provenance_Compartment idx2) ->
          ReachableCompartment config idx1 idx2
    | ReachableCallee:
        forall config idx1 idx2 c1 cap addr,
          WFConfig config ->
          nth_error config.(configCompartments) idx1 = Some c1 ->
          In (ImportEntry_SealedCapToExportEntry cap) c1.(compartmentImports) ->
          In addr cap.(capAddrs) ->
          AddrHasProvenance config addr (Provenance_Compartment idx2) ->
          ReachableCompartment config idx2 idx1
    | ReachableTrans:
        forall config idx1 idx2 idx3,
          WFConfig config ->
          ReachableCompartment config idx1 idx2 ->
          ReachableCompartment config idx2 idx3 ->
          ReachableCompartment config idx1 idx3.
             
    Definition ThreadHasSystemPerm (t: Thread) : Prop :=
      In Perm.System t.(thread_userState).(thread_pcc).(capPerms).


    Definition ThreadInUserCompartment (config: Config) (mem: FullMemory) (t: Thread) (cid: nat) : Prop :=
      (~ ThreadHasSystemPerm t) /\
      exists frame ,
        hd_error t.(thread_systemState).(thread_trustedStack).(trustedStack_frames) = Some frame /\
        LookupExportTableCompartment config frame.(trustedStackFrame_calleeExportTable) mem = Some cid.

    Definition MutuallyIsolatedCompartment (config: Config) (idx1 idx2: nat) : Prop :=
      exists c1 c2,
        nth_error config.(configCompartments) idx1 = Some c1 /\
        nth_error config.(configCompartments) idx2 = Some c2 /\
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
           - The "sealedCapToExportEntries"  reachable from PCC/CGP should be isolated
         - The caps reachable from user-mode threads in a compartment should follow the above restrictions
         Extra invariants:
         - Only the switcher should have the unsealing key to sealedCapToExportEntries
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
            cap.(capSealed) = Some (inr config.(configSwitcherKey)) ->
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

      Record Invariant' (st: State) : Prop :=
        { Inv_CompartmentIsolation: CompartmentIsolation (fst st)
        ; Inv_IsolatedThreads: CompartmentIsolatedThreads (fst st)  
        }.                                                           
      
      Definition Invariant (st: State) : Prop :=
        GlobalInvariant config (fst st) /\
          Invariant' st.

      Ltac simplify_invariants :=
        repeat match goal with
          | H: GlobalInvariant _ ?m,
              H1: nth_error (machine_threads ?m) _ = Some ?thread
            |- ValidRf (thread_rf (thread_userState ?thread)) =>
              eapply GlobalInvariantImpliesValidRf with (1 := H) (2 := H1)
          end.

      Lemma ReachableCompartmentSym':
        forall idx1 idx2,
        ReachableCompartment config idx1 idx2 ->
        ReachableCompartment config idx2 idx1.
      Proof.
        induction 1; propositional.
        - apply ReachableSelf; eauto.
        - eapply ReachableCallee; eauto.
        - eapply ReachableCaller; eauto.
        - eapply ReachableTrans; eauto.
      Qed.

      Lemma ReachableCompartmentSym:
        forall idx1 idx2,
        ReachableCompartment config idx1 idx2 <->
        ReachableCompartment config idx2 idx1.
      Proof.
        intros. split; apply ReachableCompartmentSym'.
      Qed.

      Ltac init_invariant_proof :=
        repeat match goal with
        | H: WfGeneralInst ?generalInst,
          H1: ?generalInst _ _ = Ok _ |- _=>
            let Hok := fresh "HgeneralOk" in
            mark (MkMark "generalInstOkCommon");
            specialize generalInstOkCommon with (1 := H) (2 := H1) as Hok;
            assert_pre_and_specialize Hok; [simplify_invariants | ];
            cbn in Hok; destruct_products
        | H : Invariant' _ |- _ =>
            mark (MkMark "InvCompartmentIsolation");
            let H' := fresh "HCompartmentIsolation" in 
            pose proof (Inv_CompartmentIsolation _ H) as H';
            cbv [CompartmentIsolation] in H'
        end.

      Lemma GeneralStepOk :
        forall m tr m' thread generalInst userSt' sysSt',
          GlobalInvariant config m ->
          Invariant' (m, tr) ->
          GlobalInvariant config m' ->
          (forall n : nat,
              n <> machine_curThreadId m ->
              nth_error (machine_threads m') n = nth_error (machine_threads m) n) ->
          nth_error (machine_threads m) (machine_curThreadId m) = Some thread ->
          WfGeneralInst generalInst ->
          generalInst (thread_userState thread, machine_memory m)
                      (thread_systemState thread, machine_interruptStatus m) =
            Ok (userSt', machine_memory m', (sysSt', machine_interruptStatus m')) ->
          nth_error (machine_threads m') (machine_curThreadId m) =
            Some {| thread_userState := userSt'; thread_systemState := sysSt' |} ->
          Invariant' (m',(Ev_SameThread (machine_curThreadId m) Ev_General::tr)).
      Proof.
        intros * hginv hinv hginv' hsame hthread hwf hinst hupdate.
        constructor.
        (* cbv[PCompartmentIsolation]. *)
        (* intros * hneq hisolated * hcurThread hcurCompartment * haddr hreachable. *)
        (* init_invariant_proof. *)
        (* saturate_list; unsafe_saturate_list; destruct_products. *)
        (* destruct (PeanoNat.Nat.eq_dec (machine_curThreadId m) n); subst. *)
        (* { admit. } *)
        (* { rewrite hsame in * by lia. saturate_list. destruct_products. *)
        (*   (* Thread0 is in compartment idx2, which is isolated from idx1 *) *)
        (*   (* Addr is reachable from mem' from thread0 *) *)
        (*   (* But addr is in compartment idx1 *) *)
        (*   pose proof HCompartmentIsolation as Hiso'. *)
        (*   specialize Hiso' with (1 := hneq) (thread := thread0) (addr := addr). *)
        (*   propositional. *)
        (*   (* apply Hiso'. *) *)
        (*   admit. *)
        (* } *)
      Admitted.

      Lemma ExceptionStepOk :
        forall m tr m' thread exn,
          GlobalInvariant config m ->
          Invariant' (m, tr) ->
          GlobalInvariant config m' ->
          (forall n : nat,
              n <> machine_curThreadId m ->
              nth_error (machine_threads m') n = nth_error (machine_threads m) n) ->
          nth_error (machine_threads m) (machine_curThreadId m) = Some thread ->
          nth_error (machine_threads m') (machine_curThreadId m) =
            Some (Build_Thread
                    (Build_UserThreadState
                       (thread_rf (thread_userState thread))
                       (thread_mepcc (thread_systemState thread)))
                    (Build_SystemThreadState
                       (thread_pcc (thread_userState thread))
                       exn 
                       (thread_trustedStack (thread_systemState thread)))) ->
          machine_memory m = machine_memory m' ->
          Invariant' (m',(Ev_SameThread (machine_curThreadId m) Ev_Exception::tr)).
      Proof.
        (* intros * hginv hinv hginv' hsame hthread hupdate hMemEq. *)
        (* constructor. cbv[PCompartmentIsolation]. *)
        (* intros * hneq hisolated * hcurThread hcurCompartment * haddr hreachable. *)
        (* init_invariant_proof. *)
        
      Admitted.


      Lemma CallSentryStepOk :
        forall m tr m' thread callSentryInst srcReg optLink pcc' rf', 
          GlobalInvariant config m ->
          Invariant' (m, tr) ->
          GlobalInvariant config m' ->
          (forall n : nat,
              n <> machine_curThreadId m ->
              nth_error (machine_threads m') n = nth_error (machine_threads m) n) ->
          nth_error (machine_threads m) (machine_curThreadId m) = Some thread ->
          WfCallSentryInst callSentryInst srcReg optLink ->
          callSentryInst (thread_userState thread, machine_memory m)
                         (machine_interruptStatus m) =
            Ok (pcc', rf', machine_interruptStatus m') ->
          nth_error (machine_threads m') (machine_curThreadId m) =
            Some {| thread_userState := {| thread_rf := rf'; thread_pcc := pcc' |};
                    thread_systemState := thread_systemState thread |} ->
          Invariant' (m',(Ev_SameThread (machine_curThreadId m) (Ev_Call pcc' rf' (machine_interruptStatus m'))::tr)).
      Admitted.

      Lemma RetSentryStepOk:
        forall m tr m' thread retSentryInst srcReg pcc',  
          GlobalInvariant config m ->
          Invariant' (m, tr) ->
          GlobalInvariant config m' ->
          (forall n : nat,
              n <> machine_curThreadId m ->
              nth_error (machine_threads m') n = nth_error (machine_threads m) n) ->
          nth_error (machine_threads m) (machine_curThreadId m) = Some thread ->
          WfRetSentryInst retSentryInst srcReg ->
          retSentryInst (thread_userState thread, machine_memory m) =
            Ok (pcc', machine_interruptStatus m') ->
          nth_error (machine_threads m') (machine_curThreadId m) =
            Some {| thread_userState := {| thread_rf := thread_rf (thread_userState thread);
                                           thread_pcc := pcc' |};
                    thread_systemState := thread_systemState thread |} ->
          Invariant' (m',(Ev_SameThread (machine_curThreadId m) (Ev_Ret pcc' (thread_rf (thread_userState thread)) (machine_interruptStatus m'))::tr)).
      Admitted.

      Lemma SameThreadStepOk:
        forall m tr m' ev,
          GlobalInvariant config m ->
          Invariant' (m, tr) ->
          GlobalInvariant config m' ->
          SameThreadStep m m' ev ->
          Invariant' (m', ev::tr).
      Proof.
        intros * hginv hinv hginv' hstep.
        pose proof hstep as hstep'.
        inv hstep. destruct_products.
        inv stepOkrl.
        - rename H0 into hstep. revert hstep.
          cbv [threadStepFunction exceptionState uc sc fst snd mem ints rf mepcc pcc sts].
          repeat (case_match; intros; simplify_eq); rewrite threadIdEq in *.
          + (* generalInstOk *)
            eapply GeneralStepOk with (m := m); eauto.
          + (* generalInstExn *)
            eapply ExceptionStepOk with (m := m); eauto.
          + (* callSentryOk *)
            eapply CallSentryStepOk with (m := m); eauto.
          + (* callSentryExn *)
            eapply ExceptionStepOk with (m := m); eauto.
          + (* retSentryOk *)
            eapply RetSentryStepOk with (m := m); eauto.
          + (* retSentryExn *)
            eapply ExceptionStepOk with (m := m); eauto.
          + (* Inst Exn *)
            eapply ExceptionStepOk with (m := m); eauto.
        - (* Fetch Exception *)
          cbv [threadStepFunction exceptionState uc sc fst snd mem ints rf mepcc pcc sts] in *.
          rewrite threadIdEq in *.
          eapply ExceptionStepOk with (m := m); eauto.
      Qed.
      
      Lemma InvariantStep (s: State) :
        forall t,
        Invariant s ->
        MachineStep s t ->
        Invariant t.
      Proof.
        cbv[Invariant].
        intros * hinv hstep. destruct s. destruct t.
        cbv [fst snd] in *.
        destruct_products.
        assert (GlobalInvariant config m0) as hglobal' by (eapply GlobalInvariantStep; eauto).
        split; auto.
        inv hstep.
        - constructor.
          + pose proof (Inv_CompartmentIsolation _ hinvr) as hisolation. auto.
          + pose proof (Inv_IsolatedThreads _ hinvr) as hisolation. auto.
        - eapply SameThreadStepOk with (m := m); eauto.
      Qed.

      Lemma InvariantUse (s: State) :
        Invariant s ->
        PIsolation s.
      Proof.
        cbv[Invariant].
        intros * [hginv hinv].
        by (eapply Inv_IsolatedThreads).
      Qed.

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
        | H: nth_error (configLibraries _) _ = Some ?comp,
        H1: In ?addr (libraryFootprint ?comp) |- _ =>
            let H' := fresh H1 "footprint" in 
            learn_hyp (libraryInConfigFootprint _ _ _ _ H H1) as H'
   end.
Ltac destruct_and_save H :=
  let H' := fresh H in
  pose proof H as H';
  destruct H'.

            
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

      Lemma SentriesInitiallyIsolated:
        forall idx1 idx2 initial_machine c1 cap addr,
          ValidInitialState config initial_machine ->
          idx1 <> idx2 ->
          nth_error (configCompartments config) idx1 = Some c1 ->
          ReachableCap initial_machine.(machine_memory) (capsOfCompartment c1) cap ->
          isSentry cap = true ->
          In addr cap.(capAddrs) ->
          AddrHasProvenance config addr (Provenance_Compartment idx2) ->
          False.
      Proof.
        intros * hinit hneq hc1 hreachable hsentr haddr hprovenance.
        saturate_invariants.
        assert (InLibraryFootprint config addr).
        { eapply WFCompartment_ImportEntries; eauto.
          eapply WFCompartment_Sentries; eauto.
        }
        inv hprovenance.
        cbv [InLibraryFootprint] in *. destruct_products.
        unsafe_saturate_list. destruct_products; option_simpl.
        saturate_footprints.
        simplify_Separated.
      Qed.

      Lemma PCompartmentIsolation_InitCompartments:
        forall initial_machine,
          ValidInitialState config initial_machine ->
          CompartmentIsolation initial_machine.
      Proof.
        cbv[CompartmentIsolation IsolatedFromCompartment].
        intros * hvalid * hneq hisolated * hc1 hc2.
        repeat split_and.
        - eapply AddressesInitiallyIsolated with (3 := hc1) (4 := hc2); eauto.
        - cbv[SentriesIsolatedFromCompartment]. intros.
          eapply SentriesInitiallyIsolated with (3 := hc1); eauto.
        - consider MutuallyIsolatedCompartment.
          cbv[SealedDataCapsIsolatedFromCompartment].
          intros. destruct_products; option_simpl. eapply hisolatedrr; eauto.
          eapply ReachableCaller; eauto.
          eapply WFCompartment_SealedDataCap with (config := config); cbv[isSealedDataCap];
            saturate_invariants.
      Qed.
Lemma SubsetCapsOfUserTS:
  forall (thread: Thread), 
    Subset (capsOfUserTS (thread_userState thread)) (capsOfThread thread).
Proof.
  cbv[Subset capsOfThread].
  intros. rewrite in_app_iff. auto. 
Qed.          
Ltac split_ands := repeat split_and.
Lemma ReachableAddrSubset:
  forall caps' mem addr sz p cs cbs caps,
  ReachableAddr mem caps' addr sz p cs cbs ->
  Subset caps' caps ->
  ReachableAddr mem caps addr sz p cs cbs.
Proof.
  cbv[Subset].
  intros. inv H.
  constructor; auto.
  eapply ReachableCapIncrease; eauto.
Qed.

      Lemma ReachableRWXAddrSubset:
        forall mem caps addr caps',
          ReachableRWXAddr mem caps' addr ->
          Subset caps' caps ->
          ReachableRWXAddr mem caps addr.
      Proof.
        cbv[ReachableRWXAddr]. 
        intros. destruct_products.
        do 3 eexists; split; eauto; eapply ReachableAddrSubset; eauto.
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

      Lemma RestrictRefl: forall (x: Cap), Restrict x x.
      Proof.
        intros. cbv[Restrict].
        case_match; constructor; cbv[EqSet Subset SealEq]; auto.
        all: reflexivity.
      Qed.
      Lemma RestrictTrans:
        forall (x y z: Cap),
          Restrict x y -> Restrict y z -> Restrict x z.
      Proof.
        cbv[Restrict]. intros. repeat case_match;
        repeat match goal with
        | H: RestrictSealed _ _ |- _ => destruct H
        | H: RestrictUnsealed _ _ |- _ => destruct H
          end; constructor; cbv[EqSet SealEq Subset] in *; auto; try rewrite_solve.
        all: intros *;
             try match goal with
             | H: _ |- _ => rewrite H 
             end; auto.
        all: repeat match goal with
             | _ => progress option_simpl 
             | H: _ = Some _ |- _ => rewrite H in *
             | H: _ = None |- _ => rewrite H in *
               end.
      Qed.

      Lemma RestrictSealedEq:
        forall (c c': Cap),
        Restrict c c' ->
        c.(capSealed) = c'.(capSealed).      
      Proof.
        cbv[Restrict]. intros. case_match;
          destruct H; cbv[SealEq] in *; rewrite_solve.
      Qed.
      Lemma RestrictCapSealingKeysSubset:
        forall (c c': Cap),
        Restrict c c' ->
        Subset c'.(capSealingKeys) c.(capSealingKeys).
      Proof.
        cbv[Restrict]. intros. case_match;
          destruct H; cbv[EqSet Subset] in *; auto.
        intros. rewrite<-restrictSealedSealingKeysEq; auto.
      Qed.
      Lemma RestrictCapUnsealingKeysSubset:
        forall (c c': Cap),
        Restrict c c' ->
        Subset c'.(capUnsealingKeys) c.(capUnsealingKeys).
      Proof.
        cbv[Restrict]. intros. case_match;
          destruct H; cbv[EqSet Subset] in *; auto.
        intros. rewrite<-restrictSealedUnsealingKeysSubset; auto.
      Qed.
      Lemma RestrictCapAddrsSubset:
        forall (c c': Cap),
        Restrict c c' ->
        Subset c'.(capAddrs) c.(capAddrs).
      Proof.
        cbv[Restrict]. intros. case_match;
          destruct H; cbv[EqSet Subset] in *; auto.
        intros. rewrite<-restrictSealedAddrsEq; auto.
      Qed.

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
Lemma setCapSealedNoneEq:
  forall (c: Cap), capSealed c = None -> setCapSealed c None = c.
Proof.
  cbv[setCapSealed]. destruct c; intros; cbn in *; subst; auto.
Qed.
Lemma setCapSealed_inv:
  forall (x: Cap) y z,
  setCapSealed (setCapSealed x y) z = setCapSealed x z.
Proof.
  cbv[setCapSealed]. reflexivity.
Qed.
Lemma RestrictSetCapUnsealed:
  forall (y z: Cap),            
    Restrict y z ->
    Restrict (setCapSealed y None) (setCapSealed z None).
Proof.
  intros. cbv[Restrict] in *. cbv[setCapSealed]. cbn.
  case_match; inv H; constructor; cbv[SealEq]; cbn; auto.
  all: cbv [EqSet Subset] in *; intros *; 
             try match goal with
             | H: _ |- _ => rewrite H 
             end; auto.
Qed.

      (* For CSP *)
      Lemma ReachableCapRestrictCSP:
        forall mem cap caps x,
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
          specialize RestrictCapAddrsSubset with (1 := H0); intros.
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
        pose proof (ValidInitialCSP _ _ _ hinit) as hvalidcsp. consider @ValidCSP.
        destruct_products.
        split_ands.
        - cbv[AddrsIsolatedFromCompartment]. intros.
          eapply haddr; eauto. simplify_provenance; destruct_products.
          consider ReachableRWXAddr. destruct_products. simplify_provenance.
          do 3 eexists; split; eauto.
          constructor; auto.
          eapply ReachableCapRestrictCSP with (x := x.(initThreadCSP)); auto.
          + eapply ValidInitialThread_stackUntagged; eauto.
          + rewrite setCapSealedNoneEq by auto. intros hrestrict.
            apply RestrictCapAddrsSubset in hrestrict. cbv[Subset] in *.
            assert (In addr (stackFootprint x)).
            { apply hrestrict. apply ina. constructor. auto. }
            saturate_footprints; saturate_list; simplify_Separated.
          + eapply InitialThreadCapSubset; eauto.
        - cbv[SentriesIsolatedFromCompartment]. intros.
          eapply hsentries; eauto; simplify_provenance; destruct_products.
          eapply ReachableCapRestrictCSP with (x := x.(initThreadCSP)); auto.
          + eapply ValidInitialThread_stackUntagged; eauto.
          + intros hrestrict. apply RestrictCapAddrsSubset in hrestrict. 
            fold (stackFootprint x) in *.
            assert (In addr (stackFootprint x)).
            { apply hrestrict. auto. }
            saturate_footprints; saturate_list; simplify_Separated.
          + eapply InitialThreadCapSubset; eauto.
        - cbv[SealedDataCapsIsolatedFromCompartment]. intros.
          eapply hdata; eauto; simplify_provenance; destruct_products.
          eapply ReachableCapRestrictCSP with (x := x.(initThreadCSP)); auto.
          + eapply ValidInitialThread_stackUntagged; eauto.
          + intros hrestrict. apply RestrictCapAddrsSubset in hrestrict.
            fold (stackFootprint x) in *.
            assert (In addr (stackFootprint x)).
            { apply hrestrict; auto. }
            saturate_footprints; saturate_list; simplify_Separated.
          + eapply InitialThreadCapSubset; eauto.
       Qed.

        Lemma ValidInitialThreadImpliesCompartment:
          forall config meta thread cid frame compartment,
          ValidInitialThread config meta thread ->
          hd_error (trustedStack_frames (thread_trustedStack (thread_systemState thread))) =
            Some frame ->
          LookupExportTableCompartment config (trustedStackFrame_calleeExportTable frame) (configInitMemory config) = Some cid ->
          nth_error (configCompartments config) cid = Some compartment ->
          cid = initThreadCompartment meta.
        Proof.
          intros * hvalid hframe hcompartment hid.
          destruct hvalid. destruct_products. unfold hd_error in *.
          simpl_match; option_simpl.
          match goal with
          | H: ValidTrustedStackFrame _ _ _ _ _ |- _ => destruct H
          end; option_simpl; auto.
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
        
      Lemma InvariantInitial :
        forall initial_machine,
        ValidInitialState config initial_machine ->
        Invariant (initial_machine, []).
      Proof.
        intros * hvalid.
        constructor.
        - apply hvalid.
        - pose proof (PCompartmentIsolation_InitCompartments _ hvalid) as hiso.
          pose proof (PCompartmentIsolation_InitThreads _ hvalid hiso) as hthread.
          constructor; auto.
      Qed.
    End WithConfig.

    Theorem MutuallyIsolatedCompartments :
      forall config initial_machine,
        WFConfig config ->
        ValidInitialState config initial_machine ->
        Combinators.always MachineStep (PIsolation config) (initial_machine, []).
    Proof.
      intros * hwf_config hinit_ok.
      econstructor.
      - eapply InvariantInitial; eauto.
      - eapply InvariantStep; eauto.
      - eapply InvariantUse; eauto.
    Qed.

  End WithContext.
End CompartmentIsolation.

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
    Context {LookupExportTableCompartment: Config -> Cap -> FullMemory -> option nat}.
    Notation ValidInitialState := (@ValidInitialState _ Byte Key _ LookupExportTableCompartment).
    Notation ValidInitialThread := (@ValidInitialThread _ Byte Key _ LookupExportTableCompartment). 

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
   - intermediate lemma: on a compartment call, we
 *)
   


(* Invariant: if a (isolated) compartment always sanitizes its caps such that
   - as a caller, all arguments have LG unset
   - as a callee, it never passes caps that have access to its globals in the return argument
     --> how to enforce this?
   then other compartments should only have temporary access to its caps
   -> that is, the only caps a thread in a different compartment should have access to belonging to 
 *)
                                                                              
