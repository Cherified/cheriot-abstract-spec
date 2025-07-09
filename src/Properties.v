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
      H1: nth_error ?xs ?t1 = Some ?s1,
        H2: nth_error ?xs ?t2 = Some ?s2,
          H3: In ?addr ?s1,
            H4: In ?addr ?s2 |- _ =>
        let Heq := fresh in   
        assert (t1 = t2) as Heq;
        [ destruct (PeanoNat.Nat.eq_dec t1 t2); [ by auto | ]  | subst ]
    end.

Ltac simplify_Separated :=
  prepare_Separated; try solve[finish_Separated].

(* Defining the valid initial states of a machine in terms of compartments and thread initialization. *)
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

    (* TODO: imports? *)
    Record Library :=
      { libraryReadOnly: list Addr
      }.                              

    (* The initial state of a machine is defined in terms of its
       compartments, libraries, the trusted switcher, the initial
       state of the threads, and the initial memory. *)
    Record Config := {
        configCompartments: list Compartment;
        configLibraries: list Library;
        configSwitcher: nat; (* Index of the switcher library *)
        configThreads : list InitialThreadMetadata;
        configInitMemory: FullMemory
        (* configMMIOAddrs: list Addr; *)
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

    Definition capsOfCompartment (c: Compartment) :=
      c.(compartmentPCC)::c.(compartmentCGP)::(map capsOfImportEntry c.(compartmentImports)).
    Definition AddrInCompartment (config: Config) (cid: nat) (addr: Addr): Prop :=
      exists compartment,
        nth_error config.(configCompartments) cid = Some compartment /\
        In addr (compartmentFootprint compartment).

    (* TODO: Not sufficient; need to include sealed caps. *)
    (* The addresses reachable from each compartment are all
       reachable from PCC, CGP, or import table.
     *)
    Definition InitialCompartmentAddressesOk (mem: FullMemory) (compartment: Compartment) : Prop :=
      forall a, ReachableRWXAddr mem (capsOfCompartment compartment) a ->
                In a (compartmentFootprint compartment).
                
    (* TODO *)
    Definition ValidUnsealedCap (c: Cap) : Prop :=
      In c.(capCursor) c.(capAddrs) /\ c.(capSealed) = None.

    Record WFCompartment (mem: FullMemory) (c: Compartment) :=
      { WFCompartment_ReachableRWXAddr: InitialCompartmentAddressesOk mem c
      ; WFCompartment_PCC: c.(compartmentPCC).(capSealed) = None
      }.                                                                       

    Definition WFSwitcher (c: Library) : Prop := True.

    Definition ConfigFootprints (config: Config) :=
        (* (configMMIOAddrs config) :: *)
          (map compartmentFootprint config.(configCompartments))
            ++ (map stackFootprint config.(configThreads))
            ++ (map libraryFootprint config.(configLibraries)).

    Record WFConfig (config: Config) := {
        WFConfig_footprintDisjoint: Separated (ConfigFootprints config);
        WFConfig_compartmentMemory:
          Forall (WFCompartment config.(configInitMemory)) config.(configCompartments);
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

    
    Definition ValidTrustedStackFrame (frame: TrustedStackFrame) (meta: InitialThreadMetadata) (c: Compartment): Prop :=
      Restrict c.(compartmentPCC) frame.(trustedStackFrame_calleeExportTable) /\
      Restrict meta.(initThreadCSP) frame.(trustedStackFrame_CSP) /\
      ValidUnsealedCap frame.(trustedStackFrame_calleeExportTable).

    Record ValidInitialThread (config: Config) (meta: InitialThreadMetadata) (t: Thread) : Prop :=
      { ValidInitialThread_addrs:
        exists compartment,
        nth_error config.(configCompartments) meta.(initThreadCompartment) = Some compartment /\
          forall a, ReachableRWXAddr config.(configInitMemory) (capsOfThread t) a ->
                    In a (stackFootprint meta) \/
                    In a (compartmentFootprint compartment)
      ; ValidInitialThread_trustedStack:
        exists compartment
,
        nth_error config.(configCompartments) meta.(initThreadCompartment) = Some compartment /\
        exists frame, t.(thread_systemState).(thread_trustedStack).(trustedStack_frames) = [frame] /\ ValidTrustedStackFrame frame meta compartment
      }.                         
                    
    Record ValidInitialState (config: Config) (m: Machine) : Prop :=
      { ValidInit_memory: m.(machine_memory) = config.(configInitMemory)
      ; ValidInit_threads: Forall2 (ValidInitialThread config) config.(configThreads) m.(machine_threads) 
      ; ValidInit_invariant: GlobalInvariant config m
      }.

    Hint Resolve Inv_curThread : invariants.
    Hint Resolve Inv_validRf: invariants.
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
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Notation ValidInitialState := (@ValidInitialState _ Byte Key).
    Notation ValidTrustedStackFrame := (@ValidTrustedStackFrame Byte Key).
    (* Compartments are connected on the callgraph *)
    (* TODO: double check *)
    Inductive ReachableCompartment : Config -> nat -> nat -> Prop :=
    | ReachableSelf:
        forall config idx,
          WFConfig config ->
          idx < length config.(configCompartments) ->
          ReachableCompartment config idx idx
    | ReachableCaller:
        forall config idx1 idx2 c2 idx3 cap,
          WFConfig config ->
          ReachableCompartment config idx1 idx2 ->
          nth_error config.(configCompartments) idx2 = Some c2 ->
          In (ImportEntry_SealedCapToExportEntry cap) c2.(compartmentImports) ->
          AddrHasProvenance config cap.(capCursor) (Provenance_Compartment idx3) ->
          ReachableCompartment config idx1 idx3
     | ReachableCallee:
        forall config idx1 idx2 c3 idx3 cap,
          WFConfig config ->
          ReachableCompartment config idx1 idx2 ->
          nth_error config.(configCompartments) idx3 = Some c3 ->
          In (ImportEntry_SealedCapToExportEntry cap) c3.(compartmentImports) ->
          AddrHasProvenance config cap.(capCursor) (Provenance_Compartment idx2) ->
          ReachableCompartment config idx1 idx3.
             
    (* NB: there is (not-needed-here) nuance with library calls.
     * TODO: we might need to special case the switcher.
     * TODO: is this safe?
     *)
    Definition ThreadInCompartment (config: Config) (t: Thread) (cid: nat) : Prop :=
      exists frame,
        hd_error t.(thread_systemState).(thread_trustedStack).(trustedStack_frames) = Some frame /\
        AddrHasProvenance config frame.(trustedStackFrame_calleeExportTable).(capCursor) (Provenance_Compartment cid).


    Definition MutuallyIsolatedCompartment (config: Config) (idx1 idx2: nat) : Prop :=
      (ReachableCompartment config idx1 idx2 -> False).

    Section WithConfig.
      Variable config: Config.
      Variable (pf_wf_config: WFConfig config).
      (* Variable initialMachine: Machine. *)

      (* If compartment idx1 is isolated from compartment idx2, then
         any address belonging to compartment idx1 should not be
         reachable by any thread running in compartment idx2.
       *)
      Definition PCompartmentIsolation (st: State):=
        let '(machine, tr) := st in 
        forall idx1 idx2,
          idx1 <> idx2 ->
          MutuallyIsolatedCompartment config idx1 idx2 ->
          forall thread,
          In thread machine.(machine_threads) ->
          ThreadInCompartment config thread idx2 ->
          (forall addr,
             AddrInCompartment config idx1 addr ->
             ReachableRWXAddr machine.(machine_memory) (capsOfThread thread) addr ->
             False).

      Record Invariant' (st: State) : Prop :=
        { Inv_CompartmentIsolation: PCompartmentIsolation st 
        }.                                                           
      
      Definition Invariant (st: State) : Prop :=
        GlobalInvariant config (fst st) /\
        Invariant' st.

      Lemma InvariantStep (s: State) :
        forall t,
        Invariant s ->
        MachineStep s t ->
        Invariant t.
      Admitted.

      Lemma InvariantUse (s: State) :
        Invariant s ->
        PCompartmentIsolation s.
      Proof.
        cbv[Invariant].
        intros * [hginv hinv].
        by (eapply Inv_CompartmentIsolation).
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
      Lemma ValidTrustedStackFrameCapCursor:
        forall frame meta compartment,
        compartment.(compartmentPCC).(capSealed) = None ->
        ValidTrustedStackFrame frame meta compartment ->
        In (capCursor (trustedStackFrame_calleeExportTable frame))
          (compartmentFootprint compartment).
      Proof.
        cbv [ValidTrustedStackFrame ValidUnsealedCap compartmentFootprint Restrict].
        intros; destruct_products; rewrite in_app_iff.
        left. simpl_match.
        eapply restrictUnsealedAddrsSubset; eauto.
      Qed.

      Lemma PCompartmentIsolation_Init:
        forall initial_machine,
        ValidInitialState config initial_machine ->
        PCompartmentIsolation (initial_machine, []).
      Proof.
        cbv[PCompartmentIsolation].
        intros * hvalid * hneq hisolated * hthread hcompartment * haddr * hreachable.
        consider @AddrInCompartment. consider ThreadInCompartment. consider hd_error.
        repeat match goal with
        | _ => progress destruct_products
        | _ => progress saturate_list
        | _ => progress simpl_match
        | _ => progress option_simpl
        | H: WFConfig _ |- _ => mark (MkMark "WFConfig"); destruct H
        | H: ValidInitialState _ _ |-_ => mark (MkMark "ValidInitialState"); destruct H 
        | H: Forall2 (ValidInitialThread _) _ ?xs,
          H1: In _ ?xs |- _ =>
            mark (MkMark "Forall2_ValidInitialThread");
            let n := fresh "n" in let rest := fresh in 
            apply In_nth_error in H1; destruct H1 as (n & rest);
            eapply Forall2_nth_error2' with (idx := n) in H; eauto; try lia
        | H: ValidInitialThread _ _ _ |- _ => mark (MkMark "ValidInitialThread"); destruct H
                                                                                                    | H: AddrHasProvenance _ _ (Provenance_Compartment _) |- _ => inv H
               end; try lia.
        rewrite ValidInit_memory0 in *.
        specialize ValidInitialThread_addrs0r with (1 := hreachable).
        destruct ValidInitialThread_addrs0r.
        { saturate_footprints. simplify_Separated. }
        { assert (In (capCursor (trustedStackFrame_calleeExportTable frame))
                    (compartmentFootprint compartment0)).
          { eapply ValidTrustedStackFrameCapCursor; eauto.
            eapply WFCompartment_PCC.
            eapply Forall_forall.
            eapply WFConfig_compartmentMemory; eauto.
            eauto with lists.
          }
          saturate_footprints. simplify_Separated.
        }
      Qed.

      Lemma InvariantInitial :
        forall initial_machine,
        ValidInitialState config initial_machine ->
        Invariant (initial_machine, []).
      Proof.
        intros * hvalid.
        constructor.
        - apply hvalid.
        - constructor.
          by (apply PCompartmentIsolation_Init). 
      Qed.
    End WithConfig.

    Theorem CompartmentIsolation :
      forall config initial_machine,
        WFConfig config ->
        ValidInitialState config initial_machine ->
        Combinators.always MachineStep (PCompartmentIsolation config) (initial_machine, []).
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
                                                                              
