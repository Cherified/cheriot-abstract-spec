From Stdlib Require Import List NArith.
Set Primitive Projections.

(* Represents basic permissions *)
Module Perm.
  Inductive t :=
  | Exec
  | System
  | Load
  | Store (* Needed as regions only control storage of Caps *)
  | Cap
  | Sealing
  | Unsealing.
End Perm.

(* A cap X can be stored in a cap Y only if X can be stored in a Label that Y provides *)
(* An example where restricting the label of what can be stored in a cap is useful:
   If a callee fills a cap supplied by the caller, then the callee should not store a cap to its stack into it.
   In CHERIoT, a pointer to its stack is always !GL and can only be stored in SL.
   So to prevent the pointer to the callee's stack from getting stored, the cap supplied by the caller should be !SL
   eventhough the underlying pointer is really in the stack.
 *)
Inductive Label :=
| Local
| NonLocal.

(* Represents Call and Return sentries *)
Inductive Sentry :=
| CallEnableInterrupt
| CallDisableInterrupt
| CallInheritInterrupt
| RetEnableInterrupt
| RetDisableInterrupt.

Section EqSet.
  Context [A: Type].
  Variable l1 l2: list A.
  Definition EqSet := forall x, In x l1 <-> In x l2.

  Theorem Eq_imp_EqSet: l1 = l2 -> EqSet.
  Proof.
    unfold EqSet; intros; subst; tauto.
  Qed.
End EqSet.

Section ListUtils.
  Import ListNotations.
  Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
    firstn i l ++ [e] ++ skipn (S i) l.
End ListUtils.

Section Machine.
  Variable Addr: Type.
  Variable Key: Type.

  Record Cap := {
      capSentry: Sentry;
      capSealed: option Key; (* Whether a cap is sealed, and the sealing key *)
      capPerms: list Perm.t;
      capCanStore: list Label; (* The labels of caps that this cap can store (SL in CHERIoT) *)
      capCanBeStored: list Label; (* The labels of caps where this cap can be stored in (GL and not GL in CHERIoT) *)
      capSealingKeys: list Key; (* List of sealing keys owned by this cap *)
      capUnsealingKeys: list Key; (* List of unsealing keys owned by this cap *)
      capAddrs: list Addr; (* List of addresses representing this cap's bounds *)
      capKeepPerms: list Perm.t; (* Permissions to be the only ones kept when loading using this cap *)
      capKeepCanStore: list Label; (* Labels-of-caps-that-this-cap-can-store to be the only ones kept
                                      when loading using this cap *)
      capKeepCanBeStored: list Label (* Labels-of-caps-where-this-cap-can-be-stored to be the only ones kept
                                        when loading using this cap *)
    }.

  Variable Value: Type.
  Definition CapOrValue : Type:= option Cap * Value.
  Notation Memory_t := (Addr -> CapOrValue).

  Variable Memory: Memory_t.

  Section CapStep.
    Variable y z: Cap.

    Record RestrictEqs : Prop := {
        restrictSentryEq: z.(capSentry) = y.(capSentry);
        restrictSealedEq: z.(capSealed) = y.(capSealed) }.

    Record RestrictUnsealed : Prop := {
        restrictUnsealedEqs: RestrictEqs;
        restrictUnsealedPermsSubset: forall p, In p z.(capPerms) -> In p y.(capPerms);
        restrictUnsealedCanStoreSubset: forall r, In r z.(capCanStore) -> In r y.(capCanStore);
        restrictUnsealedCanBeStoredSubset: forall r, In r z.(capCanBeStored) -> In r y.(capCanBeStored);
        restrictUnsealedSealingKeysSubset: forall k, In k z.(capSealingKeys) -> In k y.(capSealingKeys);
        restrictUnsealedUnsealingKeysSubset: forall k, In k z.(capUnsealingKeys) -> In k y.(capUnsealingKeys);
        restrictUnsealedAddrsSubset: forall a, In a z.(capAddrs) -> In a y.(capAddrs);
        restrictUnsealedKeepPermsSubset: forall p, In p z.(capKeepPerms) -> In p y.(capKeepPerms);
        restrictUnsealedKeepCanStoreSubset: forall p, In p z.(capKeepCanStore) -> In p y.(capKeepCanStore);
        restrictUnsealedKeepCanBeStoredSubset: forall p, In p z.(capKeepCanBeStored) -> In p y.(capKeepCanBeStored) }.

    Record RestrictSealed : Prop := {
        restrictSealedEqs: RestrictEqs;
        restrictSealedPermsEq: EqSet z.(capPerms) y.(capPerms);
        restrictSealedCanStore: forall r, In r z.(capCanStore) -> In r y.(capCanStore);
        (* The following seems to be a quirk of CHERIoT,
           maybe make it equal in CHERIoT ISA if there's no use case for this behavior
           and merge with RestrictUnsealed?
           Here's a concrete example why this is bad:
             I have objects in Global and a set of pointers to these objects also in Global.
             I seal an element of that set (which points to an object) and send to a client.
             Client gets a Global sealed cap, makes it Stack and sends it back to me after finishing processing.
             I unseal it, but I lost my ability to store it back into that set in Global.
             Instead, I need to rederive the Global for the unsealed cap to be able to store into the Global set.
         *)
        restrictSealedCanBeStoredSubset: forall r, In r z.(capCanBeStored) -> In r y.(capCanBeStored);
        restrictSealedSealingKeysEq: EqSet z.(capSealingKeys) y.(capSealingKeys);
        restrictSealedUnsealingKeysSubset: EqSet z.(capUnsealingKeys) y.(capUnsealingKeys);
        restrictSealedAddrsEq: EqSet z.(capAddrs) y.(capAddrs);
        restrictSealedKeepPermsSubset: EqSet z.(capKeepPerms) y.(capKeepPerms);
        restrictSealedKeepCanStoreSubset: EqSet z.(capKeepCanStore) y.(capKeepCanStore);
        restrictSealedKeepCanBeStoredSubset: EqSet z.(capKeepCanBeStored) y.(capKeepCanBeStored) }.

    Definition Restrict : Prop :=
      match y.(capSealed) with
      | None => RestrictUnsealed
      | Some k => RestrictSealed
      end.

    Variable x: Cap.
    (* When a cap y is loaded using a cap x, then the attentuation of x comes into play to create z *)

    Record NonRestrictEqs : Prop := {
        nonRestrictCanStoreEq: z.(capCanStore) = y.(capCanStore);
        nonRestrictSentryEq: z.(capSentry) = y.(capSentry);
        nonRestrictAuthUnsealed: x.(capSealed) = None;
        nonRestrictSealingKeysEq: EqSet z.(capSealingKeys) y.(capSealingKeys);
        nonRestrictUnsealingKeysEq: EqSet z.(capUnsealingKeys) y.(capUnsealingKeys);
        nonRestrictAddrsEq: EqSet z.(capAddrs) y.(capAddrs) }.

    Record AttenuatePerms : Prop := {
        attenuatePerms: forall p, In p z.(capPerms) -> (In p x.(capKeepPerms) /\ In p y.(capPerms));
        attenuateKeepPerms: forall p, In p z.(capKeepPerms) ->
                                      (In p x.(capKeepPerms) /\ In p y.(capKeepPerms)) }.

    Record NonAttenuatePerms : Prop := {
        nonAttenuatePerms: EqSet z.(capPerms) y.(capPerms);
        nonAttenuateKeepPerms: EqSet z.(capKeepPerms) y.(capKeepPerms) }.

    Record AttenuateCanStore : Prop := {
        attenuateCanStore: forall p, In p z.(capCanStore) -> (In p x.(capKeepCanStore) /\ In p y.(capCanStore));
        attenuateKeepCanStore: forall p, In p z.(capKeepCanStore) ->
                                         (In p x.(capKeepCanStore) /\ In p y.(capKeepCanStore)) }.

    Record NonAttenuateCanStore : Prop := {
        nonAttenuateCanStore: EqSet z.(capCanStore) y.(capCanStore);
        nonAttenuateKeepCanStore: EqSet z.(capKeepCanStore) y.(capKeepCanStore) }.

    Record LoadCap : Prop := {
        loadNonRestrictEqs: NonRestrictEqs;
        loadAuthPerm: In Perm.Load x.(capPerms) /\ In Perm.Cap x.(capPerms);
        loadFromAuth: exists a, In a x.(capAddrs) /\ fst (Memory a) = Some y;
        loadSealedEq: z.(capSealed) = y.(capSealed);
        loadAttenuatePerms: match y.(capSealed) with
                            | None => AttenuatePerms
                            | Some k => NonAttenuatePerms
                            end;
        loadAttenuateCanStore: match y.(capSealed) with
                               | None => AttenuateCanStore
                               | Some k => NonAttenuateCanStore
                               end;
        (* This is also a quirk of CHERIoT as in the case of restricting caps.
           Ideally, no attenuation (implicit or explicit) must happen under a seal *)
        loadAttenuateCanBeStored: forall r, In r z.(capCanBeStored) ->
                                            (In r x.(capKeepCanBeStored) /\ In r y.(capCanBeStored));
        loadKeepCanBeStored: match y.(capSealed) with
                             | None => forall r, In r z.(capKeepCanBeStored) ->
                                                 (In r x.(capKeepCanBeStored) /\ In r y.(capKeepCanBeStored))
                             | Some k => EqSet z.(capKeepCanBeStored) y.(capKeepCanBeStored)
                             end}.

    Record SealUnsealEqs : Prop := {
        sealUnsealNonRestrictEqs: NonRestrictEqs;
        sealUnsealNonAttenuatePerms: NonAttenuatePerms;
        sealUnsealNonAttenuateCanStore: NonAttenuateCanStore;
        sealUnsealCanBeStoredEq: EqSet z.(capCanBeStored) y.(capCanBeStored);
        sealUnsealKeepCanBeStoredEq: EqSet z.(capKeepCanBeStored) y.(capKeepCanBeStored) }.

    (* Cap z is the sealed version of cap y using a key in x *)
    Record Seal : Prop := {
        sealEqs: SealUnsealEqs;
        sealOrigUnsealed: y.(capSealed) = None;
        sealNewSealed: exists k, In k x.(capSealingKeys) /\ z.(capSealed) = Some k }.

    Record Unseal : Prop := {
        unsealEqs: SealUnsealEqs;
        unsealOrigSealed: exists k, In k x.(capUnsealingKeys) /\ y.(capSealed) = Some k ;
        unsealNewUnsealed: z.(capSealed) = None }.
  End CapStep.

  Section Transitivity.
    Variable origSet: list Cap.

    (* Transitively reachable cap with permissions removed according to transitive properties *)
    Inductive ReachableCap: Cap -> Prop :=
    | Refl (c: Cap) (inPf: In c origSet) : ReachableCap c
    | StepRestrict y (yPf: ReachableCap y) z (yz: Restrict y z) : ReachableCap z
    | StepLoadCap x (xPf: ReachableCap x) y z (xyz: LoadCap x y z): ReachableCap z
    | StepSeal x (xPf: ReachableCap x) y (yPf: ReachableCap y) z (xyz: Seal x y z): ReachableCap z
    | StepUnseal x (xPf: ReachableCap x) y (yPf: ReachableCap y) z (xyz: Unseal x y z): ReachableCap z.

    (* Transitively reachable addr listed with permissions, canStore and canBeStored *)
    Inductive ReachableAddr: Addr -> list Perm.t -> list Label -> list Label -> Prop :=
    | HasAddr c (cPf: ReachableCap c) a (ina: In a c.(capAddrs)) (notSealed: c.(capSealed) = None)
      : ReachableAddr a c.(capPerms) c.(capCanStore) c.(capCanBeStored).

    Definition ReachableCaps newCaps := forall c, In c newCaps -> ReachableCap c.

    Section UpdMem.
      Variable NewMemory: Memory_t.
      Variable stAddrCap: Cap.
      Definition BasicStPerm := ReachableCap stAddrCap /\ In Perm.Store stAddrCap.(capPerms) /\
                                  stAddrCap.(capSealed) = None.
      Definition modifyMemValue := (exists a, In a stAddrCap.(capAddrs) /\ snd (Memory a) <> snd (NewMemory a)) ->
                                   BasicStPerm.
      Definition removeMemCap := (exists a, In a stAddrCap.(capAddrs) /\ fst (Memory a) <> None /\
                                              fst (NewMemory a) = None) ->
                                 BasicStPerm.
      Variable stDataCap: Cap.
      Definition modifyMemCap := (exists a, In a stAddrCap.(capAddrs) /\
                                              fst (NewMemory a) = Some stDataCap /\
                                              fst (Memory a) <> Some stDataCap) ->
                                 BasicStPerm /\ ReachableCap stDataCap /\
                                   exists l, In l stAddrCap.(capCanStore) /\ In l stDataCap.(capCanBeStored).
    End UpdMem.
  End Transitivity.


  Section Machine.
    Import ListNotations.
    Variable ExnHandlerType : Type. (* In CHERIoT: rich or stackless *)

    Notation PCC := CapOrValue (only parsing).
    Notation MEPCC := CapOrValue (only parsing).
    Notation EXNInfo := Value (only parsing).
    Notation RegIdx := nat (only parsing).

    Definition RegisterFile := list CapOrValue.
    Definition CapAndValue : Type := Cap * Value.

    Record SemanticRegisterFile := {
        rf_returnAddress : CapOrValue;
        rf_csp: CapOrValue;
        rf_cgp: CapOrValue;
        rf_argsAndRets: list CapOrValue;
        rf_argsOnly: list CapOrValue;
        rf_calleeSaved: list CapOrValue;
        rf_other: list CapOrValue;
        rf_targetCalleeEntry : CapOrValue; (* Export table entry for target callee *)
    }.

    (* TODO: decide on a register file representation. RF manipulations are currently buggy. *)
    Variable rfIdx_ra : nat.
    Variable rfToSemanticRf : RegisterFile -> option SemanticRegisterFile.
    Variable semanticRfToConcreteRf : SemanticRegisterFile -> option RegisterFile.

    Inductive InterruptStatus :=
    | InterruptsEnabled
    | InterruptsDisabled.

    Record TrustedStackFrame := {
        trustedStackFrame_CSP : CapAndValue;
        trustedStackFrame_calleeExportTable : CapAndValue;
        trustedStackFrame_errorCounter : N
        (* trustedStackFrame_compartmentIdx : nat; (* Actually a pointer to the compartment's export table *) *)
    }.

    Record TrustedStack := {
        (* trustedStack_shadowRegisters : RegisterFile; *)
        trustedStack_frames : list TrustedStackFrame;
    }.

    Record UserThreadState :=
      { thread_rf : RegisterFile;
        thread_pcc: PCC
      }.

    Record SystemThreadState :=
      { thread_mepcc: MEPCC;
        thread_exceptionInfo: EXNInfo;
        thread_trustedStack: TrustedStack
      }.

    Record Thread := {
        thread_userState : UserThreadState;
        thread_systemState : SystemThreadState
    }.

    Record Machine := {
        machine_memory: Memory_t;
        machine_interruptStatus : InterruptStatus;
        machine_threads : list Thread;
        machine_curThreadId : nat;
    }.

    Section StateTransition.

      Definition ReachableCapFromRf (rf: RegisterFile) cap :=
        forall rf_caps,
        (forall c, In c rf_caps -> exists v, In (Some c, v) rf) /\
        ReachableCap rf_caps cap.

      Inductive FancyStep :=
      | Step_Normal
      | Step_Jalr (sentry: CapAndValue) (opt_linkReg: option RegIdx)
      | Step_CompartmentCall
      | Step_CompartmentRet
      | Step_Exception (exnInfo: Value).

      Definition UserContext : Type := (UserThreadState * Memory_t).
      Definition SystemContext : Type := (SystemThreadState * InterruptStatus).

      Definition ValidContexts : UserContext -> SystemContext -> Prop.
      Admitted.

      Definition step_t : Type := (UserContext -> SystemContext ->
                                   FancyStep * UserContext * SystemContext).

      (* A user step should only update state by:
         - updating register file to other cap/value reachable from memory
         - updating memory according to permissions of reachable caps, and as a function of values reachable from caps
         - be defined by value in memory at PCC?
         - call sentries that are reachable
         - only user-mode exception codes (technically)
       *)
      Definition WF_normal_user_step : UserContext -> (UserContext -> Prop) -> Prop .
      Admitted.

      Definition WF_normal_system_step : UserContext -> SystemContext -> (UserContext -> SystemContext -> Prop)
                                         -> Prop.
      Admitted.

      Definition UserContextHasSystemPerm (ctx: UserContext) : Prop :=
        let '(userThread, _) := ctx in
        match userThread.(thread_pcc) with
        | (Some cap, _) => In Perm.System cap.(capPerms)
        | (None, _) => False
        end.

      Inductive WF_step' : UserContext -> SystemContext -> (FancyStep -> UserContext -> SystemContext -> Prop)
                           -> Prop :=
      | WFStep_User :
          forall userCtx sysCtx mid post,
          WF_normal_user_step userCtx mid ->
          (forall userCtx', mid userCtx' ->
                       post Step_Normal userCtx' sysCtx) ->
          WF_step' userCtx sysCtx post
      | WFStep_System :
          forall userCtx sysCtx mid post,
          UserContextHasSystemPerm userCtx ->
          WF_normal_system_step userCtx sysCtx mid ->
          (forall userCtx' sysCtx', mid userCtx' sysCtx' ->
                               post Step_Normal userCtx' sysCtx') ->
          WF_step' userCtx sysCtx post
      | WFStep_Jalr :
          forall userCtx sysCtx post,
          False -> (* TODO *)
          WF_step' userCtx sysCtx post
      | WFStep_CompartmentCall :
          forall userCtx sysCtx mid post,
          WF_normal_user_step userCtx mid ->
          (forall userCtx', mid userCtx' ->
                       post (Step_CompartmentCall) userCtx' sysCtx) ->
          WF_step' userCtx sysCtx post
      | WFStep_CompartmentRet :
          forall userCtx sysCtx mid post,
          (forall userCtx', mid userCtx' ->
                       post (Step_CompartmentRet) userCtx' sysCtx) ->
          WF_step' userCtx sysCtx post
      | WFStep_ThrowException :
          forall userCtx sysCtx post mid exnInfo,
          WF_normal_user_step userCtx mid ->
          (forall userCtx', mid userCtx' ->
                       post (Step_Exception exnInfo) userCtx' sysCtx) ->
          WF_step' userCtx sysCtx post.

      Definition WF_step (fn: step_t): Prop :=
        forall userCtx sysCtx post,
          let '(stepRes, userCtx', sysCtx') := fn userCtx sysCtx in
          ValidContexts userCtx sysCtx ->
          post stepRes userCtx' sysCtx' ->
          WF_step' userCtx sysCtx post.

      Class StepFn := {
          stepFn : step_t;
          stepFn_ok: WF_step stepFn;
          SWITCHER_exceptionEntryPCC : CapOrValue;
          SWITCHER_compartmentCallPCC: CapOrValue;
          SWITCHER_compartmentRetPCC: CapOrValue
      }.

      Context (MachineStep: StepFn).

      Definition setMachineThread (m: Machine) (tid: nat): Machine :=
        {| machine_memory := m.(machine_memory);
           machine_interruptStatus := m.(machine_interruptStatus);
           machine_threads := m.(machine_threads);
           machine_curThreadId := tid
        |}.

      Definition SameThreadStep (m: Machine)
                                (update_fn: Thread -> Memory_t -> InterruptStatus ->
                                            (Thread -> Memory_t -> InterruptStatus -> Prop) -> Prop)
                                (post: Machine -> Prop) : Prop :=
        let tid := m.(machine_curThreadId) in
        let threads := m.(machine_threads) in
        exists thread, nth_error threads tid = Some thread /\
                  update_fn thread m.(machine_memory) m.(machine_interruptStatus) (fun thread' memory' interrupt' =>
                     post {| machine_memory:= memory';
                             machine_threads := listUpdate threads tid thread';
                             machine_curThreadId := tid;
                             machine_interruptStatus := interrupt'
                          |}).


      Definition setPCCInUserContext (pcc: PCC) (ctx: UserContext) : UserContext :=
        let '(st, mem) := ctx in
        ({| thread_rf := st.(thread_rf);
            thread_pcc := pcc;
          |}, mem).

      Definition updateRFInUserContext (idx: nat) (newValue: PCC) (ctx: UserContext) : UserContext :=
        let '(st, mem) := ctx in
        ({| thread_rf := listUpdate st.(thread_rf) idx newValue;
            thread_pcc := st.(thread_pcc);
          |}, mem).

      (* WIP *)
      Definition do_fancy_step (step: FancyStep) (userCtx: UserContext) (sysCtx: SystemContext)
                               : option (UserContext * SystemContext) :=
        let '(userSt, mem) := userCtx in
        let '(sysSt, istatus) := sysCtx in
        match step with
        | Step_Normal => Some (userCtx, sysCtx)
        | Step_Jalr sentry opt_regidx => None
        | Step_CompartmentCall =>
            (* We must have entered via a (IRQ-disabling ?!) forward sentry.
               cjalr ra --> set ra, PCC, and istatus *)
            Some ((updateRFInUserContext rfIdx_ra userSt.(thread_pcc)
                    (setPCCInUserContext SWITCHER_compartmentCallPCC userCtx)),
                  (sysSt, InterruptsDisabled (* !! *) ))
        | Step_CompartmentRet =>
            Some (setPCCInUserContext SWITCHER_compartmentRetPCC userCtx, sysCtx)
        | Step_Exception exnInfo =>
            Some (setPCCInUserContext SWITCHER_exceptionEntryPCC userCtx,
                  ({|thread_mepcc := userSt.(thread_pcc);
                     thread_exceptionInfo := exnInfo;
                     thread_trustedStack := sysSt.(thread_trustedStack);
                   |}, InterruptsDisabled)
                 )
        end.

      Definition merge_contexts (userCtx: UserContext) (sysCtx: SystemContext)
                                : Thread * Memory_t * InterruptStatus :=
        let '(userState, mem) := userCtx in
        let '(sysState, istatus) := sysCtx in
        ({| thread_userState := userState;
            thread_systemState := sysState
         |}, mem, istatus).

      Definition split_contexts (thread: Thread) (mem: Memory_t) (istatus: InterruptStatus)
                                : UserContext * SystemContext :=
          let userCtx := (thread.(thread_userState), mem) in
          let sysCtx := (thread.(thread_systemState), istatus) in
          (userCtx, sysCtx).

      Definition step_update_fn : Thread -> Memory_t -> InterruptStatus ->
                                  (Thread -> Memory_t -> InterruptStatus -> Prop) -> Prop :=
        fun thread mem istatus post =>
          let '(userCtx, sysCtx) := split_contexts thread mem istatus in
          let '(res, userCtx', sysCtx') := stepFn userCtx sysCtx in
          let '(userCtx', sysCtx') := do_fancy_step res userCtx' sysCtx' in
          let '(thread', mem', istatus') := merge_contexts userCtx' sysCtx' in
          post thread' mem' istatus'.

      Inductive Step : Machine -> (Machine -> Prop) -> Prop :=
      | Step_SwitchThreads:
        forall m tid' post,
          m.(machine_interruptStatus) = InterruptsEnabled ->
          tid' < List.length m.(machine_threads) ->
          post (setMachineThread m tid') ->
          Step m post
      | Step_SameThread :
        forall m post,
          SameThreadStep m step_update_fn post ->
          Step m post.
    End StateTransition.

  End Machine.

  (* Section MachineOld. *)
    (* Inductive ImportTableEntry := *)
    (* | ImportEntry_SealedCapToExportEntry (cap: CapAndValue) *)
    (* | ImportEntry_SentryToLibraryFunction (cap: CapAndValue) (* Code + read-only globals *) *)
    (* | ImportEntry_MMIOCap (cap: CapAndValue). *)

    (* Record ExportTableEntry := { *)
    (*     exportEntryPCC: Value; (* In CHERIoT, offset from compartment PCC *) *)
    (*     exportEntryStackSize: Value; *)
    (*     exportEntryNumArgs : nat; *)
    (*     exportEntryInterruptStatus: InterruptStatus; *)
    (* }. *)

    (* Record Compartment := { *)
    (*     compartmentPCC : CapAndValue; *)
    (*     compartmentCGP : CapAndValue; *)
    (*     compartmentErrorHandlers : list (Value * ExnHandlerType); (* offset from PCC *) *)
    (*     compartmentImportTable : list ImportTableEntry; *)
    (*     compartmentExportTable : list (ExportTableEntry) (* Address where export table entry is stored *) *)
    (* }. *)

    (* Record MachineGhostState := { *)
    (*     compartments: Compartment *)
    (* }. *)

  (*   Variable ExnHandlerType : Type. (* In CHERIoT: rich or stackless *) *)



  (*   Record ExportTableEntry := { *)
  (*       exportEntryPCC: Value; (* In CHERIoT, offset from compartment PCC *) *)
  (*       exportEntryStackSize: Value; *)
  (*       exportEntryNumArgs : nat; *)
  (*       exportEntryInterruptStatus: InterruptStatus; *)
  (*   }. *)

  (*   Record Compartment := { *)
  (*       compartmentPCC : CapOrValue; *)
  (*       compartmentCGP : CapOrValue; *)
  (*       compartmentErrorHandlers : list (Value * ExnHandlerType); (* offset from PCC *) *)
  (*       compartmentImportTable : list ImportTableEntry; *)
  (*       compartmentExportTable : list (Addr * ExportTableEntry) (* Address where export table entry is stored *) *)
  (*       (* compartmentGhostCallArgs : list CallArgs; (* TODO *) *) *)
  (*       (* compartmentGhostReturnArgs : list ReturnArgs *) *)
  (*   }. *)

  (*   (* Each thread has a TrustedStack. The TrustedStack contains: *)
  (*      - A register save area (used for preemption, but also staging space as part of exception handling) *)
  (*      - A TrustedStackFrame for each active cross-compartment call -- there is always one frame *)
  (*        - CSP: Caller's stack pointer at time of cross-compartment entry, pointing at switcher's register spills *)
  (*        - Pointer to callee export table, so we can find the error handler *)
  (*        - errorHandlerCount *)
  (*      - (state for unwinding info?) *)
  (*    *) *)
  (*   Record TrustedStackFrame := { *)
  (*       trustedStackFrame_compartmentIdx : nat; (* Actually a pointer to the compartment's export table *) *)
  (*       trustedStackFrame_CSP : CapOrValue *)
  (*   }. *)

  (*   (* Register spill area is currently implicit, in our model. *) *)
  (*   Definition TrustedStack := list TrustedStackFrame. *)

  (*   (* During a cross compartment return: *)
  (*      - If at least one trusted stack frame: *)
  (*          - Pop a trusted stack frame *)
  (*          - Restore the CSP from trusted stack frame *)
  (*          - Restore ra, gp, callee-saved registers from untrusted stack pointed to by above CSP *)
  (*              - This could potentially have been overwritten if callee had access to caller's stack through an argument *)
  (*          - Zero registers not intended for caller (!{ra,sp,gp,s0,s1,a0,a1}) *)
  (*          - Zero callee's stack *)
  (*      - Else: *)
  (*          exit thread *)
  (*    *) *)

  (*   (* Each thread contains: *)
  (*      - Register file *)
  (*      - PCC *)
  (*      - Trusted stack *)
  (*    *) *)
  (*   Definition Thread: Type. *)
  (*   Admitted. *)

  (*   Record Machine := { *)
  (*       machineCompartments : list Compartment; *)
  (*       machineThreads: list Thread; *)
  (*       machineThreadId : nat; *)
  (*       machineMemory : Memory_t; *)
  (*       machineInterruptible : InterruptStatus *)
  (*   }. *)

  (*   Section MachineHelpers. *)
  (*     Definition setMachineThread (m: Machine) (tid: nat): Machine := *)
  (*       {| machineCompartments := m.(machineCompartments); *)
  (*          machineThreads := m.(machineThreads); *)
  (*          machineThreadId := tid; *)
  (*          machineMemory := m.(machineMemory); *)
  (*          machineInterruptible := m.(machineInterruptible) *)
  (*       |}. *)

  (*     Definition SameThreadStep (m: Machine) *)
  (*                               (update_fn: Thread -> Memory_t -> list Compartment -> InterruptStatus -> (Thread -> Memory_t -> InterruptStatus  -> Prop) -> Prop) *)
  (*                               (post: Machine -> Prop) : Prop := *)
  (*       let tid := m.(machineThreadId) in *)
  (*       let threads := m.(machineThreads) in *)
  (*       let compartments := m.(machineCompartments) in *)
  (*       exists thread, nth_error threads tid = Some thread /\ *)
  (*                 update_fn thread m.(machineMemory) compartments m.(machineInterruptible) (fun thread' memory' interrupt' => *)
  (*                    post {| machineCompartments := compartments; (* TODO: update ghost state *) *)
  (*                            machineThreads := listUpdate threads tid thread'; *)
  (*                            machineThreadId := tid; *)
  (*                            machineMemory := memory'; *)
  (*                            machineInterruptible := interrupt' *)
  (*                         |}). *)

  (*   End MachineHelpers. *)

  (*   (* Steps that stay within the same compartment: *)
  (*      - Update PCC + Load/store data; load/store cap; restrict cap; seal/unseal cap *)
  (*      - Execute instruction within switcher *)
  (*    *) *)
  (*   Definition KeepDomainStep *)
  (*     (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*     (post: Thread -> Memory_t -> InterruptStatus -> Prop) : Prop. *)
  (*   Admitted. *)

  (*   (* A thread can invoke capabilities for: *)
  (*      - Return from error handler: *)
  (*          - Ask switcher to install modified registerfile (rederiving PCC from compartment code capability) *)
  (*          - Ask switcher to continue unwinding *)
  (*      - Call/return from exported function via switcher *)
  (*      - Call/return from library function *)
  (*    *) *)
  (*   Definition StepInvokeCapability *)
  (*     (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*     (post: Thread -> Memory_t -> InterruptStatus -> Prop) : Prop. *)
  (*   Admitted. *)

  (*   (* When a (user) thread throws an exception: *)
  (*        If the compartment's "rich" error handler exists and there is sufficient stack space: *)
  (*            Call the compartment's "rich" error handler *)
  (*            - Enable interrupts *)
  (*            - ra: backwards sentry to exception return path of switcher *)
  (*            - sp: stack pointer at time of invocation *)
  (*            - gp: compartment cgp (fresh?) *)
  (*            - Arguments: exception cause/info; pass sp equal to sp with a register spill frame here and above (but with pcc untagged) *)
  (*            - Enable interrupts *)
  (*        Else if the compartment's stackless error handler exists: *)
  (*            Call the compartment's stackless error handler: *)
  (*            - Enable interrupts *)
  (*            - ra: backwards sentry to exception return path of switcher *)
  (*            - sp: stack pointer at time of invocation *)
  (*            - gp: compartment cgp (fresh?) *)
  (*            - Arguments: exception cause/info *)
  (*        Else: unwind the stack: *)
  (*    *) *)
  (*   Definition StepRaiseException *)
  (*     (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*     (post: Thread -> Memory_t -> InterruptStatus -> Prop) : Prop. *)
  (*   Admitted. *)

  (*   Inductive SwitchDomainStep : Machine -> (Machine -> Prop) -> Prop := *)
  (*   | Step_SwitchThreads : *)
  (*     forall m post tid', *)
  (*     m.(machineInterruptible) = InterruptsEnabled -> *)
  (*     tid' < List.length m.(machineThreads) -> *)
  (*     post (setMachineThread m tid') -> *)
  (*     SwitchDomainStep m post *)
  (*   | Step_RaiseException: *)
  (*     forall m post, *)
  (*     SameThreadStep m StepRaiseException post -> *)
  (*     SwitchDomainStep m post *)
  (*   | Step_InvokeCapability: *)
  (*     forall m post, *)
  (*      SameThreadStep m StepInvokeCapability post -> *)
  (*      SwitchDomainStep m post. *)

  (*   (* TODO: we will need ghost state/trace to describe information flow in/out of compartments/threads *) *)
  (*   Inductive Step : Machine -> (Machine -> Prop) -> Prop := *)
  (*   | Step_KeepDomain : *)
  (*     forall m post, *)
  (*     SameThreadStep m KeepDomainStep post -> *)
  (*     Step m post *)
  (*   | Step_SwitchDomain: *)
  (*     forall m post, *)
  (*     SwitchDomainStep m post -> *)
  (*     Step m post. *)

  (* Definition CallArgs : Type. Admitted. *)
  (* Definition ReturnArgs : Type. Admitted. *)


  (* (* Record SemanticRegisterFile := { *) *)
  (* (*     rfRa : CapWithValue; *) *)
  (* (*     rfCGP : CapWithValue; *) *)
  (* (*     rfCSP: CapWithValue; *) *)
  (* (*     rfArgRegs : list CapOrValue; *) *)
  (* (*     rfMiscCallerSavedRegs : list CapOrValue; *) *)
  (* (*     rfMiscCalleeSavedRegs : list CapOrValue; *) *)

  (*   Definition capsFromRf (rf: RegisterFile) : list Cap := *)
  (*     concat (map (fun '(opt_cap, _) => match opt_cap with *)
  (*                                    | Some cap => [cap] *)
  (*                                    | None => [] *)
  (*                                    end) rf). *)

  (*   Definition StackFrame := list CapOrValue. *)

  (*   Record TrustedStackEntry := *)
  (*     { TrustedEntryPCC : CapOrValue; *)
  (*       TrustedEntryCSP : CapOrValue; *)
  (*       TrustedEntryRf : RegisterFile; *)
  (*       TrustedEntryIStatus : InterruptStatus *)
  (*     }. *)

  (*   (* TODO: Trusted stack frame should contain (among other things), CSP that compartment had on entry. *) *)
  (*   Record Thread := { *)
  (*       threadPCC: CapOrValue; (* Offset relative to compartment PCC *) *)
  (*       threadCSP: CapOrValue; (* Semantic CSP? *) *)
  (*       threadRF: RegisterFile; *)
  (*       threadCompartmentIdx: nat; (* Ghost state *) *)
  (*       threadStack : list StackFrame; (* A thread can reach any caps in its topmost stackframe? *) *)
  (*       threadTrustedStack : list TrustedStackEntry *)
  (*   }. *)





  (*   Variable ExnInfo : Type. (* CHERIoT: mtval and mcause *) *)
  (*   Variable validErrorHandlerOffset: CapOrValue -> Value -> CapOrValue -> Prop. *)
  (*   Variable validExnHandlerRf *)
  (*     : ExnInfo (* CapWithValue (* Return sentry to switcher *) *) *)
  (*               -> CapOrValue (* CGP *) *)
  (*               (* -> CapWithValue (* CSP *) *) *)
  (*               -> list CapOrValue (* Caps reachable by CSP? *) *)
  (*               -> RegisterFile *)
  (*               -> Prop. *)
  (*   Variable getHandlerReturnValue : RegisterFile -> CapOrValue. *)


  (*   (* Inductive ThreadEvent := *) *)
  (*   (* | ThreadEvent_KeepDomain (* This could contain information about caps read/stored from memory *) *) *)
  (*   (* | ThreadEvent_InvokeCap (codeCap: CapOrValue) (dataCap: CapOrValue). *) *)
  (*   (* Inductive TraceEvent := *) *)
  (*   (* | Event_SwitchThreads (newidx: nat) *) *)
  (*   (* | Event_ThreadEvent (tid: nat) (ev: ThreadEvent). *) *)


  (*   Inductive ThreadEvent := *)
  (*   | ThreadEvent_XCompartmentCallWithoutSwitcher (rf: RegisterFile) *)
  (*   | ThreadEvent_XCompartmentReturnWithoutSwitcher (rf: RegisterFile) *)
  (*   | ThreadEvent_XCompartmentCall (rf: RegisterFile) *)
  (*   | ThreadEvent_XCompartmentReturn (rf: RegisterFile) *)
  (*   | ThreadEvent_Exception (pc: CapOrValue) (rf: RegisterFile) (exn: ExnInfo) *)
  (*   | ThreadEvent_ExceptionReturn (pc: CapOrValue) (rf: RegisterFile). *)






  (*   Inductive TraceEvent := *)
  (*   | Event_SwitchThreads (newIdx: nat) *)
  (*   | Event_ThreadEvent (tid: nat) (ev: ThreadEvent). *)

  (*   Definition SameThreadStep (m: Machine) *)
  (*                             (update_fn: Thread -> Memory_t -> list Compartment -> InterruptStatus -> (Thread -> Memory_t -> InterruptStatus -> list ThreadEvent -> Prop) -> Prop) *)
  (*                             (post: Machine -> list TraceEvent -> Prop) : Prop := *)
  (*     let tid := m.(machineThreadId) in *)
  (*     let threads := m.(machineThreads) in *)
  (*     let compartments := m.(machineCompartments) in *)
  (*     exists thread, nth_error threads tid = Some thread /\ *)
  (*               update_fn thread m.(machineMemory) compartments m.(machineInterruptible) (fun thread' memory' interrupt' event' => *)
  (*                  post {| machineCompartments := m.(machineCompartments); (* TODO: update ghost state *) *)
  (*                          machineThreads := listUpdate threads tid thread'; *)
  (*                          machineThreadId := tid; *)
  (*                          machineMemory := memory'; *)
  (*                          machineInterruptible := interrupt' *)
  (*                       |} (map (Event_ThreadEvent tid) event')). *)

  (*   (* Load/store data; load/store cap; restrict cap; seal cap *) *)
  (*   Definition KeepDomainStep : Machine -> (Machine -> list TraceEvent -> Prop) -> Prop. *)
  (*   Admitted. *)

  (*   Definition validErrorHandlerPCC (pcc: CapOrValue) (compartment: Compartment) : Prop := *)
  (*     exists offset handlerType, *)
  (*       In (offset, handlerType) compartment.(compartmentErrorHandlers) /\ *)
  (*       validErrorHandlerOffset compartment.(compartmentPCC) offset pcc. *)
  (*   (* Capabilities should not increase *) *)
  (*   Definition validErrorHandlerOffset_ok : (CapOrValue -> Value -> CapOrValue -> Prop) -> Prop. *)
  (*   Admitted. *)


  (*   (* Assumes the top stack frame is non-empty *) *)
  (*   Definition PutCapOrValuesOntoStack (caps: list CapOrValue) (stack: list StackFrame) : option (list StackFrame) := *)
  (*     match stack with *)
  (*     | [] => None *)
  (*     | x::xs =>  Some ((x ++ caps)::xs) *)
  (*     end. *)

  (*   (* Handler asks to return to pcc; ensure it's within bounds of the compartment *) *)
  (*   Definition fixPCC (pcc: CapOrValue) (basePCC : CapOrValue) : option CapOrValue. *)
  (*   Admitted. *)

  (*   Definition restoreRegisters (rf: RegisterFile) (rf': RegisterFile) : Prop. Admitted. *)

  (*   Inductive StepException : Thread -> Memory_t -> list Compartment -> InterruptStatus -> (Thread -> Memory_t -> InterruptStatus -> list ThreadEvent -> Prop) -> Prop := *)
  (*   | StepException_EnterHandler : *)
  (*     forall thread mem compartments istatus compartment pcc' stack' rf' exn stackFrame post, *)
  (*     nth_error compartments thread.(threadCompartmentIdx) = Some compartment -> *)
  (*     validErrorHandlerPCC pcc' compartment -> *)
  (*     List.hd_error thread.(threadStack) = Some stackFrame -> *)
  (*     (* NB: not entirely correct. Technically this alters memory. *) *)
  (*     PutCapOrValuesOntoStack ((None, snd thread.(threadPCC))::thread.(threadRF)) thread.(threadStack) = Some stack' -> *)
  (*     validExnHandlerRf exn compartment.(compartmentCGP) stackFrame rf' -> *)
  (*     post {| threadPCC := pcc'; *)
  (*             threadRF := rf'; *)
  (*             threadCompartmentIdx := thread.(threadCompartmentIdx); *)
  (*             threadStack := stack'; (* TODO: This is incorrect --> maybe add new frame with everything from the previous frame? *) *)
  (*             threadTrustedStack:= (Build_TrustedStackEntry thread.(threadPCC) thread.(threadRF) istatus)::thread.(threadTrustedStack) *)
  (*          |} *)
  (*          mem InterruptsEnabled [ThreadEvent_Exception thread.(threadPCC) thread.(threadRF) exn] -> *)
  (*     (* Enable interrupts when entering exception handler *) *)
  (*     (* Global memory should not change *) (* TODO: technically stack memory does change ... *) *)
  (*     StepException thread mem compartments istatus post *)
  (*   | StepException_HandlerReturn : *)
  (*     forall thread mem compartments istatus post compartment trustedStackEntry pcc' rf', *)
  (*       nth_error compartments thread.(threadCompartmentIdx) = Some compartment -> *)
  (*       List.hd_error thread.(threadTrustedStack) = Some trustedStackEntry -> *)
  (*       fixPCC (getHandlerReturnValue thread.(threadRF)) compartment.(compartmentPCC) = Some pcc' -> *)
  (*       restoreRegisters trustedStackEntry.(TrustedEntryRf) rf' -> *)
  (*       post {| threadPCC := pcc'; *)
  (*               threadRF := rf'; *)
  (*               threadCompartmentIdx := thread.(threadCompartmentIdx); *)
  (*               threadStack := List.tl thread.(threadStack); (* ??? *) *)
  (*               threadTrustedStack:= List.tl thread.(threadTrustedStack) (* ??? *) *)
  (*            |} *)
  (*          mem *)
  (*          trustedStackEntry.(TrustedEntryIStatus) (* ??? *) *)
  (*          [ThreadEvent_ExceptionReturn thread.(threadPCC) thread.(threadRF) ] -> *)
  (*     StepException thread mem compartments istatus post. *)
  (*   (* TODO: Unwind stack *) *)

  (*   Definition StepXCompartmentCallViaSwitcher (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*                                              (post: Thread -> Memory_t -> InterruptStatus -> list ThreadEvent -> Prop) : Prop. *)
  (*   Admitted. *)
  (*   Definition StepXCompartmentReturnViaSwitcher (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*                                                (post: Thread -> Memory_t -> InterruptStatus -> list ThreadEvent -> Prop) : Prop. *)
  (*   Admitted. *)
  (*   Definition StepXCompartmentCallWithoutSwitcher (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*                                                  (post: Thread -> Memory_t -> InterruptStatus -> list ThreadEvent -> Prop) : Prop. *)
  (*   Admitted. *)
  (*   Definition StepXCompartmentReturnWithoutSwitcher (t: Thread) (m: Memory_t) (compartments: list Compartment) (istatus: InterruptStatus) *)
  (*                                                    (post: Thread -> Memory_t -> InterruptStatus -> list ThreadEvent -> Prop) : Prop. *)
  (*   Admitted. *)

  (*   Definition CanSwitchThread (m: Machine) (newTid: nat) : Prop := *)
  (*     m.(machineInterruptible) = InterruptsEnabled /\ *)
  (*       newTid < List.length m.(machineThreads). *)

  (*   Inductive SwitchDomainStep : Machine -> (Machine -> list TraceEvent -> Prop) -> Prop := *)
  (*   | Step_RaiseException *)
  (*   | Step_InvokeCapability *)
  (*   . *)




  (*   | Step_ThrowException : *)
  (*     forall m post mid, *)
  (*       SameThreadStep m StepException mid -> *)
  (*      (forall m' tr, mid m' tr -> post m' tr) -> *)
  (*      SwitchDomainStep m post *)
  (*   | Step_XCompartmentCallViaSwitcher: *)
  (*     forall m post mid, *)
  (*       SameThreadStep m StepXCompartmentCallViaSwitcher mid -> *)
  (*      (forall m' tr, mid m' tr -> post m' tr) -> *)
  (*      SwitchDomainStep m post *)
  (*   | Step_XCompartmentReturnViaSwitcher: *)
  (*     forall m post mid, *)
  (*       SameThreadStep m StepXCompartmentReturnViaSwitcher mid -> *)
  (*      (forall m' tr, mid m' tr -> post m' tr) -> *)
  (*      SwitchDomainStep m post *)
  (*   | Step_XCompartmentCallWithoutSwitcher: *)
  (*     forall m post mid, *)
  (*       SameThreadStep m StepXCompartmentCallWithoutSwitcher mid -> *)
  (*      (forall m' tr, mid m' tr-> post m' tr) -> *)
  (*      SwitchDomainStep m post *)
  (*   | Step_XCompartmentReturnWithoutSwitcher: *)
  (*     forall m post mid, *)
  (*       SameThreadStep m StepXCompartmentReturnWithoutSwitcher mid -> *)
  (*      (forall m' tr, mid m' tr-> post m' tr) -> *)
  (*      SwitchDomainStep m post. *)


  (* End Machine. *)
End Machine.

Module CHERIoTValidation.
  From Stdlib Require Import ZArith.
  Import ListNotations.
  Local Open Scope N_scope.
  Inductive CompressedPerm :=
  | MemCapRW (GL: bool) (SL: bool) (LM: bool) (LG: bool) (* Implicit: LD, MC, SD *)
  | MemCapRO (GL: bool) (LM: bool) (LG: bool) (* Implicit: LD, MC *)
  | MemCapWO (GL: bool) (* Implicit: SD, MC *)
  | MemDataOnly (GL: bool) (LD: bool) (SD: bool) (* Implicit: None *)
  | Executable (GL: bool) (SR: bool) (LM: bool) (LG: bool) (* Implicit: EX, LD, MC *)
  | Sealing (GL: bool) (U0: bool) (SE: bool) (US: bool) (* Implicit: None *).

  Record cheriot_cap :=
  { reserved: bool;
    permissions: CompressedPerm;
    otype: N; (* < 8 *)
    base: N;
    top: N;
    addr: N;
  }.

  Record Perm :=
    {
      EX : bool; (* PERMIT_EXECuTE *)
      GL : bool; (* GLOBAL *)
      LD : bool; (* PERMIT_LOAD *)
      SD : bool; (* PERMIT_STORE *)
      SL : bool; (* PERMIT_STORE_LOCAL_CAPABILITY *)
      SR : bool; (* PERMIT_ACCESS_SYSTEM_REGISTERS *)
      SE : bool; (* PERMIT_SEAL *)
      US : bool; (* PERMIT_UNSEAL *)
      U0 : bool; (* USER_PERM0 *)
      LM : bool; (* PERMIT_LOAD_MUTABLE *)
      LG : bool; (* PERMIT_LOAD_GLOBAL *)
      MC : bool; (* PERMIT_LOAD_STORE_CAPABILITY *)
    }.

  Definition decompress_perm (p: CompressedPerm) : Perm :=
    match p with
    | MemCapRW gl sl lm lg =>
        {| EX := false;
           GL := gl;
           LD := true;
           SD := true;
           SL := sl;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := lm;
           LG := lg;
           MC := true
        |}
    | MemCapRO gl lm lg =>
        {| EX := false;
           GL := gl;
           LD := true;
           SD := false;
           SL := false;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := lm;
           LG := lg;
           MC := true
        |}
    | MemCapWO gl =>
        {| EX := false;
           GL := gl;
           LD := false;
           SD := true;
           SL := false;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := false;
           LG := false;
           MC := true
        |}
    | MemDataOnly gl ld sd =>
        {| EX := false;
           GL := gl;
           LD := ld;
           SD := sd;
           SL := false;
           SR := false;
           SE := false;
           US := false;
           U0 := false;
           LM := false;
           LG := false;
           MC := false
        |}
    | Executable gl sr lm lg =>
        {| EX := true;
           GL := gl;
           LD := true;
           SD := false;
           SL := false;
           SR := sr;
           SE := false;
           US := false;
           U0 := false;
           LM := lm;
           LG := lg;
           MC := true
        |}
    | Sealing gl u0 se us =>
        {| EX := false;
           GL := gl;
           LD := false;
           SD := false;
           SL := false;
           SR := false;
           SE := se;
           US := us;
           U0 := u0;
           LM := false;
           LG := false;
           MC := false
        |}
    end.

  Definition mk_abstract_cap (c: cheriot_cap) : Cap nat N :=
    let d := decompress_perm c.(permissions) in
    {| capCanStore := if d.(SL) then [Local;NonLocal] else [NonLocal];
       capSentry := match c.(otype) with
                    | 0 => UnsealedJump
                    | 1 => CallInheritInterrupt
                    | 2 => CallDisableInterrupt
                    | 3 => CallEnableInterrupt
                    | 4 => RetDisableInterrupt
                    | 5 => RetEnableInterrupt
                    | (* 6 & 7 *) _ => UnsealedJump (* TODO! capSentry ⊆ capSealed *)
                    end;
       capSealed := match c.(otype) with
                    | 0 => None
                    | _ => Some c.(otype)
                    end;
       capPerms := filter (fun p => match p with
                                    | Perm.Exec => d.(EX)
                                    | Perm.System => d.(SR)
                                    | Perm.Load => d.(LD)
                                    | Perm.Store => d.(SD)
                                    | Perm.Cap => d.(MC)
                                    | Perm.Sealing => d.(SE)
                                    | Perm.Unsealing => d.(US)
                                 end)
                     [Perm.Exec;Perm.System;Perm.Load;Perm.Cap;Perm.Sealing;Perm.Unsealing];
       capCanBeStored := if d.(GL) then [Local;NonLocal] else [Local];
       capSealingKeys := [c.(addr)];
       capUnsealingKeys := [c.(addr)];
       capAddrs := seq (N.to_nat c.(base)) (N.to_nat (c.(top) - c.(base)));
       capKeepPerms := filter (fun p => match p with
                                 | Perm.Exec => true
                                 | Perm.System => true
                                 | Perm.Load => true
                                 | Perm.Store => d.(LM)
                                 | Perm.Cap => true
                                 | Perm.Sealing => true
                                 | Perm.Unsealing => true
                                 end)
                         [Perm.Exec;Perm.System;Perm.Load;Perm.Cap;Perm.Sealing;Perm.Unsealing];
       capKeepCanStore := [Local;NonLocal];
       capKeepCanBeStored := if d.(LG) then [Local;NonLocal] else [Local]
     |}.

End CHERIoTValidation.

(* Require Import coqutil.Map.Interface. *)
(* Require Import coqutil.Byte. *)
(* Require Import coqutil.Word.Interface. *)
(* Require coqutil.Word.Properties. *)
(* From Stdlib Require Import Zmod Bits. *)
(* From cheriot Require Import ZmodWord. *)

(* Set Primitive Projections. *)
(* Local Open Scope Z_scope. *)

(* Definition XLEN := 32. *)
(* Definition mword := bits XLEN. *)
(* Notation addr_t := (bits XLEN). *)

(* Module Permissions. *)
(*   Record permissions := *)
(*     { *)
(*       EX : bool; (* PERMIT_EXECTE *) *)
(*       GL : bool; (* GLOBAL *) *)
(*       LD : bool; (* PERMIT_LOAD *) *)
(*       SD : bool; (* PERMIT_STORE *) *)
(*       SL : bool; (* PERMIT_STORE_LOCAL_CAPABILITY *) *)
(*       SR : bool; (* PERMIT_ACCESS_SYSTEM_REGISTERS *) *)
(*       SE : bool; (* PERMIT_SEAL *) *)
(*       US : bool; (* PERMIT_UNSEAL *) *)
(*       U0 : bool; (* USER_PERM0 *) *)
(*       LM : bool; (* PERMIT_LOAD_MUTABLE *) *)
(*       LG : bool; (* PERMIT_LOAD_GLOBAL *) *)
(*       MC : bool; (* PERMIT_LOAD_STORE_CAPABILITY *) *)
(*     }. *)
(* End Permissions. *)

(* Module Otype. *)
(*   Class otype := { *)
(*       t : Type; *)
(*       eqb: t -> t -> bool; *)
(*   }. *)
(* End Otype. *)

(* Module SealType. *)
(*   Section WithOType. *)
(*     Context {ot: Otype.otype}. *)

(*     Inductive t := *)
(*     | Cap_Unsealed *)
(*     | Cap_Sentry (seal: Otype.t) *)
(*     | Cap_Sealed (seal: Otype.t). *)

(*   End WithOType. *)
(* End SealType. *)

(* Module Ecap. *)
(*   (* Reserved bit? *) *)
(*   Record ecap {otype: Otype.otype} := *)
(*     { perms: Permissions.permissions; *)
(*       seal_type: SealType.t; *)
(*       base_addr: addr_t; *)
(*       top_addr: addr_t *)
(*     }. *)
(* End Ecap. *)

(* Module capability. *)
(*   Section WithContext. *)
(*     Context {otype: Otype.otype} . *)
(*     Record capability := *)
(*       { valid: bool; *)
(*         ecap: Ecap.ecap; *)
(*         value: addr_t; *)
(*       }. *)
(*   End WithContext. *)
(* End capability. *)

(* Section Semantics. *)
(*   Context {gpr scr csr: Type}. *)
(*   Context {otype: Otype.otype}. *)
(*   Notation cap := (@capability.capability otype). *)
(*   (* Context {cap_methods: @capability.cap_methods ecap}. *) *)
(*   Context {regfile : map.map gpr cap}. *)
(*   Context {scrfile : map.map scr cap}. *)
(*   Context {csrfile: map.map csr mword}. (* Simplified for now; actually variable length *) *)
(*   Context {mem: map.map mword cap}. *)

(*   (* Context {memTags: map.map tag_t bool}. *) *)
(*   (* Context {mem: map.map mword byte}. *) *)
(*   (* Context {memTags: map.map tag_t bool}. *) *)

(*   (* Record Compartment := { *) *)
(*   (*     compartment_caps: list cap; *) *)
(*   (* }. *) *)

(*   (* Record Thread := { *) *)
(*   (*     thread_caps: list cap; *) *)
(*   (* }. *) *)

(*   (* Record Thread := { *) *)
(*   (*     stack: Interval.t; *) *)
(*   (*     trusted_stack: Interval.t *) *)
(*   (*   }. *) *)

(*   Record Machine := *)
(*     { pcc : cap; *)
(*       regs: regfile; *)
(*       scrs: scrfile; *)
(*       csrs: csrfile; *)
(*       dmem: mem; *)
(*       (* tags: memTags; *) *)
(*     }. *)

(*   Inductive Status := *)
(*   | ExecThread *)
(*   | CrossCompartmentCall *)
(*   | CrossCompartmentReturn *)
(*   | SwitchThreads *)
(*   | HandleException *)
(*   | Spin. *)

(*   Record CheriotMachine := *)
(*   { m: Machine; *)
(*     status: Status; *)
(*     (* compartments: list Compartment; *) *)
(*     (* curThread : (nat * nat) (* compartment_id * thread_id *) *) *)
(*   }. *)

(*   Definition InitialInvariant : CheriotMachine -> Prop. *)
(*   Admitted. *)

(*   Definition Step_ExecThread (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop. *)
(*   Admitted. *)

(*   Definition Step_CompartmentCall (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop. *)
(*   Admitted. *)

(*   Definition Step_CompartmentReturn (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop. *)
(*   Admitted. *)

(*   Definition Step_SwitchThreads (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop. *)
(*   Admitted. *)

(*   Definition Step_HandleException (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop. *)
(*   Admitted. *)

(*   Definition Step_Spin (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop. *)
(*   Admitted. *)

(*   (* TODO: interrupt *) *)
(*   Definition Step (m: CheriotMachine) (post: CheriotMachine -> Prop) : Prop := *)
(*     match m.(status) with *)
(*     | ExecThread => Step_ExecThread m post *)
(*     | CrossCompartmentCall => Step_CompartmentCall m post *)
(*     | CrossCompartmentReturn => Step_CompartmentReturn m post *)
(*     | SwitchThreads => Step_SwitchThreads m post *)
(*     | HandleException => Step_HandleException m post *)
(*     | Spin => Step_Spin m post *)
(*     end. *)

(* End Semantics. *)
