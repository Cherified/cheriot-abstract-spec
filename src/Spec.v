From Stdlib Require Import List.

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
| UnsealedJump
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
      Definition BasicStPerm := ReachableCap stAddrCap /\ In Perm.Store stAddrCap.(capPerms).
      Definition modifyMemValue := (exists a, In a stAddrCap.(capAddrs) /\ snd (Memory a) <> snd (NewMemory a)) ->
                                   BasicStPerm.
      Definition removeMemCap := (exists a, In a stAddrCap.(capAddrs) /\ fst (Memory a) <> None /\ fst (NewMemory a) = None) ->
                                 BasicStPerm.
      Variable stDataCap: Cap.
      Definition modifyMemCap := (exists a, In a stAddrCap.(capAddrs) /\
                                              fst (NewMemory a) = Some stDataCap /\ fst (Memory a) <> Some stDataCap) ->
                                 BasicStPerm /\ ReachableCap stDataCap /\
                                   exists l, In l stAddrCap.(capCanStore) /\ In l stDataCap.(capCanBeStored).
    End UpdMem.
  End Transitivity.

  (* Record ExportTableEntry := { *)
  (*     exportEntryPCC: Value; (* In CHERIoT, offset from compartment PCC *) *)
  (*     exportEntryStackSize: Value; *)
  (*     exportEntryNumArgs : nat; *)
  (*     exportEntryInterruptStatus: bool; *)
  (* }. *)

  Definition CapWithValue : Type := Cap * Value.

  Definition CallArgs : Type. Admitted.
  Definition ReturnArgs : Type. Admitted.

  Record Compartment := {
      compartmentPCC : CapWithValue;
      compartmentCGP : CapWithValue;
      compartmentErrorHandlers : list Value; (* offset from PCC *)
      compartmentImportTable : list CapWithValue; (* In CHERIoT: sealed caps to export table entries, sentry caps to library functions, and caps to MMIO regions *)
      (* compartmentExportTable : list (Addr * ExportTableEntry) *)
      compartmentGhostCallArgs : list CallArgs; (* TODO *)
      compartmentGhostReturnArgs : list ReturnArgs
  }.

  Record RegisterFile := {
      rfRa : CapWithValue;
      rfCGP : CapWithValue;
      rfCSP: CapWithValue;
      rfCallerSavedRegs : list CapOrValue;
      rfCalleeSavedRegs : list CapOrValue;
      rfArgRegs : list CapOrValue;
      rfMiscRegisters : list CapOrValue;
  }.

  Inductive ThreadEvent :=
  | ThreadEvent_XCompartmentCall (rf: RegisterFile)
  | ThreadEvent_XCompartmentReturn (rf: RegisterFile).

  Definition StackFrame : Type.
  Admitted.

  Record Thread := {
      threadPCC: CapWithValue; (* Offset relative to compartment PCC *)
      threadRF: RegisterFile;
      threadGhostCompartmentIdx: nat; (* Ghost state *)
      threadStackFrame : list StackFrame
  }.

  Section MachineState.
    Variable Exn : Type.

    Import ListNotations.

    Record MachineState := {
        machineCompartments : list Compartment;
        machineThreads: list Thread;
        machineCurThreadIdx : nat;
        machineMemory : Memory_t;
        machineInterruptible : bool
    }.

    Definition setMachineThread (m: MachineState) (tid: nat): MachineState :=
      {| machineCompartments := m.(machineCompartments);
         machineThreads := m.(machineThreads);
         machineCurThreadIdx := tid;
         machineMemory := m.(machineMemory);
         machineInterruptible := m.(machineInterruptible)
      |}.

    Inductive TraceEvent :=
    | Event_SwitchThreads (newIdx: nat)
    | Event_Exception (pc: CapWithValue) (rf: RegisterFile) (exn: Exn)
    | Event_XCompartmentCallViaSwitcher (rf: RegisterFile)
    | Event_XCompartmentReturnViaSwitcher (rf: RegisterFile)
    | Event_XCompartmentCallWithoutSwitcher (rf: RegisterFile)
    | Event_XCompartmentReturnWithoutSwitcher (rf: RegisterFile).

    Definition SameThreadStep (m: MachineState)
                              (update_fn: Thread -> Memory_t -> (Thread -> Memory_t -> bool -> list TraceEvent -> Prop) -> Prop)
                              (post: MachineState -> Prop) : Prop :=
      let tid := m.(machineCurThreadIdx) in
      let threads := m.(machineThreads) in
      exists thread, nth_error threads tid = Some thread /\
                update_fn thread m.(machineMemory) (fun thread' memory' interrupt' event' =>
                   post {| machineCompartments := m.(machineCompartments); (* TODO: update ghost state *)
                           machineThreads := listUpdate threads tid thread';
                           machineCurThreadIdx := tid;
                           machineMemory := memory';
                           machineInterruptible := interrupt'
                        |}).

    Definition SameDomainStep : MachineState -> (MachineState -> list TraceEvent -> Prop) -> Prop.
    Admitted.

    Definition StepThrowException (t: Thread) (m: Memory_t) (post: Thread -> Memory_t -> bool -> list TraceEvent -> Prop) : Prop.
    Admitted.

    Definition StepXCompartmentCallViaSwitcher (t: Thread) (m: Memory_t) (post: Thread -> Memory_t -> bool -> list TraceEvent -> Prop) : Prop.
    Admitted.
    Definition StepXCompartmentReturnViaSwitcher (t: Thread) (m: Memory_t) (post: Thread -> Memory_t -> bool -> list TraceEvent -> Prop) : Prop.
    Admitted.
    Definition StepXCompartmentCallWithoutSwitcher (t: Thread) (m: Memory_t) (post: Thread -> Memory_t -> bool -> list TraceEvent -> Prop) : Prop.
    Admitted.
    Definition StepXCompartmentReturnWithoutSwitcher (t: Thread) (m: Memory_t) (post: Thread -> Memory_t -> bool -> list TraceEvent -> Prop) : Prop.
    Admitted.

    Definition CanSwitchThread (m: MachineState) (newTid: nat) : Prop :=
      m.(machineInterruptible) = true /\
        newTid < List.length m.(machineThreads).

    Inductive DifferentDomainStep : MachineState -> (MachineState -> list TraceEvent -> Prop) -> Prop :=
    | Step_SwitchThreads :
      forall m post tid',
      CanSwitchThread m tid' ->
      post (setMachineThread m tid') [Event_SwitchThreads tid'] ->
      DifferentDomainStep m post
    | Step_ThrowException :
      forall m thread post exn mid,
        SameThreadStep m StepThrowException mid ->
       (forall m', mid m' ->
              post m' [Event_Exception thread.(threadPCC) thread.(threadRF) exn]) ->
       DifferentDomainStep m post
    | Step_XCompartmentCallViaSwitcher:
      forall m thread post mid,
        SameThreadStep m StepXCompartmentCallViaSwitcher mid ->
       (forall m', mid m' ->
              post m' [Event_XCompartmentCallViaSwitcher thread.(threadRF) ]) ->
       DifferentDomainStep m post
    | Step_XCompartmentReturnViaSwitcher:
      forall m thread post mid,
        SameThreadStep m StepXCompartmentReturnViaSwitcher mid ->
       (forall m', mid m' ->
              post m' [Event_XCompartmentReturnViaSwitcher thread.(threadRF) ]) ->
       DifferentDomainStep m post
    | Step_XCompartmentCallWithoutSwitcher:
      forall m thread post mid,
        SameThreadStep m StepXCompartmentCallWithoutSwitcher mid ->
       (forall m', mid m' ->
              post m' [Event_XCompartmentCallWithoutSwitcher thread.(threadRF) ]) ->
       DifferentDomainStep m post
    | Step_XCompartmentReturnWithoutSwitcher:
      forall m thread post mid,
        SameThreadStep m StepXCompartmentReturnWithoutSwitcher mid ->
       (forall m', mid m' ->
              post m' [Event_XCompartmentReturnWithoutSwitcher thread.(threadRF) ]) ->
       DifferentDomainStep m post.

    Inductive Step : MachineState -> (MachineState -> list TraceEvent -> Prop) -> Prop :=
    | Step_SameDomain :
      forall m1 post,
      SameDomainStep m1 post ->
      Step m1 post
    | Step_DifferentDomain:
      forall m1 post,
      DifferentDomainStep m1 post ->
      Step m1 post.

  End MachineState.
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

Require Import coqutil.Map.Interface.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Properties.
From Stdlib Require Import Zmod Bits.
From cheriot Require Import ZmodWord.

Set Primitive Projections.
Local Open Scope Z_scope.

Definition XLEN := 32.
Definition mword := bits XLEN.
Notation addr_t := (bits XLEN).

Module Permissions.
  Record permissions :=
    {
      EX : bool; (* PERMIT_EXECTE *)
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
End Permissions.

Module Otype.
  Class otype := {
      t : Type;
      eqb: t -> t -> bool;
  }.
End Otype.

Module SealType.
  Section WithOType.
    Context {ot: Otype.otype}.

    Inductive t :=
    | Cap_Unsealed
    | Cap_Sentry (seal: Otype.t)
    | Cap_Sealed (seal: Otype.t).

  End WithOType.
End SealType.

Module Ecap.
  (* Reserved bit? *)
  Record ecap {otype: Otype.otype} :=
    { perms: Permissions.permissions;
      seal_type: SealType.t;
      base_addr: addr_t;
      top_addr: addr_t
    }.
End Ecap.

Module capability.
  Section WithContext.
    Context {otype: Otype.otype} .
    Record capability :=
      { valid: bool;
        ecap: Ecap.ecap;
        value: addr_t;
      }.
  End WithContext.
End capability.

Section Semantics.
  Context {gpr scr csr: Type}.
  Context {otype: Otype.otype}.
  Notation cap := (@capability.capability otype).
  (* Context {cap_methods: @capability.cap_methods ecap}. *)
  Context {regfile : map.map gpr cap}.
  Context {scrfile : map.map scr cap}.
  Context {csrfile: map.map csr mword}. (* Simplified for now; actually variable length *)
  Context {mem: map.map mword cap}.

  (* Context {memTags: map.map tag_t bool}. *)
  (* Context {mem: map.map mword byte}. *)
  (* Context {memTags: map.map tag_t bool}. *)

  (* Record Compartment := { *)
  (*     compartment_caps: list cap; *)
  (* }. *)

  (* Record Thread := { *)
  (*     thread_caps: list cap; *)
  (* }. *)

  (* Record Thread := { *)
  (*     stack: Interval.t; *)
  (*     trusted_stack: Interval.t *)
  (*   }. *)

  Record Machine :=
    { pcc : cap;
      regs: regfile;
      scrs: scrfile;
      csrs: csrfile;
      dmem: mem;
      (* tags: memTags; *)
    }.

  Inductive Status :=
  | ExecThread
  | CrossCompartmentCall
  | CrossCompartmentReturn
  | SwitchThreads
  | HandleException
  | Spin.

  Record CheriotMachine :=
  { m: Machine;
    status: Status;
    (* compartments: list Compartment; *)
    (* curThread : (nat * nat) (* compartment_id * thread_id *) *)
  }.

  Definition InitialInvariant : CheriotMachine -> Prop.
  Admitted.

  Definition Step_ExecThread (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop.
  Admitted.

  Definition Step_CompartmentCall (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop.
  Admitted.

  Definition Step_CompartmentReturn (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop.
  Admitted.

  Definition Step_SwitchThreads (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop.
  Admitted.

  Definition Step_HandleException (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop.
  Admitted.

  Definition Step_Spin (m: CheriotMachine) (post: CheriotMachine -> Prop): Prop.
  Admitted.

  (* TODO: interrupt *)
  Definition Step (m: CheriotMachine) (post: CheriotMachine -> Prop) : Prop :=
    match m.(status) with
    | ExecThread => Step_ExecThread m post
    | CrossCompartmentCall => Step_CompartmentCall m post
    | CrossCompartmentReturn => Step_CompartmentReturn m post
    | SwitchThreads => Step_SwitchThreads m post
    | HandleException => Step_HandleException m post
    | Spin => Step_Spin m post
    end.

End Semantics.
