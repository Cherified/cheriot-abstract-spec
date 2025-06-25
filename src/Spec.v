From Stdlib Require Import List Lia Bool Nat.
Set Primitive Projections.

Section EqSet.
  Context [A: Type].
  Variable l1 l2: list A.
  Definition EqSet := forall x, In x l1 <-> In x l2.

  Theorem Eq_imp_EqSet: l1 = l2 -> EqSet.
  Proof.
    unfold EqSet; intros; subst; tauto.
  Qed.

  Definition Subset := forall x, In x l1 -> In x l2.

End EqSet.

Fixpoint listSumToInl [A B: Type] (l: list (A+B)) : list A :=
  match l with
  | nil => nil
  | x :: xs => match x with
               | inl y => y :: listSumToInl xs
               | _ => listSumToInl xs
               end
  end.

Theorem seqInBounds n: forall b v,
    b <= v < b + n -> In v (seq b n).
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (PeanoNat.Nat.eq_dec b v); [auto|right].
    apply IHn.
    lia.
Qed.

Definition is_some [A] (a: option A) : bool :=
  match a with
  | Some _ => true
  | _ => false
  end.

Class ISA_params := {
    ISA_LG_CAPSIZE_BYTES : nat;
    ISA_CAPSIZE_BYTES := Nat.pow 2 ISA_LG_CAPSIZE_BYTES;
    ISA_NREGS: nat
  }.

(* Represents basic permissions *)
Module Perm.
  Inductive t :=
  | Exec
  | System
  | Load
  | Store
  | Cap
  | Sealing
  | Unsealing.
  Scheme Equality for t.
End Perm.

Section Machine.
  Context [ISA: ISA_params].
  Variable Byte: Type.
  Variable Key: Type.
  Definition Addr := nat.
  Definition CapAddr := nat.
  Definition toCapAddr (a: Addr): CapAddr := Nat.shiftr a ISA_LG_CAPSIZE_BYTES.
  Definition fromCapAddr (a: CapAddr): Addr := Nat.shiftl a ISA_LG_CAPSIZE_BYTES.

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

  Definition SealT := (Sentry + Key)%type. (* A sealed cap is either a sentry or a data cap sealed with a key *)

  Record Cap := {
      capSealed: option SealT;
      capPerms: list Perm.t;
      capCanStore: list Label; (* The labels of caps that this cap can store (SL in CHERIoT) *)
      capCanBeStored: list Label; (* The labels of caps where this cap can be stored in (GL and not GL in CHERIoT) *)
      capSealingKeys: list Key; (* List of sealing keys owned by this cap *)
      capUnsealingKeys: list Key; (* List of unsealing keys owned by this cap *)
      capAddrs: list Addr; (* List of addresses representing this cap's bounds *)
      capKeepPerms: list Perm.t; (* Permissions to be the only ones kept when loading using this cap *)
      capKeepCanStore: list Label; (* Labels-of-caps-that-this-cap-can-store to be the only ones kept
                                      when loading using this cap *)
      capKeepCanBeStored: list Label; (* Labels-of-caps-where-this-cap-can-be-stored to be the only ones kept
                                         when loading using this cap *)
      capCursor: Addr (* The current address of a cap.
                         These cursors can be out of bounds w.r.t. capAddrs.
                         In CHERI these out of bounds cursors are allowed as part of representable region.
                         In the formal model, any address is representable.
                         Notice that when sealing a capability, the cursor is not checked to be inbounds.
                         This mean one has to explicitly check if the sentry capabilities are in-bounds.
                         This creates a problem for return sentries, as they need not be in-bounds;
                         the error has to be handled by the caller compartment on return. *)
    }.

  Definition Memory_t := Addr -> Byte.
  Definition Tag_t := CapAddr -> bool.
  Definition FullMemory := (Memory_t * Tag_t)%type.
  Definition Bytes := list Byte.
  Definition CapOrBytes := (Cap + Bytes)%type.

  Variable bytesToCapUnsafe: Bytes -> Cap.
  Variable capToBytes: Cap -> Bytes.

  Definition bytesToCap (tag: bool) (bytes: Bytes): CapOrBytes :=
    if tag && (length bytes =? ISA_CAPSIZE_BYTES)
    then inl (bytesToCapUnsafe bytes)
    else inr bytes.

  Definition readMemBytes (mem: Memory_t) (a: Addr) (sz: nat) : Bytes :=
    map mem (seq (fromCapAddr a) sz).

  Definition readMemTagCap (mem: Memory_t) (tags: Tag_t) (a: CapAddr) : CapOrBytes :=
    bytesToCap (tags a) (readMemBytes mem (fromCapAddr a) ISA_CAPSIZE_BYTES).

  Definition writeMemByte (mem: Memory_t) (a: Addr) (byte: Byte) : Memory_t :=
    fun i => if i =? a
             then byte
             else mem i.

  Definition writeMemBytes (mem: Memory_t) (a: Addr) (bytes: Bytes): Memory_t :=
    fst (fold_left (fun '(mem', i) byte => (writeMemByte mem' (a + i) byte, S i)) bytes (mem, 0)).

  Definition writeTagTag (tags: Tag_t) (a: CapAddr) (t: bool) : Tag_t := (fun i => if i =? a
                                                                                   then t
                                                                                   else tags i).

  Definition writeMemTagCap (mem: Memory_t) (tags: Tag_t) (a: CapAddr) (c: Cap) : FullMemory :=
    let capa := fromCapAddr a in
    (writeMemBytes mem capa (capToBytes c), writeTagTag tags capa true).

  Definition readByte (mem: FullMemory) (a: Addr) : Byte := (fst mem) a.
  Definition readBytes (mem: FullMemory) := readMemBytes (fst mem).
  Definition readTag (mem: FullMemory) (a: CapAddr) : bool := (snd mem) a.
  Definition readCap (mem: FullMemory) := readMemTagCap (fst mem) (snd mem).
  Definition writeByte (mem: FullMemory) := writeMemByte (fst mem).
  Definition writeBytes (mem: FullMemory) := writeMemBytes (fst mem).
  Definition writeTag (mem: FullMemory) := writeTagTag (snd mem).
  Definition writeCap (mem: FullMemory) := writeMemTagCap (fst mem) (snd mem).

  Definition ExnInfo := Bytes.

  Section CurrMemory.
    Variable mem: FullMemory.

    Section CapStep.
      Variable y z: Cap.

      Definition SealEq := z.(capSealed) = y.(capSealed).

      (* NB: capCursor can change arbitrarily for unsealed caps. *)
      Record RestrictUnsealed : Prop := {
          restrictUnsealedEqs: SealEq;
          restrictUnsealedPermsSubset: Subset z.(capPerms) y.(capPerms);
          restrictUnsealedCanStoreSubset: Subset z.(capCanStore) y.(capCanStore);
          restrictUnsealedCanBeStoredSubset: Subset z.(capCanBeStored) y.(capCanBeStored);
          restrictUnsealedSealingKeysSubset: Subset z.(capSealingKeys) y.(capSealingKeys);
          restrictUnsealedUnsealingKeysSubset: Subset z.(capUnsealingKeys) y.(capUnsealingKeys);
          restrictUnsealedAddrsSubset: Subset z.(capAddrs) y.(capAddrs);
          restrictUnsealedKeepPermsSubset: Subset z.(capKeepPerms) y.(capKeepPerms);
          restrictUnsealedKeepCanStoreSubset: Subset z.(capKeepCanStore) y.(capKeepCanStore);
          restrictUnsealedKeepCanBeStoredSubset: Subset z.(capKeepCanBeStored) y.(capKeepCanBeStored) }.

      Record RestrictSealed : Prop := {
          restrictSealedEqs: SealEq;
          restrictSealedPermsEq: EqSet z.(capPerms) y.(capPerms);
          restrictSealedCanStore: EqSet z.(capCanStore) y.(capCanStore);
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
          restrictSealedCanBeStoredSubset: Subset z.(capCanBeStored) y.(capCanBeStored);
          restrictSealedSealingKeysEq: EqSet z.(capSealingKeys) y.(capSealingKeys);
          restrictSealedUnsealingKeysSubset: EqSet z.(capUnsealingKeys) y.(capUnsealingKeys);
          restrictSealedAddrsEq: EqSet z.(capAddrs) y.(capAddrs);
          restrictSealedKeepPermsSubset: EqSet z.(capKeepPerms) y.(capKeepPerms);
          restrictSealedKeepCanStoreSubset: EqSet z.(capKeepCanStore) y.(capKeepCanStore);
          restrictSealedKeepCanBeStoredSubset: EqSet z.(capKeepCanBeStored) y.(capKeepCanBeStored);
          restrictSealedCursorEq: z.(capCursor) = y.(capCursor) }.

      Definition Restrict : Prop :=
        match y.(capSealed) with
        | None => RestrictUnsealed
        | _ => RestrictSealed
        end.

      Variable x: Cap.
      (* When a cap y is loaded using a cap x, then the attentuation of x comes into play to create z *)

      Record NonRestrictEqs : Prop := {
          nonRestrictAuthUnsealed: x.(capSealed) = None;
          nonRestrictSealingKeysEq: EqSet z.(capSealingKeys) y.(capSealingKeys);
          nonRestrictUnsealingKeysEq: EqSet z.(capUnsealingKeys) y.(capUnsealingKeys);
          nonRestrictAddrsEq: EqSet z.(capAddrs) y.(capAddrs);
          nonRestrictCursorEq: z.(capCursor) = y.(capCursor) }.

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
          loadFromAuth: exists capa, Subset (seq (fromCapAddr capa) ISA_CAPSIZE_BYTES) x.(capAddrs) /\ readCap mem capa = inl y;
          loadSealEq: z.(capSealed) = y.(capSealed);
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
                               | Some _ => EqSet z.(capKeepCanBeStored) y.(capKeepCanBeStored)
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
          sealNewSealed: exists k, In k x.(capSealingKeys) /\ z.(capSealed) = Some (inr k) }.

      Record Unseal : Prop := {
          unsealEqs: SealUnsealEqs;
          unsealOrigSealed: exists k, In k x.(capUnsealingKeys) /\ y.(capSealed) = Some (inr k) ;
          unsealNewUnsealed: z.(capSealed) = None }.
    End CapStep.

    Section Transitivity.
      Variable origSet: list Cap.

      Inductive ReachableCap: Cap -> Prop :=
      | Refl (c: Cap) (inPf: In c origSet) : ReachableCap c
      | StepRestrict y (yPf: ReachableCap y) z (yz: Restrict y z) : ReachableCap z
      | StepLoadCap x (xPf: ReachableCap x) y z (xyz: LoadCap x y z): ReachableCap z
      | StepSeal x (xPf: ReachableCap x) y (yPf: ReachableCap y) z (xyz: Seal x y z): ReachableCap z
      | StepUnseal x (xPf: ReachableCap x) y (yPf: ReachableCap y) z (xyz: Unseal x y z): ReachableCap z.

      (* Transitively reachable addr listed with permissions, canStore and canBeStored *)
      Inductive ReachableAddr: Addr -> nat -> list Perm.t -> list Label -> list Label -> Prop :=
      | HasAddr c (cPf: ReachableCap c) a sz (ina: Subset (seq a sz) c.(capAddrs)) (notSealed: c.(capSealed) = None)
        : ReachableAddr a sz c.(capPerms) c.(capCanStore) c.(capCanBeStored).

      Definition ReachableCaps newCaps := forall c, In c newCaps -> ReachableCap c.

      Section UpdMem.
        Variable mem': FullMemory.

        Definition BasicStPermForAddr (auth: Cap) (a: Addr) (sz: nat) :=
          ReachableCap auth
          /\ In Perm.Store auth.(capPerms)
          /\ auth.(capSealed) = None
          /\ Subset (seq a sz) auth.(capAddrs).

        Definition ValidMemCapUpdate :=
          forall capa, readCap mem capa <> readCap mem' capa ->
                          readTag mem' capa = true ->
                          exists stAddrCap, BasicStPermForAddr stAddrCap (fromCapAddr capa) ISA_CAPSIZE_BYTES
                                            /\ exists stDataCap, ReachableCap stDataCap
                                                                 /\ (exists l, In l stAddrCap.(capCanStore) /\ In l stDataCap.(capCanBeStored)).

        Definition ValidMemTagRemoval :=
          forall capa, readTag mem capa = true ->
                          readTag mem' capa = false ->
                          exists stAddrCap, BasicStPermForAddr stAddrCap (fromCapAddr capa) 1.

        Definition ValidMemDataUpdate :=
          forall a, readByte mem a <> readByte mem' a ->
                          exists stAddrCap, BasicStPermForAddr stAddrCap a 1.

        Definition ValidMemUpdate := ValidMemCapUpdate /\ ValidMemTagRemoval /\ ValidMemDataUpdate.
      End UpdMem.
    End Transitivity.
  End CurrMemory.

  Section Machine.
    Import ListNotations.
    Notation PCC := Cap (only parsing).
    Notation MEPCC := Cap (only parsing). (* While MEPCC can become invalid architecturally,
                                             it shouldn't if the switcher is correct *)
    Definition EXNInfo := Bytes.
    Notation RegIdx := nat (only parsing).

    Definition RegisterFile := list CapOrBytes.
    Definition capsOfRf (rf: RegisterFile) := listSumToInl rf.

    (* TODO: decide on a register file representation. RF manipulations are currently buggy. *)
    Variable rfIdx_ra : nat.

    (* Given that the spec can switch threads at any time,
       interrupts are disabled only to achieve atomicity of a code sequence in single-core machines. *)
    Inductive InterruptStatus :=
    | InterruptsEnabled
    | InterruptsDisabled.

    Record TrustedStackFrame := {
        trustedStackFrame_CSP : Cap;
        trustedStackFrame_calleeExportTable : Cap;
        trustedStackFrame_errorCounter : nat
        (* trustedStackFrame_compartmentIdx : nat; (* Actually a pointer to the compartment's export table *) *)
      }.

    (* TS denotes TrustedStack everywhere below *)
    Definition capsOfTSFrame tsf := [tsf.(trustedStackFrame_CSP); tsf.(trustedStackFrame_calleeExportTable)].

    (* Note that TrustedStack is a first class entity in our abstraction, and not yet another object in the Memory *)
    (* That is, it is accessed like how a PCC is accessed using a name *)
    (* In CHERIoT, Trusted stack is just another object in Memory accessible through a thread's MTDC *)
    (* This refinement will be done later *)
    Record TrustedStack := {
        (* trustedStack_shadowRegisters : RegisterFile; *)
        trustedStack_frames : list TrustedStackFrame;
    }.
    Definition capsOfTS ts := concat (map capsOfTSFrame ts.(trustedStack_frames)).

    Record UserThreadState :=
      { thread_rf : RegisterFile;
        thread_pcc: PCC
      }.
    Definition capsOfUserTS uts := uts.(thread_pcc) :: capsOfRf uts.(thread_rf).

    (* SystemThreadState is a first class entity like TrustedStack.
       In CHERIoT, only MEPCC is a first class entity; the rest are objects in memory *)
    Record SystemThreadState :=
      { thread_mepcc: MEPCC;
        thread_exceptionInfo: EXNInfo;
        thread_trustedStack: TrustedStack
      }.
    Definition capsOfSystemTS sts := sts.(thread_mepcc) :: capsOfTS sts.(thread_trustedStack).

    Inductive SystemCall :=
    | SystemCall_Exception
    | SystemCall_ExceptionRet
    | SystemCall_CompartmentCall
    | SystemCall_CompartmentRet.

    Inductive ThreadMode :=
    | UserMode
    | SystemMode (call: SystemCall) (offset: nat).

    Record Thread := {
        thread_userState : UserThreadState;
        thread_systemState : SystemThreadState;
        thread_mode : ThreadMode
      }.
    Definition capsOfThread t := capsOfUserTS t.(thread_userState) ++ capsOfSystemTS t.(thread_systemState).

    Record Machine := {
        machine_memory: FullMemory;
        machine_interruptStatus : InterruptStatus;
        machine_threads : list Thread;
        machine_curThreadId : nat;
    }.

    (* The following definitions are defined per thread (obvious, but re-iterating) *)
    Definition UserContext : Type := (UserThreadState * FullMemory).
    Definition SystemContext : Type := (SystemThreadState * InterruptStatus).

    (* TODO: Check if we can remove checking Load permission *)
    Definition ReachableDataSame m1 m2 caps :=
      forall a sz p cs cbs, ReachableAddr m1 caps a sz p cs cbs -> In Perm.Load p ->
                            (ReachableAddr m2 caps a sz p cs cbs /\ readByte m1 a = readByte m2 a).

    (* TODO: Check if we can remove checking Load/Cap permission *)
    Definition ReachableTagSame m1 m2 caps :=
      forall capa p cs cbs, ReachableAddr m1 caps capa ISA_CAPSIZE_BYTES p cs cbs -> In Perm.Load p -> In Perm.Cap p ->
                               (ReachableAddr m2 caps capa ISA_CAPSIZE_BYTES p cs cbs /\ readTag m1 capa = readTag m2 capa).

    Definition ReachableMemSame m1 m2 caps := ReachableDataSame m1 m2 caps /\ ReachableTagSame m1 m2 caps.

    Definition UpdatedDataSame (m1 m2 m1' m2': FullMemory) :=
      forall a, (readByte m1' a <> readByte m1 a \/ readByte m2' a <> readByte m2 a) -> readByte m1' a = readByte m2' a.

    Definition UpdatedTagSame (m1 m2 m1' m2': FullMemory) :=
      forall capa, (readTag m1' capa <> readTag m1 capa \/ readTag m2' capa <> readTag m2 capa) -> readTag m1' capa = readTag m2' capa.

    Definition UpdatedMemSame (m1 m2 m1' m2': FullMemory) := UpdatedDataSame m1 m2 m1' m2' /\ UpdatedTagSame m1 m2 m1' m2'.

    Inductive Result {e t} :=
    | Ok : t -> Result
    | Exn : e -> Result.
    Arguments Result : clear implicits.

    Section NormalInst.
      Variable normalInst: UserContext -> Result ExnInfo UserContext.

      Definition FuncNormal :=
        forall rf pcc m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          match normalInst (Build_UserThreadState rf pcc, m1),
                normalInst (Build_UserThreadState rf pcc, m1) with
          | Ok (uts1, m1'), Ok (uts2, m2') =>
              uts1 = uts2 /\ UpdatedMemSame m1 m2 m1' m2'
          | Exn e1, Exn e2 => e1 = e2
          | _, _ => False
          end.

      Definition WfNormalInst := forall rf pcc mem,
          match normalInst (Build_UserThreadState rf pcc, mem) with
          | Ok (Build_UserThreadState rf' pcc', mem') =>
            let caps := pcc :: capsOfRf rf in
            let caps' := pcc' :: capsOfRf rf' in
            In Perm.Exec pcc.(capPerms)
            /\ ValidMemUpdate mem caps mem'
            /\ ReachableCaps mem caps caps'
            /\ In Perm.Exec pcc'.(capPerms)
            /\ FuncNormal
          | Exn e => FuncNormal
          end.
    End NormalInst.

    Section SystemInst.
      Variable systemInst: UserContext -> SystemContext -> (UserContext * SystemContext * nat).

      Definition FuncSystem := forall rf pcc mepcc exnInfo ts ints m1 m2,
          ReachableMemSame m1 m2 ((pcc :: capsOfRf rf) ++ (mepcc :: capsOfTS ts)) ->
          let '((uts1, m1'), sc1, offset) := systemInst (Build_UserThreadState rf pcc, m1)
                                       (Build_SystemThreadState mepcc exnInfo ts, ints) in
          let '((uts2, m2'), sc2, offset) := systemInst (Build_UserThreadState rf pcc, m2)
                                       (Build_SystemThreadState mepcc exnInfo ts, ints) in
          uts1 = uts2 /\ sc1 = sc2 /\ UpdatedMemSame m1 m2 m1' m2'.

      Definition WfSystemInst := forall rf pcc mem mepcc exnInfo ts ints,
          let '((Build_UserThreadState rf' pcc', mem'),
                  (Build_SystemThreadState mepcc' exnInfo' ts', ints'),
                  offset) :=
            systemInst (Build_UserThreadState rf pcc, mem) (Build_SystemThreadState mepcc exnInfo ts, ints) in
          let caps := (pcc :: capsOfRf rf) ++ (mepcc :: capsOfTS ts) in
          let caps' := (pcc' :: capsOfRf rf') ++ (mepcc' :: capsOfTS ts') in
          In Perm.Exec pcc.(capPerms)
          /\ In Perm.System pcc.(capPerms)
          /\ ValidMemUpdate mem caps mem'
          /\ ReachableCaps mem caps caps'
          /\ In Perm.Exec pcc'.(capPerms)
          /\ FuncSystem.
    End SystemInst.

    Section CallSentryInst.
      Variable callSentryInst: UserContext -> InterruptStatus -> Result ExnInfo (PCC * option Cap * InterruptStatus).

      Definition FuncCallSentry :=
        forall rf pcc ints m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          match callSentryInst (Build_UserThreadState rf pcc, m1) ints,
                callSentryInst (Build_UserThreadState rf pcc, m2) ints  with
          | Ok (pcc1', l1, ints1'), Ok (pcc2', l2, ints2') =>
              pcc1' = pcc2' /\ l1 = l2 /\ ints1' = ints2'
          | Exn e1, Exn e2 =>
              e1 = e2
          | _, _ => False
          end.

      Definition WfCallSentryInst := forall rf pcc ints mem,
          match callSentryInst (Build_UserThreadState rf pcc, mem) ints with
          | Ok (pcc', optLink, ints') =>
            let caps := pcc :: capsOfRf rf in
            In Perm.Exec pcc.(capPerms)
            /\ ReachableCap mem caps pcc'
            /\ match optLink with
               | Some link => ReachableCap mem caps link
                              /\ link.(capSealed) = Some (inl (if ints
                                                               then RetEnableInterrupt
                                                               else RetDisableInterrupt))
                              /\ In Perm.Exec link.(capPerms)
               | None => True
               end
            /\ match pcc'.(capSealed) with
               | Some (inl CallEnableInterrupt) => ints' = InterruptsEnabled
               | Some (inl CallDisableInterrupt) => ints' = InterruptsDisabled
               | Some (inl CallInheritInterrupt) => ints' = ints
               | _ => False
               end
            /\ In Perm.Exec pcc'.(capPerms)
            /\ FuncCallSentry
          | Exn _ => FuncCallSentry
          end.
    End CallSentryInst.

    Section RetSentryInst.
      Variable retSentryInst: UserContext -> Result ExnInfo (PCC * InterruptStatus).

      Definition FuncRetSentry :=
        forall rf pcc m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          match retSentryInst (Build_UserThreadState rf pcc, m1),
                retSentryInst (Build_UserThreadState rf pcc, m2) with
          | Ok (pcc1', ints1'), Ok (pcc2', ints2') =>
              pcc1' = pcc2' /\ ints1' = ints2'
          | Exn e1, Exn e2 => e1 = e2
          | _, _ => False
          end.

      Definition WfRetSentryInst := forall rf pcc mem,
          match retSentryInst (Build_UserThreadState rf pcc, mem) with
          | Ok (pcc', ints') =>
            let caps := pcc :: capsOfRf rf in
            In Perm.Exec pcc.(capPerms)
            /\ ReachableCap mem caps pcc'
            /\ match pcc'.(capSealed) with
               | Some (inl RetEnableInterrupt) => ints' = InterruptsEnabled
               | Some (inl RetDisableInterrupt) => ints' = InterruptsDisabled
               | _ => False
               end
            /\ In Perm.Exec pcc'.(capPerms)
            /\ FuncRetSentry
          | Exn e => FuncRetSentry
          end.
    End RetSentryInst.

    Section ExnInst.
      Variable exnInst: UserContext -> EXNInfo.

      Definition FuncExn :=
        forall rf pcc m1 m2,
          ReachableMemSame m1 m2 (pcc :: capsOfRf rf) ->
          let exn1 := exnInst (Build_UserThreadState rf pcc, m1) in
          let exn2 := exnInst (Build_UserThreadState rf pcc, m2) in
          exn1 = exn2.

      Definition WfExnInst := forall rf pcc mem,
          let exn := exnInst (Build_UserThreadState rf pcc, mem) in
          let caps := pcc :: capsOfRf rf in
          FuncExn.
    End ExnInst.

    Inductive Inst :=
    | Inst_Normal normalInst (wf: WfNormalInst normalInst)
    (* | Inst_System systemInst (wf: WfSystemInst systemInst) *)
    | Inst_Call callSentryInst (wf: WfCallSentryInst callSentryInst)
    | Inst_Ret retSentryInst (wf: WfRetSentryInst retSentryInst)
    (* | Inst_CompartmentCall *)
    (* | Inst_CompartmentRet *)
    | Inst_Exn exnInst (wf: WfExnInst exnInst).

    Inductive SysInst : Type :=
    | Inst_System systemInst (wf: WfSystemInst systemInst).

    Section FetchDecodeExecute.
      Variable fetchAddrs: FullMemory -> Addr -> list Addr.
      Variable decode : list Byte -> Inst.
      Variable getSystemInst : SystemCall -> nat -> SysInst.
      Variable pccNotInBounds: EXNInfo.

      Variable compartmentCallPCC: Cap. (* This has Exec and System permission; must pass the proof *)
      Variable compartmentRetPCC: Cap.  (* This has Exec and System permission; must pass the proof *)
      Variable exceptionEntryPCC: Cap.  (* This has Exec and System permission; must pass the proof *)
      Variable exceptionRetPCC: Cap.  (* This has Exec and System permission; must pass the proof *)

      Section WithContext.
        Variable uc: UserContext.
        Definition mem : FullMemory := snd uc.
        Definition pcc := (fst uc).(thread_pcc).
        Definition rf := (fst uc).(thread_rf).
        Variable sc: SystemContext.
        Variable mode : ThreadMode.
        Definition ints := snd sc.

        (* Addresses fetched should not depend on arbitrary memory regions. *)
        Definition fetchAddrsOk :=
          exists (fn: Addr -> list Addr),
            forall mem1 mem2 addr,
            (forall a, In a (fn addr) -> readByte mem1 a = readByte mem2 a /\ readTag mem1 a = readTag mem2 a ) ->
            fetchAddrs mem1 addr = fetchAddrs mem2 addr.
        Context {fetchAddrsOk: fetchAddrsOk}.

        Definition exceptionState (exnInfo: EXNInfo): (UserContext * SystemContext) :=
          ((Build_UserThreadState rf exceptionEntryPCC, mem),
            (Build_SystemThreadState pcc exnInfo (fst sc).(thread_trustedStack), ints)
          ).

        Definition threadStepFunction: UserContext * SystemContext :=
          match decode (map (readByte mem) (fetchAddrs mem pcc.(capCursor))) with
          | Inst_Normal normalInst wf =>
              match normalInst uc with
              | Ok uc' => (uc', sc)
              | Exn e => exceptionState e
              end
          (* | Inst_System systemInst wf => systemInst uc sc *)
          | Inst_Call callSentryInst wf =>
              match callSentryInst uc ints with (* TODO: fix optLink *)
              | Ok (pcc', optLink, ints') =>
                ((Build_UserThreadState rf pcc', mem), (fst sc, ints'))
              | Exn e => exceptionState e
              end
          | Inst_Ret retSentryInst wf =>
              match retSentryInst uc with
              | Ok (pcc', ints') =>
                  ((Build_UserThreadState rf pcc', mem), (fst sc, ints'))
              | Exn e => exceptionState e
              end
          (* | Inst_CompartmentCall => *)
          (*     ((Build_UserThreadState rf compartmentCallPCC, mem), sc) *)
          (* | Inst_CompartmentRet => *)
          (*     ((Build_UserThreadState rf compartmentRetPCC, mem), sc) *)
          | Inst_Exn exnInst wf =>
            ((Build_UserThreadState rf exceptionEntryPCC, mem),
              (Build_SystemThreadState pcc (exnInst uc) (fst sc).(thread_trustedStack), ints)
            )
          end.

        Definition SystemPCC_eqb (c1 c2: Cap) : bool. Proof using. Admitted.
        Definition hasSystemPerm (c: Cap) : bool :=
          existsb (Perm.t_beq Perm.System) c.(capPerms).

        Definition magicThreadStepFunction : UserContext * SystemContext * ThreadMode :=
          match mode with
          | UserMode =>
              let '(uc', sc') := threadStepFunction in
              let mode' :=
                if (SystemPCC_eqb (fst uc').(thread_pcc) compartmentCallPCC) then
                  SystemMode SystemCall_CompartmentCall 0
                else if (SystemPCC_eqb (fst uc').(thread_pcc) compartmentRetPCC) then
                  SystemMode SystemCall_CompartmentRet 0
                else if (SystemPCC_eqb (fst uc').(thread_pcc) exceptionEntryPCC) then
                  SystemMode SystemCall_Exception 0
                else if (SystemPCC_eqb (fst uc').(thread_pcc) exceptionRetPCC) then
                  SystemMode SystemCall_ExceptionRet 0
                else
                  UserMode in
              (uc', sc', mode')
          | SystemMode mode offset =>
              match getSystemInst mode offset with
              | Inst_System systemInst wf =>
                  let '(uc', sc', delta) := systemInst uc sc in
                  let mode' :=
                    if hasSystemPerm (fst uc').(thread_pcc) then
                      SystemMode mode (offset + delta)
                    else
                      UserMode in
                  (uc', sc', mode')
              end
          end.

        Definition fetchAddrsInBounds := Subset (fetchAddrs mem pcc.(capCursor)) pcc.(capAddrs)
                                         /\ In pcc.(capCursor) pcc.(capAddrs).

        Inductive ThreadStep : (UserContext * SystemContext * ThreadMode) -> Prop :=
        | GoodUserThreadStep (inBounds: fetchAddrsInBounds) (inUserMode: mode = UserMode)
:
            ThreadStep magicThreadStepFunction
        | BadUserFetch (notInBounds: ~ fetchAddrsInBounds) (inUserMode: mode = UserMode)
          : ThreadStep (exceptionState pccNotInBounds, SystemMode SystemCall_Exception 0)
        | SystemThreadStep (inSystemMode: exists call offset, mode = SystemMode call offset)
          : ThreadStep magicThreadStepFunction
        .
      End WithContext.

      Definition setMachineThread (m: Machine) (tid: nat): Machine :=
        {| machine_memory := m.(machine_memory);
           machine_interruptStatus := m.(machine_interruptStatus);
           machine_threads := m.(machine_threads);
           machine_curThreadId := tid
        |}.

      Inductive SameThreadStep : Machine -> Machine -> Prop :=
      | SameThreadStepOk m1 m2
          (threadIdEq: m2.(machine_curThreadId) = m1.(machine_curThreadId))
          (idleThreadsEq: forall n, n <> m1.(machine_curThreadId) ->
                               nth_error m2.(machine_threads) n = nth_error m1.(machine_threads) n)
          (stepOk: forall userSt' mem' sysSt' interrupt' mode',
                  exists thread, nth_error m1.(machine_threads) m1.(machine_curThreadId) = Some thread /\
                  ThreadStep (thread.(thread_userState), m1.(machine_memory))
                             (thread.(thread_systemState), m1.(machine_interruptStatus))
                             thread.(thread_mode)
                             ((userSt', mem'), (sysSt', interrupt'), mode') ->
                  m2.(machine_memory) = mem' /\
                  m2.(machine_interruptStatus) = interrupt' /\
                  nth_error m2.(machine_threads) m2.(machine_curThreadId)
                    = Some (Build_Thread userSt' sysSt' mode')) :
          SameThreadStep m1 m2.

      Inductive MachineStep : Machine -> Machine -> Prop :=
      | Step_SwitchThreads:
        forall m tid',
        m.(machine_interruptStatus) = InterruptsEnabled ->
        tid' < List.length m.(machine_threads) ->
        MachineStep m (setMachineThread m tid')
      | Step_SameThread:
        forall m1 m2,
        SameThreadStep m1 m2 ->
        MachineStep m1 m2.

    End FetchDecodeExecute.

  End Machine.
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
    length: N;
    addr: N;
    addrInBounds: base <= addr < base + length
    (* This is needed because of compressed caps. See comment in definition of Cap above *)
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

  Definition mk_abstract_cap (c: cheriot_cap) : Cap N :=
    let d := decompress_perm c.(permissions) in
    {|capSealed := if d.(EX)
                   then match c.(otype) with
                        | 0 => None
                        | 1 => Some (inl CallInheritInterrupt)
                        | 2 => Some (inl CallDisableInterrupt)
                        | 3 => Some (inl CallEnableInterrupt)
                        | 4 => Some (inl RetDisableInterrupt)
                        | 5 => Some (inl RetEnableInterrupt)
                        | (* 6 & 7 *) _ => None (* TODO: capSentry ⊆ capSealed *)
                        end
                   else match c.(otype) with
                        | 0 => None
                        | _ => Some (inr c.(otype))
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
      capCanStore := if d.(SL) then [Local;NonLocal] else [NonLocal];
      capCanBeStored := if d.(GL) then [Local;NonLocal] else [Local];
      capSealingKeys := [c.(addr)];
      capUnsealingKeys := [c.(addr)];
      capAddrs := seq (N.to_nat c.(base)) (N.to_nat c.(length));
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
      capKeepCanBeStored := if d.(LG) then [Local;NonLocal] else [Local];
      capCursor := N.to_nat c.(addr) |}.
End CHERIoTValidation.
