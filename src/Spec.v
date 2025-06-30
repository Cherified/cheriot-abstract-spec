From Stdlib Require Import List Lia Bool Nat NArith.
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
  Context {Byte Key: Type}.
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
    map mem (seq a sz).

  Definition readMemTagCap (mem: Memory_t) (tags: Tag_t) (capa: CapAddr) : CapOrBytes :=
    bytesToCap (tags capa) (readMemBytes mem (fromCapAddr capa) ISA_CAPSIZE_BYTES).

  Definition writeMemByte (mem: Memory_t) (a: Addr) (byte: Byte) : Memory_t :=
    fun i => if i =? a
             then byte
             else mem i.

  Definition writeMemBytes (mem: Memory_t) (a: Addr) (bytes: Bytes): Memory_t :=
    fst (fold_left (fun '(mem', a') byte => (writeMemByte mem' a' byte, S a')) bytes (mem, a)).

  Definition writeTagTag (tags: Tag_t) (capa: CapAddr) (t: bool) : Tag_t := (fun i => if i =? capa
                                                                                      then t
                                                                                      else tags i).

  Definition writeMemTagCap (mem: Memory_t) (tags: Tag_t) (capa: CapAddr) (c: Cap) : FullMemory :=
    let a := fromCapAddr capa in
    (writeMemBytes mem a (capToBytes c), writeTagTag tags capa true).

  Definition readByte (mem: FullMemory) := fst mem.
  Definition readBytes (mem: FullMemory) := readMemBytes (fst mem).
  Definition readTag (mem: FullMemory) := snd mem.
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

    Section CapHelpers.
      Definition setCapSealed (c: Cap) (seal: option SealT) : Cap :=
        {| capSealed := seal;
           capPerms := c.(capPerms);
           capCanStore := c.(capCanStore);
           capCanBeStored := c.(capCanBeStored);
           capSealingKeys := c.(capSealingKeys);
           capUnsealingKeys := c.(capUnsealingKeys);
           capAddrs := c.(capAddrs);
           capKeepPerms := c.(capKeepPerms);
           capKeepCanStore := c.(capKeepCanStore);
           capKeepCanBeStored := c.(capKeepCanBeStored);
           capCursor := c.(capCursor)
        |}.
      Definition isSentry (c: Cap) :=
        match c.(capSealed) with
        | Some (inl _) => true
        | _ => false
        end.

      Definition isSealedDataCap (c: Cap) :=
        match c.(capSealed) with
        | Some (inr _) => true
        | _ => false
        end.

    End CapHelpers.

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

        Definition StPermForAddr (auth: Cap) (a: Addr) (sz: nat) :=
          ReachableCap auth
          /\ In Perm.Store auth.(capPerms)
          /\ auth.(capSealed) = None
          /\ Subset (seq a sz) auth.(capAddrs).

        Definition StPermForCap (auth: Cap) (capa: CapAddr) :=
          StPermForAddr auth (fromCapAddr capa) ISA_CAPSIZE_BYTES.

        Definition ValidMemCapUpdate :=
          forall capa, readCap mem capa <> readCap mem' capa ->
                          readTag mem' capa = true ->
                          exists stAddrCap, StPermForCap stAddrCap capa
                                            /\ exists stDataCap, ReachableCap stDataCap
                                                                 /\ (exists l, In l stAddrCap.(capCanStore) /\
                                                                                 In l stDataCap.(capCanBeStored)).

        Definition ValidMemTagRemoval :=
          forall capa, readTag mem capa = true ->
                          readTag mem' capa = false ->
                          exists stAddrCap, StPermForCap stAddrCap capa.

        Definition ValidMemDataUpdate :=
          forall a, readByte mem a <> readByte mem' a ->
                          exists stAddrCap, StPermForAddr stAddrCap a 1.

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

    Record Thread := {
        thread_userState : UserThreadState;
        thread_systemState : SystemThreadState;
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

    Section ReachableMemSame.
      Variable m1 m2: FullMemory.
      Variable caps: list Cap.
      (* TODO: Check if we can remove checking Load permission *)
      Definition ReachableDataSame :=
        forall a sz p cs cbs, ReachableAddr m1 caps a sz p cs cbs -> In Perm.Load p ->
                              (ReachableAddr m2 caps a sz p cs cbs /\ readByte m1 a = readByte m2 a).

      (* TODO: Check if we can remove checking Load/Cap permission *)
      Definition ReachableTagSame :=
        forall capa p cs cbs, ReachableAddr m1 caps capa ISA_CAPSIZE_BYTES p cs cbs ->
                              In Perm.Load p -> In Perm.Cap p ->
                              (ReachableAddr m2 caps capa ISA_CAPSIZE_BYTES p cs cbs /\
                                 readTag m1 capa = readTag m2 capa).

      Definition ReachableMemSame := ReachableDataSame /\ ReachableTagSame.

      Section UpdatedMemSame.
        Variable m1' m2': FullMemory.
        (* TODO: Are the UpdatedMemSame conditions all wrong?
           Should they be detected a-priori instead of checking equality of updates *)
        Definition UpdatedDataSame :=
          forall a, (readByte m1' a <> readByte m1 a \/ readByte m2' a <> readByte m2 a) ->
                    readByte m1' a = readByte m2' a.

        Definition UpdatedTagSame :=
          forall capa, (readTag m1' capa <> readTag m1 capa \/ readTag m2' capa <> readTag m2 capa) ->
                       readTag m1' capa = readTag m2' capa.

        Definition UpdatedMemSame := UpdatedDataSame /\ UpdatedTagSame.
      End UpdatedMemSame.
    End ReachableMemSame.

    (* TODO: Should e be a parameter in Result? *)
    Inductive Result {e t} :=
    | Ok : t -> Result
    | Exn : e -> Result.
    Arguments Result : clear implicits.

    Section ValidState.
      Definition ValidRf (rf: RegisterFile) : Prop :=
        length rf = ISA_NREGS.
    End ValidState.

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

      (* TODO: We might need some provable predicates on all ExnInfo as well
         (for instance, if NO_EXEC_PERMISSION, then MEPCC tag would still be valid) *)
      Definition WfNormalInst := forall rf pcc mem,
          ValidRf rf ->
          FuncNormal /\
          match normalInst (Build_UserThreadState rf pcc, mem) with
          | Ok (Build_UserThreadState rf' pcc', mem') =>
            let caps := pcc :: capsOfRf rf in
            let caps' := pcc' :: capsOfRf rf' in
            In Perm.Exec pcc.(capPerms)
            /\ ValidMemUpdate mem caps mem'
            /\ ReachableCaps mem caps caps'
            /\ In Perm.Exec pcc'.(capPerms)
            /\ ValidRf rf'
          | Exn _ => True
          end.
    End NormalInst.

    Section SystemInst.
      Variable systemInst: UserContext -> SystemContext -> Result ExnInfo (UserContext * SystemContext).

      Definition FuncSystem := forall rf pcc mepcc exnInfo ts ints m1 m2,
          ReachableMemSame m1 m2 ((pcc :: capsOfRf rf) ++ (mepcc :: capsOfTS ts)) ->
          match systemInst (Build_UserThreadState rf pcc, m1)
                  (Build_SystemThreadState mepcc exnInfo ts, ints),
                systemInst (Build_UserThreadState rf pcc, m2)
                                       (Build_SystemThreadState mepcc exnInfo ts, ints) with
          | Ok ((uts1, m1'), sc1), Ok ((uts2, m2'), sc2) =>
              uts1 = uts2 /\ sc1 = sc2 /\ UpdatedMemSame m1 m2 m1' m2'
          | Exn e1, Exn e2 => e1 = e2
          | _, _ => False
          end.

      Definition WfSystemInst pcc := forall rf mem mepcc exnInfo ts ints,
          ValidRf rf ->
          FuncSystem /\
          match systemInst (Build_UserThreadState rf pcc, mem) (Build_SystemThreadState mepcc exnInfo ts, ints) with
          | Ok ((Build_UserThreadState rf' pcc', mem'),
                  (Build_SystemThreadState mepcc' exnInfo' ts', ints')) =>
            let caps := (pcc :: capsOfRf rf) ++ (mepcc :: capsOfTS ts) in
            let caps' := (pcc' :: capsOfRf rf') ++ (mepcc' :: capsOfTS ts') in
            In Perm.Exec pcc.(capPerms)
            /\ In Perm.System pcc.(capPerms)
            /\ ValidMemUpdate mem caps mem'
            /\ ReachableCaps mem caps caps'
            /\ In Perm.Exec pcc'.(capPerms)
            /\ ValidRf rf'
          | Exn _ => True
          end.
    End SystemInst.

    Section GeneralInstruction.
      Variable generalInst: UserContext -> SystemContext -> Result ExnInfo (UserContext * SystemContext).

      (* If the pcc does not have system permissions, the instruction should behave as a function of user state. *)
      Definition WfGeneralInst :=
        (exists normalInst,
           WfNormalInst normalInst /\
           (forall rf pcc mem sysCtx,
              ~ In Perm.System pcc.(capPerms) ->
              match generalInst (Build_UserThreadState rf pcc, mem) sysCtx,
                    normalInst (Build_UserThreadState rf pcc, mem)  with
              | Ok (userCtx', sysCtx'), Ok (nuserCtx') =>
                  userCtx' = nuserCtx' /\ sysCtx = sysCtx'
              | Exn e1, Exn e2 =>
                  e1 = e2
              | _, _ => False
              end)) /\
        (forall pcc,
          In Perm.System pcc.(capPerms) ->
          WfSystemInst generalInst pcc).
    End GeneralInstruction.

    Section CallSentryInst.
      Variable callSentryInst: UserContext -> InterruptStatus ->
                               Result ExnInfo (PCC * RegisterFile * InterruptStatus).

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

      Definition WfCallSentryInst (src: RegIdx) (optLink: option RegIdx):= forall rf pcc ints mem,
          ValidRf rf ->
          src < ISA_NREGS /\
          (forall link, optLink = Some link -> link < ISA_NREGS) /\
          FuncCallSentry /\
          match callSentryInst (Build_UserThreadState rf pcc, mem) ints with
          | Ok (pcc', rf', ints') =>
            let caps := pcc :: capsOfRf rf in
            In Perm.Exec pcc.(capPerms) /\
            (exists src_cap,
               nth_error rf src = Some (inl src_cap) /\
               In Perm.Exec src_cap.(capPerms) /\
               match src_cap.(capSealed) with
               | Some (inl CallEnableInterrupt) => ints' = InterruptsEnabled
               | Some (inl CallDisableInterrupt) => ints' = InterruptsDisabled
               | Some (inl CallInheritInterrupt) => ints' = ints
               | None => ints' = ints (* TODO: Does this handle unsealed? *)
               | _ => False
               end /\
             pcc' = setCapSealed src_cap None) /\
             match optLink with
             | Some link =>
                 (forall idx, idx <> link -> nth_error rf' idx = nth_error rf idx)
                 /\ (exists linkCap,
                        nth_error rf' link = Some (inl linkCap)
                        /\ RestrictUnsealed pcc linkCap (* TODO: Check correctness *)
                        /\ linkCap.(capSealed) = Some (inl (if ints
                                                            then RetEnableInterrupt
                                                            else RetDisableInterrupt))
                        /\ In Perm.Exec linkCap.(capPerms))
             | None => rf' = rf
             end
          | Exn _ => True
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

      Definition WfRetSentryInst (src_idx: RegIdx):= forall rf pcc mem,
          ValidRf rf ->
          FuncRetSentry /\
          (src_idx < ISA_NREGS) /\
          match retSentryInst (Build_UserThreadState rf pcc, mem) with
          | Ok (pcc', ints') =>
            In Perm.Exec pcc.(capPerms) /\
            (exists src_cap,
                nth_error rf src_idx = Some (inl src_cap) /\
                In Perm.Exec src_cap.(capPerms) /\
                match src_cap.(capSealed) with
                | Some (inl RetEnableInterrupt) => ints' = InterruptsEnabled
                | Some (inl RetDisableInterrupt) => ints' = InterruptsDisabled
                | _ => False (* TODO: if we want to support unsealed returns, how do we do it (we don't have ints)? *)
                end /\
                pcc' = setCapSealed src_cap None)
          | Exn e => True
          end.
    End RetSentryInst.

    (* TODO: This might be needed for ECall; or can we move ECall to normal instruction decode? *)
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
    | Inst_General generalInst (wf: WfGeneralInst generalInst)
    | Inst_Call (srcReg: RegIdx) (optLink: option RegIdx) callSentryInst
                (wf: WfCallSentryInst callSentryInst srcReg optLink)
    | Inst_Ret (srcReg: RegIdx) retSentryInst (wf: WfRetSentryInst retSentryInst srcReg)
    | Inst_Exn exnInst (wf: WfExnInst exnInst).

    (* WIP *)
    Notation ThreadIdx := nat (only parsing).
    Inductive SameThreadEvent :=
    | Ev_Exception
    | Ev_Call (pcc: PCC) (rf: RegisterFile) (is: InterruptStatus)
    | Ev_Ret (pcc: PCC) (rf: RegisterFile) (is: InterruptStatus)
    | Ev_General.
    Inductive Event :=
    | Ev_SwitchThreads (idx: nat)
    | Ev_SameThread (idx: ThreadIdx) (ev: SameThreadEvent).
    Definition Trace := list Event.

    Section FetchDecodeExecute.
      Variable fetchAddrs: FullMemory -> Addr -> list Addr.
      (* Addresses fetched should not depend on arbitrary memory regions. *)
      Definition FetchAddrsOk :=
        exists (fn: Addr -> list Addr),
        forall mem1 mem2 addr,
          (forall a, In a (fn addr) -> readByte mem1 a = readByte mem2 a
          (* TODO: Do we need tags to be the same? *)
          (* /\ readTag mem1 (toCapAddr a) = readTag mem2 (toCapAddr a) *) ) ->
          fetchAddrs mem1 addr = fetchAddrs mem2 addr.
      Context {fetchAddrsOk: FetchAddrsOk}.

      Variable decode : list Byte -> Inst.
      Variable pccNotInBounds: EXNInfo.

      Section WithContext.
        Variable fc: UserContext * SystemContext.
        Definition uc := fst fc.
        Definition mem : FullMemory := snd uc.
        Definition pcc := (fst uc).(thread_pcc).
        Definition rf := (fst uc).(thread_rf).
        Definition sc := snd fc.
        Definition sts := fst sc.
        Definition ints := snd sc.
        Definition mepcc := (fst sc).(thread_mepcc).

        Definition exceptionState (exnInfo: EXNInfo): (UserContext * SystemContext) * SameThreadEvent :=
          (((Build_UserThreadState rf mepcc, mem),
             (Build_SystemThreadState pcc exnInfo sts.(thread_trustedStack), ints)
           ), Ev_Exception).

        Definition threadStepFunction: (UserContext * SystemContext) * SameThreadEvent :=
          match decode (map (readByte mem) (fetchAddrs mem pcc.(capCursor))) with
          | Inst_General generalInst wf =>
              match generalInst uc sc with
              | Ok (uc', sc') => ((uc', sc'), Ev_General)
              | Exn e => (exceptionState e)
              end
          | Inst_Call src optLinkReg callSentryInst wf =>
              match callSentryInst uc ints with
              | Ok (pcc', rf', ints') =>
                   (((Build_UserThreadState rf' pcc', mem), (sts, ints')), Ev_Call pcc' rf' ints')
              | Exn e => (exceptionState e)
              end
          | Inst_Ret srcReg retSentryInst wf =>
              match retSentryInst uc with
              | Ok (pcc', ints') =>
                  (((Build_UserThreadState rf pcc', mem), (sts, ints')), Ev_Ret pcc' rf ints')
              | Exn e => (exceptionState e)
              end
          | Inst_Exn exnInst wf =>
              (exceptionState (exnInst uc))
          end.

        Definition fetchAddrsInBounds := Subset (fetchAddrs mem pcc.(capCursor)) pcc.(capAddrs)
                                         /\ In pcc.(capCursor) pcc.(capAddrs).

        Inductive ThreadStep : ((UserContext * SystemContext) * SameThreadEvent) -> Prop :=
        | GoodUserThreadStep (inBounds: fetchAddrsInBounds) : ThreadStep threadStepFunction
        | BadUserFetch (notInBounds: ~ fetchAddrsInBounds) : ThreadStep (exceptionState pccNotInBounds).
      End WithContext.

      Definition setMachineThread (m: Machine) (tid: nat): Machine :=
        {| machine_memory := m.(machine_memory);
           machine_interruptStatus := m.(machine_interruptStatus);
           machine_threads := m.(machine_threads);
           machine_curThreadId := tid
        |}.

      (* TODO: Can we just have a single MachineStep constructor,
         where if interrupts are disabled, the thread has to match the previous step's?
         Would such a change create a problem when it comes to implementing the thread switcher? *)
      Inductive SameThreadStep : Machine -> Machine -> Event -> Prop :=
      | SameThreadStepOk m1 m2 ev
          (threadIdEq: m2.(machine_curThreadId) = m1.(machine_curThreadId))
          (idleThreadsEq: forall n, n <> m1.(machine_curThreadId) ->
                               nth_error m2.(machine_threads) n = nth_error m1.(machine_threads) n)
          (stepOk: forall userSt' mem' sysSt' interrupt',
            exists thread, nth_error m1.(machine_threads) m1.(machine_curThreadId) = Some thread /\
                             ThreadStep ((thread.(thread_userState), m1.(machine_memory)),
                                 (thread.(thread_systemState), m1.(machine_interruptStatus)))
                               (((userSt', mem'), (sysSt', interrupt')), ev)->
                           m2.(machine_memory) = mem' /\
                             m2.(machine_interruptStatus) = interrupt' /\
                             nth_error m2.(machine_threads) m2.(machine_curThreadId)
                             = Some (Build_Thread userSt' sysSt')) :
        SameThreadStep m1 m2 (Ev_SameThread m2.(machine_curThreadId) ev).

      Inductive MachineStep : Machine * Trace -> (Machine * Trace -> Prop) -> Prop :=
      | Step_SwitchThreads:
        forall m tr tid' post,
        m.(machine_interruptStatus) = InterruptsEnabled ->
        tid' < List.length m.(machine_threads) ->
        post ((setMachineThread m tid'),(tr ++ [Ev_SwitchThreads tid'])) ->
        MachineStep (m, tr) post
      | Step_SameThread:
        forall m1 m2 tr ev post,
        SameThreadStep m1 m2 ev ->
        post (m2, tr ++ [ev]) ->
        MachineStep (m1, tr) post.

    End FetchDecodeExecute.
  End Machine.
End Machine.

Module Combinators.
  Section __.
    Context [State : Type] (step: State -> (State -> Prop) -> Prop).
    Inductive always(P: State -> Prop)(initial: State): Prop :=
    | mk_always
        (invariant: State -> Prop)
        (Establish: invariant initial)
        (Preserve: forall s, invariant s -> step s invariant)
        (Use: forall s, invariant s -> P s).
  End __.
End Combinators.

Module Separation.
  Definition Disjoint {T: Type} (xs ys: list T) : Prop :=
    forall t, In t xs -> In t ys -> False.

  Definition Separated {T: Type} (xss: list (list T)) : Prop :=
    forall i j xi xj,
      i <> j ->
      nth_error xss i = Some xi ->
      nth_error xss j = Some xj ->
      Disjoint xi xj.

End Separation.

Section ListUtils.
  Lemma Forall2_refl {A: Type} (R: A -> A -> Prop) :
    forall xs,
    (forall a, R a a) ->
    Forall2 R xs xs.
  Proof.
    induction xs; auto.
  Qed.
End ListUtils.
Module Configuration.
  Import Separation.
  Import ListNotations.

  Section __.
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {bytesToCapUnsafe: Bytes (Byte:=Byte) -> Spec.Cap (Key:=Key)}.

    Notation FullMemory := (@FullMemory Byte).
    Notation EXNInfo := (@EXNInfo Byte).
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> Inst bytesToCapUnsafe}.
    Context {pccNotInBounds : EXNInfo}.
    Notation Machine := (@Machine Byte Key).
    Notation Cap := (@Cap Key).
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation Thread := (@Thread Byte Key).
    Notation ReachableCaps := (@ReachableCaps ISA Byte Key bytesToCapUnsafe).
    Notation RegisterFile := (@RegisterFile Byte Key).

    Definition ExportEntry : Type.
    Admitted.

    Definition ImportEntry : Type.
    Admitted.

    Record InitialThreadMetadata := {
        initThreadEntryPoint: Addr;
        initThreadRf : list RegisterFile;
        initThreadStackSize: nat;
        initThreadStackAddr: Addr
    }.

    Record Compartment := {
        compartmentReadOnly: list Addr; (* Code and read-only data, including import entries *)
        compartmentGlobals: list Addr;
        compartmentExports: list ExportEntry;
        compartmentImports: list ImportEntry
    }.

    Record Config := {
        configCompartments: list Compartment;
        configSwitcher: nat;
        configThreads : list InitialThreadMetadata;
        configInitMemory: FullMemory
        (* configMMIOAddrs: list Addr; *)
    }.

    Definition compartmentFootprint (compartment: Compartment) : list Addr :=
        compartment.(compartmentReadOnly) ++ compartment.(compartmentGlobals).
    Definition stackFootprint (t: InitialThreadMetadata) : list Addr :=
        seq t.(initThreadStackAddr) t.(initThreadStackSize).
    Record WFCompartment (compartment: Compartment) := {
        (* WFCompartment_addrs: Disjoint compartment.(compartmentReadOnly) compartment.(compartmentGlobals); *)
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

    (* WIP *)
    Record ValidInitialState (config: Config) (m: Machine) : Prop :=
      { ValidInit_memory: m.(machine_memory) = config.(configInitMemory)
      }.

  End __.
End Configuration.

(* From a valid initial state where threads are in disjoint compartments, for
   any sequence of same-domain (Ev_General) steps, the reachable caps in each
   thread do not increase.
 *)
Module ThreadIsolatedMonotonicity.
  Import ListNotations.
  Import Configuration.
  Section __.
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {bytesToCapUnsafe: Bytes (Byte:=Byte) -> Spec.Cap (Key:=Key)}.

    Notation FullMemory := (@FullMemory Byte).
    Notation EXNInfo := (@EXNInfo Byte).
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> Inst bytesToCapUnsafe}.
    Context {pccNotInBounds : EXNInfo}.
    Notation Machine := (@Machine Byte Key).
    Notation Cap := (@Cap Key).
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation Thread := (@Thread Byte Key).
    Notation ReachableCaps := (@ReachableCaps ISA Byte Key bytesToCapUnsafe).
    Notation Trace := (@Trace Byte Key).
    Notation State := (Machine * Trace)%type.
    Notation Event := (@Event Byte Key).
    Notation Config := (@Config ISA Byte Key bytesToCapUnsafe fetchAddrs decode pccNotInBounds).

    Definition SameDomainEvent (ev: Event) : Prop :=
      (exists idx, ev = Ev_SwitchThreads idx) \/
      (exists idx, ev = Ev_SameThread idx Ev_General).
    Definition SameDomainTrace (tr: Trace) : Prop :=
      Forall SameDomainEvent tr.

    (* TODO: add additional restrictions *)
    Definition ValidInitialMachine (config: Config) (st: Machine) : Prop :=
      ValidInitialState config st.

    Section WithConfig.
      Variable config: Config.
      Variable initialMachine: Machine.

      Definition ReachableCapSubset (t_init t_cur: Thread) : Prop :=
        ReachableCaps initialMachine.(machine_memory) (capsOfThread t_init) (capsOfThread t_cur).

      (* A thread's caps are a subset of caps reachable from initial state. *)
      Definition PThreadIsolatedMonotonicity (st: State) : Prop :=
        let '(machine, tr) := st in
        SameDomainTrace tr ->
        Forall2 ReachableCapSubset
                initialMachine.(machine_threads) machine.(machine_threads).

      Definition Invariant (st: State) : Prop :=
        let '(machine, tr) := st in
        SameDomainTrace tr ->
        Forall2 ReachableCapSubset
                initialMachine.(machine_threads) machine.(machine_threads).

      Lemma InvariantInitial  :
        ValidInitialMachine config initialMachine ->
        Invariant (initialMachine, []).
      Proof.
        cbv [Invariant SameDomainTrace ReachableCapSubset].
        intros * hValidInit hTr.
        apply Forall2_refl.
        solve[constructor; auto].
      Qed.

      (* TODO: Non-determinism *)
      Lemma InvariantStep (s: State) :
        Invariant s ->
        MachineStep s Invariant.
      Proof.
        cbv [Invariant]. destruct s. intros Hinv.
      Admitted.

      Lemma InvariantUse (s: State) :
        Invariant s ->
        PThreadIsolatedMonotonicity s.
      Proof.
        auto.
      Qed.
    End WithConfig.

    Theorem ThreadIsolatedMonotonicity :
      forall config initial_machine,
      WFConfig config ->
      ValidInitialMachine config initial_machine ->
      Combinators.always MachineStep (PThreadIsolatedMonotonicity initial_machine) (initial_machine, []).
    Proof.
      intros * hwf_config hinit_ok.
      econstructor.
      - eapply InvariantInitial; eauto.
      - eapply InvariantStep; eauto.
      - eapply InvariantUse; eauto.
    Qed.
  End __.
End ThreadIsolatedMonotonicity.



Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil
  | Forall3_cons : forall (x : A) (y : B) (z: C) (l : list A) (l' : list B) (l'': list C),
                   R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z::l'').

Module Properties.
  Section __.
    Context [ISA: ISA_params].
    Context [Byte Key: Type].
    Context [bytesToCapUnsafe: Bytes (Byte:=Byte) -> Spec.Cap (Key:=Key)].

    Notation FullMemory := (@FullMemory Byte).
    Notation EXNInfo := (@EXNInfo Byte).
    Context [fetchAddrs: FullMemory -> Addr -> list Addr].
    Context [decode: list Byte -> Inst bytesToCapUnsafe].
    Context [pccNotInBounds : EXNInfo].
    Notation Machine := (@Machine Byte Key).
    Notation Cap := (@Cap Key).
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation Thread := (@Thread Byte Key).
    Notation ReachableCaps := (@ReachableCaps ISA Byte Key bytesToCapUnsafe).

    Record ExportEntry := {
        exportEntryAddr: Addr;
        exportEntryStackSize : nat;
        exportEntryNumArgs: nat;
        exportEntryInterruptStatus: InterruptStatus
    }.

    Inductive ImportEntry :=
    | ImportEntry_SealedCapToExportEntry (c: Cap) (* Cap or addr? *)
    | ImportEntry_SentryToLibraryFunction (c: Cap) (* Cap or addr? *)
    | ImportEntry_MMIOCap (c: Cap).
    (* | ImportEntry_SharedObject (c: Cap). *) (* TODO! *)

    Record Compartment := {
        compartmentReadOnly: list Addr; (* Code and read-only data, including import entries *)
        compartmentGlobals: list Addr;
        compartmentExports: list ExportEntry;
        compartmentImports: list ImportEntry
    }.

    Record InitialThreadMetadata := {
        initThreadEntryPoint: Addr;
        initThreadStackSize: nat;
        initThreadStackAddr: Addr
    }.

    Record Config := {
        configCompartments: list Compartment;
        configSwitcher: nat;
        configThreads : list InitialThreadMetadata;
        configMMIOAddrs: list Addr;
    }.

    (* Each thread is in a compartment. *)
    Record ThreadGhostState := {
        threadGhost_compartmentIdx : nat
    }.

    (* The ghost state should capture:
       - The compartment each thread is in.
       - The arguments each callee had access to at time of entry, and the history of return values.
     *)
    Record GhostState : Type := {
        ghostThreads : list ThreadGhostState
    }.

    Definition Trace : Type. Admitted.
    Definition State : Type := Machine * GhostState * Trace.

    Definition compartmentFootprint (compartment: Compartment) : list Addr :=
        compartment.(compartmentReadOnly) ++ compartment.(compartmentGlobals).

    Definition stackFootprint (t: InitialThreadMetadata) : list Addr :=
      seq t.(initThreadStackAddr) t.(initThreadStackSize).

    Record WFCompartment (compartment: Compartment) := {
        WFCompartment_addrs: Disjoint compartment.(compartmentReadOnly) compartment.(compartmentGlobals);
    }.

    (* Memory should be separately divided into:
       - Compartment-owned code&read-only and global regions.
       - A stack per thread.
       - Device and MMIO memory
       - TODO(??): Pre-shared objects (potentially shared between compartments).
     *)
    Definition ConfigFootprints (config: Config) :=
        (configMMIOAddrs config)
          ::((map compartmentFootprint config.(configCompartments))
                                   ++ (map stackFootprint config.(configThreads))).

    (* Import entries should belong to another compartment's read only regions
       and be exported by the other compartment.

       TODO: These properties potentially are not all needed.
     *)
    Definition ImportEntriesOk (config: Config) :=
      forall i compartment entry,
        nth_error config.(configCompartments) i = Some compartment ->
        In entry compartment.(compartmentImports) ->
        match entry with
        | ImportEntry_MMIOCap c => Subset c.(capAddrs) config.(configMMIOAddrs)
        | ImportEntry_SealedCapToExportEntry c =>
            isSealedDataCap c = true /\
            (exists j compartment',
                i <> j /\
                nth_error config.(configCompartments) j = Some compartment' /\
                Subset c.(capAddrs) compartment'.(compartmentReadOnly) /\
                exists export_entry, In export_entry compartment'.(compartmentExports) /\
                                export_entry.(exportEntryAddr) = c.(capCursor)
            )
        | ImportEntry_SentryToLibraryFunction c =>
            isSentry c = true /\
            (exists j compartment',
                i <> j /\
                nth_error config.(configCompartments) j = Some compartment' /\
                Subset c.(capAddrs) compartment'.(compartmentReadOnly) /\
                exists export_entry, In export_entry compartment'.(compartmentExports) /\
                                export_entry.(exportEntryAddr) = c.(capCursor)
            )
        end.

    (* TODO *)
    Definition WFSwitcher (c: Compartment) : Prop := True.

    Record WFConfig (config: Config) := {
        WFConfig_footprintDisjoint: Separated (ConfigFootprints config);
        WFConfig_compartments: forall c, In c config.(configCompartments) -> WFCompartment c;
        WFConfig_switcher: exists c, nth_error config.(configCompartments) config.(configSwitcher) = Some c /\
                                WFSwitcher c;
        WFConfig_importEntriesOk: ImportEntriesOk config
    }.

    (* Initially:
     * - The only caps a compartment has access to outside itself are in the import table,
           - either in the MMIO region, a sentry, or sealed with a key that only the switcher can access.
           - indirectly, a compartment has access to read only data from library calls.
     * - Only the switcher has:
         - system access permission.
         - the unsealing key for export data entries.
     *)
    Definition InitialMachine (config: Config) : Machine.
    Admitted.

    Section Invariant.
      Variable config: Config.
      Variable st: State.
      Notation machine := (fst (fst st)) (only parsing).
      Notation trace := ((snd st)) (only parsing).
      Notation ghost := (snd (fst st)) (only parsing).
      Notation memory := machine.(machine_memory).

      Section WithThread.
        Variable t: Thread.
        Variable tghost: ThreadGhostState.
        Notation rf := t.(thread_userState).(thread_rf).
        Notation pcc := t.(thread_userState).(thread_pcc).
        Notation baseCaps := (pcc::(capsOfRf rf)).

        (* Threads running in user mode:
           - do not have access to the system access permission.
           - do not have access to the unsealing key for export data entries.
         *)
        Record InUserMode : Prop := {
            userMode_noSystemAccessPerm :
              forall c caps, ReachableCaps memory baseCaps caps ->
                        In c caps ->
                        In Perm.System c.(capPerms) ->
                        c.(capSealed) = None ->
                        False
        }.

        Record InSystemMode : Prop := {
        }.
      End WithThread.

      (* Top-level invariant: a compartment should only have access to its caps
         from its initial state and any caps explicitly passed through
         arguments/return values.
       *)
      Record ThreadInv (initialThread: InitialThreadMetadata) (t: Thread) (tghost: ThreadGhostState): Prop :=
      { threadInUserMode : tghost.(threadGhost_compartmentIdx) <> config.(configSwitcher) ->
                           InUserMode t
      ; threadInSystemMode : tghost.(threadGhost_compartmentIdx) = config.(configSwitcher) ->
                             InSystemMode
      }.

      Record Invariant := {
        Inv_curThread: exists t, nth_error machine.(machine_threads) machine.(machine_curThreadId) = Some t;
        Inv_threads: Forall3 ThreadInv config.(configThreads) machine.(machine_threads) ghost.(ghostThreads)
      }.

    End Invariant.

    Context [ExnHandlerType : Type].

  End __.
End Properties.

Module CHERIoTValidation.
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

  Definition mk_abstract_cap (c: cheriot_cap) : @Cap N :=
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
