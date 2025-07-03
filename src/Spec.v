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
  Scheme Equality for Label.

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

    Definition isSealed (c: Cap) :=
      match c.(capSealed) with
      | Some _ => true
      | _ => false
      end.

    Notation PermIntersect perms1 perms2 := (filter (fun p => existsb (Perm.t_beq p) perms2) perms1).
    Notation LabelIntersect labels1 labels2 := (filter (fun p => existsb (Label_beq p) labels2) labels1).

    Definition AttenuatePermsIfNotSealed (sealed: bool) (perms1 perms2: list Perm.t) :=
      if sealed then perms2
      else PermIntersect perms1 perms2.
    Definition AttenuateLabelsIfNotSealed (sealed: bool) (labels1 labels2: list Label) :=
      if sealed then labels2
      else LabelIntersect labels1 labels2.

    Definition attenuate (loadAuthCap: Cap) (loaded: Cap) : Cap :=
      let sealed := isSealed loaded in
      {| capSealed          := loaded.(capSealed);
         capPerms           := AttenuatePermsIfNotSealed  sealed loadAuthCap.(capKeepPerms) loaded.(capPerms);
         capCanStore        := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanStore) loaded.(capCanStore);
         capCanBeStored     := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanBeStored) loaded.(capCanBeStored);
         capSealingKeys     := loaded.(capSealingKeys);
         capUnsealingKeys   := loaded.(capUnsealingKeys);
         capAddrs           := loaded.(capAddrs);
         capKeepPerms       := AttenuatePermsIfNotSealed  sealed loadAuthCap.(capKeepPerms) loaded.(capKeepPerms);
         capKeepCanStore    := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanStore) loaded.(capKeepCanStore);
         (* TODO: Double check this does not attenuate if sealed *)
         capKeepCanBeStored := AttenuateLabelsIfNotSealed sealed loadAuthCap.(capKeepCanBeStored) loaded.(capKeepCanBeStored);
         capCursor          := loaded.(capCursor)
      |}.

  End CapHelpers.

  Section CurrMemory.
    Variable mem: FullMemory.

    Section CapStep.
      Variable x: Cap.
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

      Record LoadCap : Prop :=
        { loadAuthUnsealed : x.(capSealed) = None;
          loadAuthPerm: In Perm.Load x.(capPerms) /\ In Perm.Cap x.(capPerms);
          loadFromAuth: exists capa, Subset (seq (fromCapAddr capa) ISA_CAPSIZE_BYTES) x.(capAddrs) /\
                                readCap mem capa = inl y;
          (* When a cap y is loaded using a cap x, then the attentuation of x comes into play to create z *)
          loadAttenuate: z = attenuate x y
        }.

      (* Cap z is the sealed version of cap y using a key in x *)
      Definition Seal : Prop :=
        exists k, In k x.(capSealingKeys) /\
             y.(capSealed) = None /\
             z = setCapSealed y (Some (inr k)).

      Definition Unseal : Prop :=
        exists k, In k x.(capSealingKeys) /\
             y.(capSealed) = Some (inr k) /\
             z = setCapSealed y None.
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

        Definition StPermForAddr (auth: Cap) (a: Addr) (sz: nat) :=
          ReachableCap auth
          /\ In Perm.Store auth.(capPerms)
          /\ auth.(capSealed) = None
          /\ Subset (seq a sz) auth.(capAddrs).

        Definition StPermForCap (auth: Cap) (capa: CapAddr) :=
          StPermForAddr auth (fromCapAddr capa) ISA_CAPSIZE_BYTES.

        Definition ValidMemCapUpdate :=
          forall capa stDataCap, readCap mem capa <> readCap mem' capa ->
                            readCap mem' capa = inl stDataCap ->
                            ReachableCap stDataCap /\
                            exists stAddrCap, StPermForCap stAddrCap capa
                                         /\ (exists l, In l stAddrCap.(capCanStore) /\
                                                 In l stDataCap.(capCanBeStored)
                                           ).

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
              | Exn e => exceptionState e
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
        | GoodUserThreadStep (inBounds: fetchAddrsInBounds) :
          ThreadStep threadStepFunction
        | BadUserFetch (notInBounds: ~ fetchAddrsInBounds) :
            ThreadStep (exceptionState pccNotInBounds).
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
      | SameThreadStepOk :
        forall m1 m2 ev
          (threadIdEq: m2.(machine_curThreadId) = m1.(machine_curThreadId))
          (idleThreadsEq: forall n, n <> m1.(machine_curThreadId) ->
                            nth_error m2.(machine_threads) n = nth_error m1.(machine_threads) n)
          (stepOk: exists thread userSt' sysSt',
                   nth_error m1.(machine_threads) m1.(machine_curThreadId) = Some thread /\
                   ThreadStep ((thread.(thread_userState), m1.(machine_memory)),
                               (thread.(thread_systemState), m1.(machine_interruptStatus)))
                              ((userSt', m2.(machine_memory)), (sysSt', m2.(machine_interruptStatus)), ev) /\
                   nth_error m2.(machine_threads) m2.(machine_curThreadId) = Some (Build_Thread userSt' sysSt')),
          SameThreadStep m1 m2 (Ev_SameThread m2.(machine_curThreadId) ev).
      Inductive MachineStep : Machine * Trace -> Machine * Trace -> Prop :=
      | Step_SwitchThreads m tr tid'
          (iEnabled: m.(machine_interruptStatus) = InterruptsEnabled)
          (tidOk: tid' < List.length m.(machine_threads)):
        MachineStep (m, tr) ((setMachineThread m tid'),(tr ++ [Ev_SwitchThreads tid']))
      | Step_SameThread m1 m2 tr ev
          (stepOk:SameThreadStep m1 m2 ev):
        MachineStep (m1, tr) (m2, tr ++ [ev]) .

    End FetchDecodeExecute.
  End Machine.
End Machine.

Module Combinators.
  Section __.
    Context [State : Type] (step: State -> State -> Prop).
    Inductive always(P: State -> Prop)(initial: State): Prop :=
    | mk_always
        (invariant: State -> Prop)
        (Establish: invariant initial)
        (Preserve: forall s t, invariant s -> step s t -> invariant t)
        (Use: forall s, invariant s -> P s).
  End __.
End Combinators.

Module Separation.
  Definition Disjoint {T: Type} (xs ys: list T) : Prop :=
    forall t, In t xs -> In t ys -> False.

  Definition Pairwise {T: Type} (P: T -> T -> Prop) (xss: list T) : Prop :=
    forall i j xi xj,
      i <> j ->
      nth_error xss i = Some xi ->
      nth_error xss j = Some xj ->
      P xi xj.

  Definition Separated {T: Type} (xss: list (list T)) : Prop :=
    Pairwise Disjoint xss.

End Separation.

Lemma simple_tuple_inversion:
  forall {A} {B} (a: A) (b: B) x y,
  (a,b) = (x,y) ->
  a = x /\ b = y.
Proof.
  intros. inversion H. auto.
Qed.

Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : False |- _ => contradiction
  | H : ?x = _ |- _ => subst x
  | H: _ = ?x |- _ => subst x
  | [ H: (_,_) = (_,_) |- _ ] =>
    apply simple_tuple_inversion in H;
    let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  end.
Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  end.

Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  | H: context[let '(_,_) := ?x in _] |- _ =>
    destruct x eqn:?
  | |- context[let '(_,_) := ?x in _] =>
    destruct x eqn:?
  end.
Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | _ =>
      destruct e eqn:?
  end.

Ltac destruct_matches_in_hyp H :=
  lazymatch type of H with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | ?v =>
      let H1 := fresh H in
      destruct v eqn:H1
  end.
Tactic Notation "case_match" "eqn" ":" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.
Ltac case_match :=
  let H := fresh in case_match eqn:H.
Search Nat.eqb true.
Ltac simplify_nats :=
  match goal with
  | H: Nat.eqb _ _ = true |- _ =>
      rewrite PeanoNat.Nat.eqb_eq in H
  | H: Nat.eqb _ _ = false |- _ =>
      rewrite PeanoNat.Nat.eqb_neq in H
  end.
Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | reflexivity ].
Tactic Notation "fast_by" tactic(tac) :=
  tac; fast_done.
Ltac done :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    | progress intros
    | solve [symmetry; trivial]
    | discriminate
    | contradiction
    | split
    ]
  ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

Section OptionUtils.
  Lemma Some_inj :
    forall A (x y:A),
    Some x = Some y ->
    x = y.
  Proof.
    intros. inversion H. auto.
  Qed.
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ \/ _ => destruct H as [H|H]
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.

End OptionUtils.
Ltac option_simpl :=
  repeat match goal with
  | H : Some ?x = Some _ |- _ => apply Some_inj in H; simplify_eq
  | H : ?x = Some ?y, H1 : ?x = Some ?z |- _ => rewrite H in H1; apply Some_inj in H1; try subst y; try subst z
  end.

Ltac simplify_Result :=
  repeat match goal with
  | H: match ?x with | Ok _ => _ | Exn _ => False end |- _ =>
      let Ht := fresh H "Ok" in
      destruct x eqn:Ht; [ | contradiction]
  end.
Tactic Notation "split_and" :=
  match goal with
  | |- _/\ _ => split
  end.
Tactic Notation "split_and" "?" := repeat split_and.
Tactic Notation "split_and" "!" := hnf; split_and; split_and?.
Lemma SubsetFilter1:
  forall {A} (xs ys: list A) eqb,
  (forall p q, eqb p q = true -> p = q) ->
  Subset (filter (fun p => existsb (eqb p) xs) ys) xs.
Proof.
  cbv[Subset]. intros * eqb *.
  rewrite filter_In, existsb_exists.
  intros; destruct_products; eauto.
  apply eqb in Hrr. subst; auto.
Qed.

Lemma Subset_app:
  forall {A} (xs ys: list A),
  Subset xs (xs ++ ys).
Proof.
  cbv[Subset].
  intros. apply in_or_app. auto.
Qed.
Lemma Subset_refl :
  forall {A} (xs: list A),
  Subset xs xs.
Proof.
  cbv[Subset]. auto.
Qed.
Ltac simplify_Subset :=
  repeat match goal with
  | |- Subset ?x (?x ++ _) =>
      apply Subset_app
  | |- Subset ?x ?x =>
      apply Subset_refl
  end.

Section ListUtils.
  Import ListNotations.
  Lemma Forall_one:
    forall {T} (x: T) P,
    Forall P [x] ->
    P x.
  Proof.
    inversion 1. auto.
  Qed.

  Lemma Forall2_refl {A: Type} (R: A -> A -> Prop) :
    forall xs,
    (forall a, R a a) ->
    Forall2 R xs xs.
  Proof.
    induction xs; auto.
  Qed.
  Lemma Forall2_nth_error1 : forall A B (R: A -> B -> Prop) xs ys,
      length xs = length ys ->
      (forall idx x y, nth_error xs idx = Some x ->
                  nth_error ys idx = Some y ->
                  R x y) ->
      Forall2 R xs ys.
  Proof.
    induction xs.
    - destruct ys; try discriminate; auto.
    - destruct ys; try discriminate.
      intros; constructor; eauto.
      + eapply H0 with (idx := 0); eauto.
      + eapply IHxs; eauto.
        intros; eapply H0 with (idx := S idx); auto.
  Qed.

  Lemma Forall2_nth_error2 : forall A B (R: A -> B -> Prop) xs ys,
      Forall2 R xs ys ->
      forall idx x y,
      nth_error xs idx = Some x ->
      nth_error ys idx = Some y ->
      R x y.
  Proof.
    induction 1.
    - intros *; rewrite nth_error_nil. discriminate.
    - destruct idx; cbn; intros;
        repeat match goal with
        | H: Some _ = Some _ |- _ => apply Some_inj in H; subst
        end; eauto.
  Qed.

  Lemma Forall2_nth_error2' : forall A B (R: A -> B -> Prop) xs ys idx,
      Forall2 R xs ys ->
      idx < length xs ->
      exists x y,
      nth_error xs idx = Some x /\
      nth_error ys idx = Some y /\
      R x y.
  Proof.
    intros.
    destruct (nth_error xs idx) eqn:?.
    destruct (nth_error ys idx) eqn:?.
    - exists a; exists b; repeat split; auto.
      eapply Forall2_nth_error2; eauto.
    - apply nth_error_None in Heqo0. rewrite Forall2_length with (1 := H) in H0. lia.
    - apply nth_error_None in Heqo. lia.
  Qed.

End ListUtils.

Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ \/ _ => destruct H as [H|H]
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.
Lemma Some_not_None :
  forall A (a: A) x,
  x = Some a ->
  x <> None.
Proof.
  destruct x; congruence.
Qed.

Lemma listUpdate_length:
  forall A (xs ys: list A) idx a,
  (forall n, n <> idx -> nth_error ys n = nth_error xs n) ->
  idx < length xs ->
  nth_error ys idx = Some a ->
  length xs = length ys.
Proof.
  intros * herror hlen hsome.
  destruct_with_eqn (Nat.eqb (length xs) (length ys)); simplify_nats; auto.
  exfalso.
  assert (length xs < length ys \/ length ys < length xs) as Hcase by lia.
  destruct_or! Hcase; exfalso.
  - rewrite<-nth_error_Some in Hcase.
    rewrite herror in Hcase by lia.
    rewrite nth_error_Some in Hcase. lia.
  - destruct_with_eqn (Nat.ltb idx (length ys)).
    + rewrite PeanoNat.Nat.ltb_lt in *.
      rewrite<-nth_error_Some in Hcase.
      rewrite<-herror in Hcase by lia.
      rewrite nth_error_Some in Hcase. lia.
    + rewrite PeanoNat.Nat.ltb_nlt in *.
      apply Some_not_None in hsome.
      apply nth_error_Some in hsome. lia.
Qed.
Create HintDb invariants.
Import ListNotations.

Ltac consider X :=
  unfold X in *.
Ltac simplify_Forall :=
  repeat match goal with
  | H : Forall _ (_ ++ _ ) |- _ =>
      apply Forall_app in H;
      let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | H : Forall _ [_] |- _ =>
      apply Forall_one in H
  end.
Ltac propositional :=
  repeat match goal with
  | H1: ?x -> _, H2: ?x |- _ =>
      specialize H1 with (1 := H2)
  end.
Ltac assert_pre_and_specialize H :=
  match type of H with
  | ?x -> _ => let Hx := fresh in assert x as Hx; [ | specialize H with (1 := Hx); clear Hx]
  end.
Set Nested Proofs Allowed.

Module Configuration.
  Import Separation.

  Section __.
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {bytesToCapUnsafe: Bytes (Byte:=Byte) -> Spec.Cap (Key:=Key)}.
    Notation FullMemory := (@FullMemory Byte).
    Notation EXNInfo := (@EXNInfo Byte).
    Notation Cap := (@Cap Key).
    Notation CapOrBytes := (@CapOrBytes Byte Key).
    Notation ReachableCaps := (ReachableCaps bytesToCapUnsafe).
    Notation ReachableCap := (ReachableCap bytesToCapUnsafe).
    Notation LoadCap := (LoadCap bytesToCapUnsafe).
    Notation ValidMemCapUpdate := (ValidMemCapUpdate bytesToCapUnsafe).
    Notation ValidMemTagRemoval := (ValidMemTagRemoval bytesToCapUnsafe).
    Notation ValidMemDataUpdate := (ValidMemDataUpdate bytesToCapUnsafe).
    Notation ValidMemUpdate := (@ValidMemUpdate ISA Byte Key bytesToCapUnsafe).
    Notation ReachableAddr := (@ReachableAddr ISA Byte Key bytesToCapUnsafe).

    Section Helpers.
      (* TODO: decidable equality *)
      Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).
      Context {Cap_eqb: Cap -> Cap -> bool}.
      Context {Cap_eq_dec: EqDecider Cap_eqb}.
      Context {CapOrBytes_eqb: CapOrBytes -> CapOrBytes -> bool}.
      Context {CapOrBytes_eq_dec: EqDecider CapOrBytes_eqb}.
      Lemma ReachableCapIncrease:
        forall mem caps capss caps',
          ReachableCap mem caps caps' ->
          Subset caps capss ->
          ReachableCap mem capss caps'.
      Proof.
        cbv[Subset].
        induction 1; intros hsubset.
        - apply Refl; auto.
        - eapply StepRestrict; eauto.
        - eapply StepLoadCap; eauto.
        - apply StepSeal with (x := x) (y := y); auto.
        - apply StepUnseal with (x := x) (y := y); auto.
      Qed.
      Lemma ReachableCaps_app:
        forall mem c1 c2 cs,
          ReachableCaps mem c1 c2 ->
          ReachableCaps mem (c1 ++ cs) (c2 ++ cs).
      Proof.
        cbv[ReachableCaps].
        intros * Hin * Hin2.
        apply in_app_or in Hin2.
        destruct_or! Hin2.
        - eapply ReachableCapIncrease; eauto. apply Subset_app.
        - constructor. apply in_app_iff; auto.
      Qed.

      Lemma AttenuateRestrict:
        forall (x y: Cap),
          Restrict y (attenuate x y).
      Proof.
        cbv [attenuate Restrict].
        intros.
        case_match; constructor; cbn; cbv[SealEq isSealed]; cbn; repeat simpl_match; cbn.
        all: repeat match goal with
             | |- EqSet ?x ?x => cbv[EqSet]; reflexivity
             | |- Subset (filter _ _) _ => apply SubsetFilter1
             | |- _ => progress (simplify_Subset || auto)
             end.
        all: by (apply internal_Label_dec_bl || apply Perm.internal_t_dec_bl).
      Qed.

      Lemma LoadCapUpdate:
        forall mem mem' x y z caps,
        ReachableCap mem caps x ->
        LoadCap mem' x y z ->
        ValidMemCapUpdate mem caps mem' ->
        ReachableCap mem caps z.
      Proof.
        cbv [ValidMemCapUpdate].
        intros * hauth hload hupdate.
        inv hload. destruct_products.
        specialize (hupdate capa). rewrite loadFromAuth0r in *.
        destruct (CapOrBytes_eq_dec (readCap bytesToCapUnsafe mem0 capa) (inl y) ) as [Heq | Hneq].
        - eapply StepLoadCap with (y := y); eauto.
          constructor; eauto.
        - propositional.
          specialize hupdate with (1 := Hneq) (2 := eq_refl).
          destruct_products.
          eapply StepRestrict; eauto.
          eapply AttenuateRestrict; eauto.
      Qed.

      Lemma LoadCapUpdate'':
        forall mem mem' x y z caps,
        ReachableCap mem caps x ->
        LoadCap mem' x y z ->
        ValidMemUpdate mem caps mem' ->
        ReachableCap mem caps z.
      Proof.
        cbv[ValidMemUpdate].
        intros; eapply LoadCapUpdate; destruct_products; eauto.
      Qed.

      Lemma ReachableCap_ValidUpdate:
        forall mem mem' caps caps' c,
          ReachableCap mem' caps' c ->
          ValidMemUpdate mem caps mem' ->
          ReachableCaps mem caps caps' ->
          ReachableCap mem caps c.
      Proof.
        cbv [ReachableCaps].
        induction 1; intros * hupdate hcaps'; propositional.
        - auto.
        - eapply StepRestrict; eauto.
        - eapply LoadCapUpdate''; eauto.
        - eapply StepSeal with (3 := xyz); auto.
        - eapply StepUnseal with (3 := xyz); auto.
      Qed.

      Lemma ReachableCaps_ValidUpdate:
        forall mem mem' caps caps' cs,
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableCaps mem' caps' cs ->
        ReachableCaps mem caps cs.
      Proof.
        cbv[ReachableCaps].
        intros * hupdate hcaps hcaps' * hcaps0.
        pose proof (hcaps' _ hcaps0) as hc'.
        eapply ReachableCap_ValidUpdate; eauto.
      Qed.
      Definition ReachableReadAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
        exists p cs cbs ,
          ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Load p).
      Definition ReachableWriteAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
        exists p cs cbs ,
          ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Store p).

      Definition WriteReadDisjoint (mem: FullMemory) (c1 c2: list Cap) : Prop :=
        forall a,
          ReachableWriteAddr mem c1 a ->
          ReachableReadAddr mem c2 a ->
          False.
      Lemma WriteReadDisjointImpliesFalse:
        forall mem caps caps' x y a,
        WriteReadDisjoint mem caps caps' ->
        ReachableCap mem caps x ->
        ReachableCap mem caps' y ->
        capSealed x = None ->
        capSealed y = None ->
        In Perm.Store (capPerms x) ->
        In Perm.Load (capPerms y) ->
        In a (capAddrs x) ->
        In a (capAddrs y) ->
        False.
      Proof.
        cbv [WriteReadDisjoint ReachableWriteAddr ReachableReadAddr].
        intros * hdisjoint hx hy hsealx hsealy hstorex hloady hax hay.
        specialize (hdisjoint a).
        apply hdisjoint;
          repeat eexists; eauto;
          unfold Subset; cbn; intuition; subst; auto.
      Qed.

      Lemma ISA_CAPSIZE_BYTES_NONZERO:
        ISA_CAPSIZE_BYTES > 0.
      Proof.
        unfold ISA_CAPSIZE_BYTES.
        pose proof (PeanoNat.Nat.pow_nonzero 2 ISA_LG_CAPSIZE_BYTES). lia.
      Qed.

      Lemma LoadCapUpdateDisjointUnchanged:
        forall mem caps mem' x y z t,
          ReachableCap mem' t x ->
          LoadCap mem' x y z ->
          ValidMemCapUpdate mem caps mem' ->
          WriteReadDisjoint mem caps t ->
          ReachableCap mem t x ->
          LoadCap mem x y z.
      Proof.
        intros * hauth' hload hupdate hdisjoint hauth.
        inv hload. destruct_products. constructor; eauto.
        eexists; split; eauto.
        unfold ValidMemCapUpdate in *.
        specialize hupdate with (capa := capa) (stDataCap := y) (2 := loadFromAuth0r).
        destruct (CapOrBytes_eq_dec (readCap bytesToCapUnsafe mem0 capa) (inl y) ) as [Heq | Hneq]; auto.
        exfalso.
        rewrite loadFromAuth0r in *. propositional.
        destruct_products.
        consider StPermForCap. consider StPermForAddr. destruct_products.
        pose proof ISA_CAPSIZE_BYTES_NONZERO.
        destruct ISA_CAPSIZE_BYTES eqn:?; [lia | ].
        eapply WriteReadDisjointImpliesFalse with (x := stAddrCap) (y := x) (a := (fromCapAddr capa));eauto.
        all: match goal with
        | H: Subset _ ?x |- In _ ?x =>
            eapply H
        end; constructor; auto.
      Qed.

      Lemma ReachableCapDisjointUnchanged':
        forall mem caps mem' t c,
          ReachableCap mem' t c ->
          ValidMemCapUpdate mem caps mem' ->
          WriteReadDisjoint mem caps t ->
          ReachableCap mem t c.
      Proof.
        induction 1; intros * hupdate hdisjoint; propositional.
        - apply Refl; auto.
        - eapply StepRestrict; eauto.
        - eapply StepLoadCap; eauto.
          eapply LoadCapUpdateDisjointUnchanged with (mem' := mem') (mem := mem0); eauto.
        - eapply StepSeal with (3:= xyz); auto.
        - eapply StepUnseal with (3:= xyz); auto.
      Qed.
      Definition ReachableRWAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
        ReachableReadAddr mem caps a \/
        ReachableWriteAddr mem caps a.

      Definition RWAddressesDisjoint (mem: FullMemory) (c1 c2: list Cap) : Prop :=
        forall a,
          ReachableRWAddr mem c1 a ->
          ReachableRWAddr mem c2 a ->
          False.
      Definition ReachableCapSubset (m_init m_cur: FullMemory) (caps_init caps_cur: list Cap) : Prop :=
        forall caps,
          ReachableCaps m_cur caps_cur caps ->
          ReachableCaps m_init caps_init caps.
      Lemma ReachableCapSubsetImpliesReachableCap:
        forall mem mem1 cs cs1 c,
        ReachableCapSubset mem mem1 cs cs1 ->
        ReachableCap mem1 cs1 c ->
        ReachableCap mem cs c.
      Proof.
        cbv[ReachableCapSubset].
        intros. eapply H with (caps := [c]); cbv[ReachableCaps]; intuition eauto.
        - repeat destruct H1; subst; auto.
        - constructor; auto.
      Qed.

      Lemma ReachableCapSubsetDisjointUnchanged':
        forall mem0 mem mem' t0 t caps,
        ReachableCapSubset mem0 mem t0 t ->
        ValidMemTagRemoval mem caps mem' ->
        ValidMemCapUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableCapSubset mem0 mem' t0 t.
      Proof.
        cbv[ReachableCapSubset ReachableCaps].
        intros * hinit htag hupdate hdisjoint.
        intros * hcapsIn * hin.
        eapply ReachableCapSubsetImpliesReachableCap; eauto.
        specialize hcapsIn with (1 := hin).
        eapply ReachableCapDisjointUnchanged'; eauto.
      Qed.
      Lemma ReachableCapSubsetUpdateDisjointUnchanged:
        forall mem0 mem mem' t0 t caps,
        ReachableCapSubset mem0 mem t0 t ->
        ValidMemUpdate mem caps mem' ->
        WriteReadDisjoint mem caps t ->
        ReachableCapSubset mem0 mem' t0 t.
      Proof.
        cbv[ValidMemUpdate].
        intros; destruct_products; by (eapply ReachableCapSubsetDisjointUnchanged').
      Qed.
      Lemma RWDisjointImpliesWriteReadDisjoint:
        forall m xi xj,
        RWAddressesDisjoint m xi xj ->
        WriteReadDisjoint m xi xj.
      Proof.
        cbv [RWAddressesDisjoint WriteReadDisjoint ReachableRWAddr].
        intros. eapply H; eauto.
      Qed.


    End Helpers.
    Definition ExportEntry : Type.
    Proof using ISA Byte Key.
    Admitted.

    Definition ImportEntry : Type.
    Proof using ISA Byte Key.
    Admitted.

    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> Inst bytesToCapUnsafe}.
    Context {pccNotInBounds : EXNInfo}.
    Notation Machine := (@Machine Byte Key).
    Notation AddrOffset := nat (only parsing).
    Notation MachineStep := (MachineStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).
    Notation PCC := Cap (only parsing).
    Notation Thread := (@Thread Byte Key).
    Notation Trace := (@Trace Byte Key).
    Notation State := (Machine * Trace)%type.
    Notation Event := (@Event Byte Key).
    Notation SameThreadStep := (SameThreadStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).
    Notation StPermForCap := (StPermForCap bytesToCapUnsafe).
    Notation StPermForAddr := (StPermForAddr bytesToCapUnsafe).
    Notation RegisterFile := (@RegisterFile Byte Key).
    Notation ThreadStep := (ThreadStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).

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
    Record ThreadInv (t: InitialThreadMetadata) (t: Thread) : Prop :=
    { Inv_validRf : ValidRf t.(thread_userState).(thread_rf)
    }.

    Record GlobalInvariant (config: Config) (m: Machine) : Prop :=
    { Inv_curThread: m.(machine_curThreadId) < length m.(machine_threads)
    ; Inv_threads : Forall2 ThreadInv config.(configThreads) m.(machine_threads)
    }.

    (* WIP *)
    Record ValidInitialState (config: Config) (m: Machine) : Prop :=
      { ValidInit_memory: m.(machine_memory) = config.(configInitMemory)
      ; ValidInit_invariant: GlobalInvariant config m
      }.

    Hint Resolve Inv_curThread : invariants.
    Hint Resolve Inv_validRf: invariants.
    Section Proofs.
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

      Lemma SameThreadStep_lengthThreads:
        forall m1 m2 ev,
          machine_curThreadId m1 < length (machine_threads m1) ->
          SameThreadStep m1 m2 ev ->
          length (machine_threads m1) = length (machine_threads m2).
      Proof.
        intros * hlen hstep.
        inv hstep. destruct_products.
        eapply listUpdate_length; eauto.
        rewrite<-threadIdEq. eauto.
      Qed.

      Lemma SameThreadStep_curId:
        forall m1 m2 ev,
          machine_curThreadId m1 < length (machine_threads m1) ->
          SameThreadStep m1 m2 ev ->
          machine_curThreadId m2 < length (machine_threads m2).
      Proof.
        intros * hlen hstep.
        pose proof (SameThreadStep_lengthThreads _ _ _ hlen hstep) as hlen'.
        inv hstep; destruct_products.
        rewrite threadIdEq. lia.
      Qed.
      Lemma StPermForAddrSubset:
        forall mem caps caps' capa a size ,
          StPermForAddr mem caps capa a size ->
          Subset caps caps' ->
          StPermForAddr mem caps' capa a size.
      Proof.
        cbv[StPermForAddr].
        intros. destruct_products.
        split_and!; auto.
        eapply ReachableCapIncrease; eauto.
      Qed.
      Lemma StPermForCapSubset:
        forall mem caps caps' addr capa,
          StPermForCap mem caps addr capa ->
          Subset caps caps' ->
          StPermForCap mem caps' addr capa.
      Proof.
        cbv[StPermForCap].
        intros. destruct_products.
        eapply StPermForAddrSubset; eauto.
      Qed.
      Lemma ValidMemTagRemovalSubset:
        forall mem mem' caps caps',
          ValidMemTagRemoval mem caps mem' ->
          Subset caps caps' ->
          ValidMemTagRemoval mem caps' mem'.
      Proof.
        cbv[ValidMemTagRemoval].
        intros. specialize H with (1 := H1) (2 := H2). destruct_products.
        eexists. eapply StPermForCapSubset; eauto.
      Qed.
      Lemma ValidMemDataUpdateSubset:
        forall mem mem' caps caps',
          ValidMemDataUpdate mem caps mem' ->
          Subset caps caps' ->
          ValidMemDataUpdate mem caps' mem'.
      Proof.
        cbv[ValidMemDataUpdate].
        intros. specialize H with (1 := H1). destruct_products.
        eexists. eapply StPermForAddrSubset; eauto.
      Qed.
      Lemma ValidMemCapUpdateSubset:
        forall mem mem' caps caps',
          ValidMemCapUpdate mem caps mem' ->
          Subset caps caps' ->
          ValidMemCapUpdate mem caps' mem'.
      Proof.
        cbv[ValidMemCapUpdate].
        intros * hupdate subset * hcap htag.
        specialize hupdate with (1 := hcap) (2 := htag).
        destruct_products. split; eauto.
        - eapply ReachableCapIncrease; eauto.
        - eexists; split; eauto.
          eapply StPermForCapSubset; eauto.
      Qed.
      Lemma ValidMemUpdateSubset:
        forall mem mem' caps caps',
          ValidMemUpdate mem caps mem' ->
          Subset caps caps' ->
          ValidMemUpdate mem caps' mem'.
      Proof.
        cbv[ValidMemUpdate].
        intros * hsubset hupdate. destruct_products.
        split_and!; by (eapply ValidMemCapUpdateSubset || eapply ValidMemTagRemovalSubset || eapply ValidMemDataUpdateSubset).
      Qed.
      Lemma readCapImpliesTag:
        forall mem capa cap,
          readCap bytesToCapUnsafe mem capa = inl cap ->
          readTag mem capa = true.
      Proof.
        cbv[readCap readTag readMemTagCap bytesToCap].
        intros *. case_match; try congruence.
        rewrite andb_true_iff in *. destruct_products; auto.
      Qed.

      Lemma generalInstOkCommon:
        forall userSt mem sysSt istatus userSt' mem' sysSt' istatus' generalInst,
          WfGeneralInst bytesToCapUnsafe generalInst ->
          generalInst (userSt, mem) (sysSt, istatus) = Ok (userSt', mem', (sysSt', istatus')) ->
          ValidRf (thread_rf userSt) ->
          let caps := (capsOfUserTS userSt ++ capsOfSystemTS sysSt) in
          let caps' := (capsOfUserTS userSt' ++ capsOfSystemTS sysSt') in
          ValidMemUpdate mem caps mem' /\
            ReachableCaps mem caps caps' /\
            In Perm.Exec (thread_pcc userSt).(capPerms) /\
            In Perm.Exec (thread_pcc userSt').(capPerms) /\
            ValidRf (thread_rf userSt').
      Proof.
        cbv[WfGeneralInst WfSystemInst WfNormalInst].
        intros * [hwf_user hwf_sys] hinst hpre.
        destruct (in_dec Perm.t_eq_dec Perm.System (capPerms (thread_pcc userSt)));
          [ clear hwf_user; rename i into hmode| clear hwf_sys].
        - specialize hwf_sys with (1 := hmode) (2 := hpre) (mem := mem0)
                                  (mepcc := thread_mepcc sysSt) (exnInfo := thread_exceptionInfo sysSt)
                                  (ts := thread_trustedStack sysSt) (ints := istatus).
          setoid_rewrite hinst in hwf_sys. destruct_products. auto.
        - cbv[capsOfUserTS capsOfSystemTS]. destruct_products.
          specialize hwf_userl with (1 := hpre) (pcc := thread_pcc userSt) (mem := mem0).
          specialize hwf_userr with (1 := n) (rf := thread_rf userSt) (mem := mem0) (sysCtx := (sysSt, istatus)).
          destruct userSt. cbv [thread_rf thread_pcc] in *.
          rewrite hinst in hwf_userr.
          simplify_Result. destruct_products; simplify_eq.
          split_and!; auto.
          + eapply ValidMemUpdateSubset; eauto. simplify_Subset.
          + apply ReachableCaps_app. auto.
      Qed.

      Lemma ValidRfUpdate:
        forall rf rf' v idx,
          @ValidRf ISA Byte Key rf ->
          (forall n, n <> idx -> nth_error rf' n = nth_error rf n) ->
          idx < length rf ->
          nth_error rf' idx = Some v ->
          ValidRf rf'.
      Proof.
        cbv[ValidRf]. intros * hrf hsame hlen hsome.
        rewrite<-hrf. symmetry.
        eapply listUpdate_length; eauto.
      Qed.
      Lemma callSentryOkCommon:
        forall callSentryInst srcReg optLink userSt mem istatus pcc' rf' istatus',
          WfCallSentryInst bytesToCapUnsafe callSentryInst srcReg optLink ->
          callSentryInst (userSt, mem) istatus = Ok (pcc', rf', istatus') ->
          ValidRf (thread_rf userSt) ->
          ValidRf rf' /\
          In Perm.Exec pcc'.(capPerms).
      Proof.
        cbv[WfCallSentryInst].
        intros * hwf hinst hpre.
        specialize hwf with (1 := hpre) (pcc := thread_pcc userSt) (ints := istatus) (mem := mem0).
        setoid_rewrite hinst in hwf.
        destruct_products. simplify_eq.
        split; auto.
        destruct optLink eqn:?; simplify_eq; auto.
        destruct_products.
        eapply ValidRfUpdate with (idx := n) (1 := hpre); eauto.
        rewrite hpre. auto.
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
                | H: WfGeneralInst _ ?generalInst,
                  H1: ?generalInst _ _ = Ok _ |- ValidRf _ =>
                    eapply generalInstOkCommon with (1 := H) (2 := H1); by (eauto with invariants)
                | H: WfCallSentryInst _ ?callSentryInst _ _ ,
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

  End __.
  Hint Resolve Inv_curThread : invariants.
End Configuration.
(* From a valid initial state where threads are in disjoint compartments, for
   any sequence of same-domain (Ev_General) steps, the reachable caps in each
   thread do not increase.
 *)
Module ThreadIsolatedMonotonicity.
  Import ListNotations.
  Import Configuration.
  Import Separation.
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
    Notation ReachableAddr := (@ReachableAddr ISA Byte Key bytesToCapUnsafe).
    Notation Trace := (@Trace Byte Key).
    Notation State := (Machine * Trace)%type.
    Notation Event := (@Event Byte Key).
    Notation Config := (@Config ISA Byte Key).
    Notation SameThreadStep := (SameThreadStep bytesToCapUnsafe fetchAddrs decode pccNotInBounds).
    Notation ValidMemUpdate := (@ValidMemUpdate ISA Byte Key bytesToCapUnsafe).
    Notation ReachableCap := (@ReachableCap ISA Byte Key bytesToCapUnsafe).
    Notation ValidMemCapUpdate := (ValidMemCapUpdate bytesToCapUnsafe).
    Notation ValidMemTagRemoval := (ValidMemTagRemoval bytesToCapUnsafe).
    Notation ValidMemDataUpdate := (ValidMemDataUpdate bytesToCapUnsafe).
    Notation StPermForCap := (StPermForCap bytesToCapUnsafe).
    Notation StPermForAddr := (StPermForAddr bytesToCapUnsafe).
    Notation LoadCap := (LoadCap bytesToCapUnsafe).
    Notation CapOrBytes := (@CapOrBytes Byte Key).
    Notation ReachableCapSubset := (@ReachableCapSubset ISA Byte Key bytesToCapUnsafe).
    Notation RWAddressesDisjoint := (@RWAddressesDisjoint ISA Byte Key bytesToCapUnsafe).
    Notation WriteReadDisjoint := (@WriteReadDisjoint ISA Byte Key bytesToCapUnsafe).

    (* TODO: decidable equality *)
    Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).
    Context {Cap_eqb: Cap -> Cap -> bool}.
    Context {Cap_eq_dec: EqDecider Cap_eqb}.
    Context {CapOrBytes_eqb: CapOrBytes -> CapOrBytes -> bool}.
    Context {CapOrBytes_eq_dec: EqDecider CapOrBytes_eqb}.

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
    (* TODO: write in terms of restrictions on the initial configuration. *)
    Definition ValidInitialMachine (config: Config) (st: Machine) : Prop :=
      ValidInitialState config st /\
      IsolatedThreads st.
    Section WithConfig.
      Variable config: Config.
      Variable initialMachine: Machine.
      Variable pfValidInitialMachine: ValidInitialMachine config initialMachine.
      (* A thread's caps are a subset of caps reachable from initial state. *)
      Definition PThreadIsolatedMonotonicity (st: State) : Prop :=
        let '(machine, tr) := st in
        SameDomainTrace tr ->
        Forall2 (ThreadReachableCapSubset initialMachine.(machine_memory) machine.(machine_memory))
                initialMachine.(machine_threads) machine.(machine_threads).
      Record Invariant' machine : Prop :=
        {
          Inv_Isolation: IsolatedThreads machine;
          Inv_Monotonicity:
           Forall2 (ThreadReachableCapSubset initialMachine.(machine_memory) machine.(machine_memory))
             initialMachine.(machine_threads) machine.(machine_threads)
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
          + cbv [SameDomainTrace ThreadReachableCapSubset ReachableCapSubset ValidInitialMachine].
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


      Lemma ReachableCapSubset_ValidUpdate:
        forall mem0 mem mem' caps0 caps caps',
        ReachableCapSubset mem0 mem caps0 caps ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableCapSubset mem0 mem' caps0 caps'.
      Proof.
        cbv[ReachableCapSubset].
        intros * hinit hmem hcaps.
        pose proof (hinit _ hcaps) as hcaps0'.
        intros * hcaps'.
        specialize ReachableCaps_ValidUpdate with (1 := CapOrBytes_eq_dec) (2 := hmem) (3 := hcaps) (4 := hcaps'); auto.
      Qed.

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

        (* assert (IsolatedThreads m') as hisolated'. *)
        (* { cbv [IsolatedThreads]. *)
        (*   admit. *)
        (* } *)
        constructor; auto.
        { admit. }
        apply Forall2_nth_error1; auto.
        - apply GlobalInvariant_length. auto.
        - intros * hx hy.
          destruct_with_eqn (Nat.eqb idx (m'.(machine_curThreadId))); simplify_nats; subst.
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
      Admitted.

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
        inv hstep; simplify_Forall; propositional.
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
  End __.
End ThreadIsolatedMonotonicity.

(* Other properties:
   - Isolation
   - Top-level invariant: capabilities accessible are those of compartment + caller args/callee rets
 *)


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
