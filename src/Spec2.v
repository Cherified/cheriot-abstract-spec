From Stdlib Require Import Vector List NArith Lia Zmod Bits .
Set Primitive Projections.
Require Import coqutil.Byte.

Notation "x <- f ; e" := (f (fun x => e)) (at level 20, right associativity).
Notation "' x <- f ; e" := (f (fun x => e)) (at level 20, x pattern, right associativity).


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
Section ListUtils.
  Import ListNotations.
  Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
    firstn i l ++ [e] ++ skipn (S i) l.

  Fixpoint listSumToInl [A B: Type] (l: list (A+B)) : list A :=
    match l with
    | nil => nil
    | x :: xs => match x with
                 | inl y => y :: listSumToInl xs
                 | _ => listSumToInl xs
                 end
    end.
End ListUtils.

Theorem seqInBounds n: forall b v,
    b <= v < b + n -> In v (seq b n).
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (PeanoNat.Nat.eq_dec b v); [auto|right].
    apply IHn.
    lia.
Qed.

Definition option_to_bool [A] (a: option A) : bool :=
  match a with
  | Some _ => true
  | _ => false
  end.

Module Perm.
  Inductive t :=
  | Exec
  | System
  | Load
  | Store
  | Cap
  | Sealing
  | Unsealing.
End Perm.

Class ISA_params := {
    ISA_NBYTES : N;
    ISA_NREGS : nat;
    ISA_instruction_size: list byte -> nat;
}.

Class ISA_params_ok (params: ISA_params) := {
    ISA_instruction_size_ok: forall bs, params.(ISA_instruction_size) bs <= List.length bs
}.


Section Machine.
  Context {Key Value: Type}.
  Context {ISA : ISA_params}.
  Section TypeDefs.
    Local Open Scope Z_scope.
    Definition XLEN : Z := (8 * (Z.of_N ISA_NBYTES)).
    Definition Addr := bits XLEN.
    Definition TAGLEN := (XLEN - 3).
    Definition Tag := bits TAGLEN.
  End TypeDefs.


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
  Notation Memory_data_t := (Addr -> byte).
  Notation Memory_tags_t := (Tag -> byte).

  Record Memory :=
  { Memory_data : Memory_data_t;
    Memory_tags : Memory_tags_t
  }.

  Inductive InterruptStatus :=
  | InterruptsEnabled
  | InterruptsDisabled.

  Notation PCC := Cap (only parsing).
  Notation MEPCC := Cap (only parsing). (* While MEPCC can become invalid architecturally,
                                           it shouldn't if the switcher is correct *)
  Notation CapOrValue := (Cap + Value)%type.
  Notation EXNInfo := Value (only parsing).

  Definition RegisterFile := Vector.t CapOrValue ISA_NREGS.

  Record TrustedStackFrame := {
      trustedStackFrame_CSP : Cap;
      trustedStackFrame_calleeExportTable : Cap;
      trustedStackFrame_errorCounter : N
      (* trustedStackFrame_compartmentIdx : nat; (* Actually a pointer to the compartment's export table *) *)
    }.

  (* Note that TrustedStack is a first class entity in our abstraction, and not yet another object in the Memory *)
  (* That is, it is accessed like how a PCC is accessed using a name *)
  (* In CHERIoT, Trusted stack is just another object in Memory accessible through a thread's MTDC *)
  (* This refinement will be done later *)
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
      machine_memory: Memory;
      machine_interruptStatus : InterruptStatus;
      machine_threads : list Thread;
      machine_curThreadId : nat;
  }.

  Section StateTransition.

    Class Linker_params := {
        switcher_exceptionEntryPCC : Cap
    }.
    Context {Linked: Linker_params}.

    Definition setMachineThread (m: Machine) (tid: nat): Machine :=
      {| machine_memory := m.(machine_memory);
         machine_interruptStatus := m.(machine_interruptStatus);
         machine_threads := m.(machine_threads);
         machine_curThreadId := tid
      |}.
    Definition SameThreadStep (m: Machine)
                              (update_fn: Thread -> Memory -> InterruptStatus ->
                                          (Thread -> Memory -> InterruptStatus -> Prop) -> Prop)
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

    Definition InSystemMode (t: Thread) : Prop :=
      In Perm.System t.(thread_userState).(thread_pcc).(capPerms).

    (* The following definitions are defined per thread (obvious, but re-iterating) *)
    Definition UserContext : Type := (UserThreadState * Memory).
    Definition SystemContext : Type := (SystemThreadState * InterruptStatus).

    Variable TODO_EXN_INFO: EXNInfo.

    Inductive Result {T: Type} :=
    | Ok (t: T)
    | Exception (exn: EXNInfo)
    | Fail (* Placeholder *).
    Arguments Result : clear implicits.

    Definition footprint (a: Addr) (n: nat) : list Addr :=
      List.map (fun i => Zmod.add a (bits.of_Z _ (Z.of_nat i))) (List.seq 0 n).

    Definition load_bytes (m: Memory_data_t) (a: Addr) (n: nat) : list byte :=
      List.map m (footprint a n).

    Definition ValidFetch (pcc: PCC) (addrs: list Addr) : Prop :=
      In Perm.Exec pcc.(capPerms) /\
      Subset addrs pcc.(capAddrs).

    (* Ignores tags?
     * Exception handling?
     *)
    Definition fetch (pcc: PCC) (mem: Memory_data_t) (post: Result (list byte) -> Prop) : Prop :=
      let bytes := load_bytes mem pcc.(capCursor) (N.to_nat ISA_NBYTES) in
      let isa_nbytes := ISA_instruction_size bytes in
      let addrs := footprint pcc.(capCursor) isa_nbytes in
      let bytes := load_bytes mem pcc.(capCursor) isa_nbytes in
      (ValidFetch pcc addrs -> post (Ok bytes)) /\
      (~ValidFetch pcc addrs -> post (Exception TODO_EXN_INFO)).

    Inductive MemSize :=
    | Byte
    | Half
    | Word
    | Double.

    Inductive type :=
    | Ty_CapOrValue
    | Ty_Value.

    Definition type_denote (t: type) :=
      match t with
      | Ty_CapOrValue => CapOrValue
      | Ty_Value => Value
      end.
    Require Import Stdlib.Strings.String.

    (* TODO: PERMS *)
    Inductive RestrictOps :=
    | ChangeCursor (fn: Value -> Value)
    | FilterPerms (fn: Perm.t -> bool)
    | FilterCapCanStore (fn: Label -> bool)
    | FilterSealingKeys (fn: Key -> bool)
    | FilterUnsealingKeys (fn: Key -> bool)
    | FilterAddrs (fn: Addr -> bool)
    | FilterCapKeepPerms (fn: Perm.t -> bool)
    | FilterCapKeepCanStore (fn: Label -> bool)
    | FilterCapKeepCanBeStored (fn: Label -> bool).

    Inductive expr : type -> Type :=
    | ValueUnop (fn: Value -> Value) (e1: expr Ty_CapOrValue) : expr Ty_CapOrValue
    | ValueBinop (fn: Value -> Value -> Value) (e1 e2: expr Ty_CapOrValue) : expr Ty_CapOrValue
    | ReadReg (idx: Fin.t ISA_NREGS) : expr Ty_CapOrValue
    | RestrictCap (restrict: list RestrictOps) (c: expr Ty_CapOrValue) : expr Ty_CapOrValue.

    Inductive cmd : Type :=
    | Done
    | WriteReg (idx: Fin.t ISA_NREGS) (value: expr Ty_CapOrValue).

    Inductive error_t : Prop :=
    | Err (s: string).

    Class semantics_parameters (T: Type) :=
      { err: error_t -> T;
        option_bind: forall {A}, option A -> error_t -> (A -> T) -> T
      }.
    Context {T: Type} {semantics_params : semantics_parameters T}.

    Fixpoint interp_expr (pcc: PCC) (regs: RegisterFile) (mem: Memory)
                         {tau: type}
                         (e: expr tau)
                         (post: type_denote tau -> T)
                         : T :=
      match e with
      | ValueUnop fn e1 =>
          ve1 <- interp_expr pcc regs mem e1;
          err (Err "TODO")
      | _ => err (Err "TODO")
      end.

    Definition interp_cmd (pcc: PCC) (regs: RegisterFile) (mem: Memory)
                          (c: cmd)
                          (post: Result (PCC * RegisterFile * Memory) -> T)
                          : T :=
      match c with
      | Done => post (Ok (pcc,regs,mem))
      | WriteReg idx value =>

      | _ =>  post Fail
      end.
(*     | ReadReg (auth: Fin.t ISA_NREGS) (cont: CapOrValue -> InstructionStep). *)

(*     | Unop ( *)

(*     | LoadData (auth: Fin.t ISA_NREGS) (a: Addr) (length: MemSize) *)
(*     | StoreData (auth: Fin.t ISA_NREGS) (a: Addr) (length: MemSize) *)
(*     | LoadCap (auth: Fin.t ISA_NREGS) (a: Addr) (dst: Fin.t ISA_NREGS) *)
(*     | StoreCap (auth: Fin.t ISA_NREGS) (a: Addr) (src: Fin.t ISA_NREGS) *)
(*     | RestrictCap (src: Fin.t ISA_NREGS) (dst: Fin.t ISA_NREGS) *)
(*     | SealCap (auth: Fin.t ISA_NREGS) (src: Fin.t ISA_NREGS) (dst: Fin.t ISA_NREGS) *)
(*     | UnsealCap (auth: Fin.t ISA_NREGS)(src: Fin.t ISA_NREGS) (dst: Fin.t ISA_NREGS) *)
(*     | RaiseException *)
(*     | InvokeCapability (r: Fin.t ISA_NREGS) (r': Fin.t ISA_NREGS). *)

(* Definition unop := *)

    Definition user_step_fn (instr: list byte) (userCtx: UserContext) (post: Result UserContext -> Prop) : Prop.
    Admitted.

    Definition UserStep (ctx : UserContext) (post: Result UserContext -> Prop) : Prop :=
      let '(threadSt, mem) := ctx in
      res <- fetch threadSt.(thread_pcc) mem.(Memory_data);
      match res with
      | Ok instr => user_step_fn instr ctx post
      | Exception exn => post (Exception exn)
      end.

    Inductive Step1 : Thread -> Memory -> InterruptStatus ->
                      (Thread -> Memory -> InterruptStatus -> Prop) -> Prop :=
    | Step_UserOk :
      forall t mem istatus mid post,
      ~ InSystemMode t ->
      UserStep (t.(thread_userState), mem) mid ->
      (forall userSt' mem', mid (Ok (userSt', mem')) ->
                       post {| thread_userState := userSt';
                               thread_systemState := t.(thread_systemState)
                            |} mem' istatus) ->
      Step1 t mem istatus post
    | Step_UserExn :
      forall t mem istatus mid post,
      ~ InSystemMode t ->
      UserStep (t.(thread_userState), mem) mid ->
      (forall exnInfo, mid (Exception exnInfo) ->
                  post {| thread_userState := {| thread_pcc := switcher_exceptionEntryPCC;
                                                 thread_rf := t.(thread_userState).(thread_rf)
                                              |};
                          thread_systemState := {| thread_mepcc := t.(thread_userState).(thread_pcc);
                                                   thread_exceptionInfo := exnInfo;
                                                   thread_trustedStack := t.(thread_systemState).(thread_trustedStack)
                                                |}
                        |} mem InterruptsDisabled) ->
      Step1 t mem istatus post
    | Step_System:
      forall t mem istatus post,
      InSystemMode t ->
      False -> (* TODO *)
      Step1 t mem istatus post.

    Inductive Step : Machine -> (Machine -> Prop) -> Prop :=
    | Step_SwitchThreads:
      forall m tid' post,
        m.(machine_interruptStatus) = InterruptsEnabled ->
        tid' < List.length m.(machine_threads) ->
        post (setMachineThread m tid') ->
        Step m post
    | Step_SameThread :
      forall m post,
        SameThreadStep m Step1 post ->
        Step m post.

  End StateTransition.

End Machine.

Section Properties.

End Properties.

Module CHERIoTValidation.
  From Stdlib Require Import ZArith.
  Import ListNotations.
  Local Open Scope N_scope.

  Arguments Cap : clear implicits.

  Inductive CompressedPerm :=
  | MemCapRW (GL: bool) (SL: bool) (LM: bool) (LG: bool) (* Implicit: LD, MC, SD *)
  | MemCapRO (GL: bool) (LM: bool) (LG: bool) (* Implicit: LD, MC *)
  | MemCapWO (GL: bool) (* Implicit: SD, MC *)
  | MemDataOnly (GL: bool) (LD: bool) (SD: bool) (* Implicit: None *)
  | Executable (GL: bool) (SR: bool) (LM: bool) (LG: bool) (* Implicit: EX, LD, MC *)
  | Sealing (GL: bool) (U0: bool) (SE: bool) (US: bool) (* Implicit: None *).

  Instance CHERIOT_params : ISA_params :=
    {| ISA_NBYTES := 4;
       ISA_NREGS := 16;
       ISA_instruction_size := fun x => List.length x; (* PLACEHOLDER *)
    |}.

  Record cheriot_cap :=
  { reserved: bool;
    permissions: CompressedPerm;
    otype: N; (* < 8 *)
    base: Addr;
    length: Addr;
    addr: Addr;
    addrInBounds: (Zmod.unsigned base <= Zmod.unsigned addr < Zmod.unsigned base + Zmod.unsigned length)%Z
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
  Definition mk_abstract_cap (c: cheriot_cap) : Cap N CHERIOT_params :=
    let d := decompress_perm c.(permissions) in
    {|capSealed := if d.(EX)
                   then match c.(otype) with
                        | 0 => None
                        | 1 => Some (inl CallInheritInterrupt)
                        | 2 => Some (inl CallDisableInterrupt)
                        | 3 => Some (inl CallEnableInterrupt)
                        | 4 => Some (inl RetDisableInterrupt)
                        | 5 => Some (inl RetEnableInterrupt)
                        | (* 6 & 7 *) _ => None (* TODO! capSentry ⊆ capSealed *)
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
      capSealingKeys := [Z.to_N (Zmod.unsigned c.(addr))];
      capUnsealingKeys := [Z.to_N (Zmod.unsigned c.(addr))];
      capAddrs := map (fun v => bits.of_Z _ (Z.of_nat v))
                    (seq (Z.to_nat (Zmod.unsigned c.(base))) (Z.to_nat (Zmod.unsigned c.(length))));
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
      capCursor := c.(addr) |}.

    Definition x0 : Fin.t 16. apply (@Fin.of_nat_lt 0 16). repeat constructor. Defined.
    Definition x1 : Fin.t 16. apply (@Fin.of_nat_lt 1 16). repeat constructor. Defined.
    Definition x2 : Fin.t 16. apply (@Fin.of_nat_lt 2 16). repeat constructor. Defined.
    Definition x3 : Fin.t 16. apply (@Fin.of_nat_lt 3 16). repeat constructor. Defined.
    Definition x4 : Fin.t 16. apply (@Fin.of_nat_lt 4 16). repeat constructor. Defined.

    Notation reg_t := (Fin.t ISA_NREGS).

    Definition ADDI (dst src1: reg_t) (imm: Z) : @cmd N Z CHERIOT_params :=
      WriteReg dst (ValueUnop (Z.add imm) (ReadReg src1)).

    (* Definition LW (dst src1: reg_t) (imm: Z) : @cmd N Z CHERIOT_params := *)
    (*   WriteReg dst (ValueBinop Z.add (ReadReg src1)). *)


End CHERIoTValidation.
