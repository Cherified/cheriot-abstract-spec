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
