From Stdlib Require Import List.

Set Primitive Projections.

(* Represents basic permissions *)
Module Perm.
  Inductive t :=
  | Exec
  | System
  | Load
  (* Store is not needed as StRegions give a granular way to state this *)
  | Cap
  | Sealing
  | Unsealing.
End Perm.

(* Represents disjoint semantics regions of memory *)
Inductive Region :=
| Stack
| Global.

(* Represents Call and Return sentries *)
Inductive Sentry :=
| UnsealedJump
| CallEnableInterrupt
| CallDisableInterrupt
| CallInheritInterrupt
| RetEnableInterrupt
| RetDisableInterrupt.

Section Machine.
  Variable Value: Type.
  Variable Addr: Type.
  Variable Key: Type.

  Record Cap := {
      capThisRegion: Region; (* The provenant region from which this cap was derived (SL in CHERIoT) *)
      capSentry: Sentry;
      capSealed: option Key; (* Whether a cap is sealed, and the sealing key *)
      capPerms: list Perm.t;
      capStRegions: list Region; (* The regions where this cap can be stored (G and not G in CHERIoT) *)
      capSealingKeys: list Key; (* List of sealing keys owned by this cap *)
      capUnsealingKeys: list Key; (* List of unsealing keys owned by this cap *)
      capAddrs: list Addr; (* List of addresses representing this cap's bounds *)
      capKeepPerms: list Perm.t; (* Permissions to be the only ones kept when loading using this cap *)
      capKeepStRegions: list Region (* Regions-where-this-cap-can-be-stored to be the only ones kept
                                       when loading using this cap *)
    }.

  Variable Memory: Addr -> (Value * list Cap).

  Section CapStep.
    Variable y z: Cap.

    Record AlwaysEqs : Prop := {
        restrictThisRegionEq: z.(capThisRegion) = y.(capThisRegion);
        restrictSentryEq: z.(capSentry) = y.(capSentry) }.

    Record RestrictEqs : Prop := {
        restrictAlwaysEqs: AlwaysEqs;
        restrictSealedEq: z.(capSealed) = y.(capSealed) }.

    Record RestrictUnsealed : Prop := {
        restrictUnsealedEqs: RestrictEqs;
        restrictUnsealedPermsSubset: forall p, In p z.(capPerms) -> In p y.(capPerms);
        restrictUnsealedStRegionsSubset: forall r, In r z.(capStRegions) -> In r y.(capStRegions);
        restrictUnsealedSealingKeysSubset: forall k, In k z.(capSealingKeys) -> In k y.(capSealingKeys);
        restrictUnsealedUnsealingKeysSubset: forall k, In k z.(capUnsealingKeys) = In k y.(capUnsealingKeys);
        restrictUnsealedAddrsSubset: forall a, In a z.(capAddrs) -> In a y.(capAddrs);
        restrictUnsealedKeepPermsSubset: forall p, In p z.(capKeepPerms) -> In p y.(capKeepPerms);
        restrictUnsealedKeepStRegionsSubset: forall p, In p z.(capKeepStRegions) -> In p y.(capKeepStRegions) }.

    Record RestrictSealed : Prop := {
        restrictSealedEqs: RestrictEqs;
        restrictSealedPermsEq: z.(capPerms) = y.(capPerms);
        (* The following seems to be a quirk of CHERIoT,
           maybe make it equal in CHERIoT ISA if there's no use case for this behavio
           and merge with RestrictUnsealed?
           Here's a concrete example why this is bad:
             I have objects in Global and a set of pointers to these objects also in Global.
             I seal an element of that set (which points to an object) and send to a client.
             Client gets a Global sealed cap, makes it Stack and sends it back to me after finishing processing.
             I unseal it, but I lost my ability to store it back into that set in Global.
             Instead, I need to rederive the Global for the unsealed cap to be able to store into the Global set.
         *)
        restrictSealedStRegionsSubset: forall r, In r z.(capStRegions) -> In r y.(capStRegions);
        restrictSealedSealingKeysEq: z.(capSealingKeys) = y.(capSealingKeys);
        restrictSealedUnsealingKeysSubset: z.(capUnsealingKeys) = y.(capUnsealingKeys);
        restrictSealedAddrsEq: z.(capAddrs) = y.(capAddrs);
        restrictSealedKeepPermsSubset: z.(capKeepPerms) = y.(capKeepPerms);
        restrictSealedKeepStRegionsSubset: z.(capKeepStRegions) = y.(capKeepStRegions) }.

    Definition Restrict : Prop :=
      match y.(capSealed) with
      | None => RestrictUnsealed
      | Some k => RestrictSealed
      end.

    Variable x: Cap.
    (* When a cap y is loaded using a cap x, then the attentuation of x comes into play to create z *)

    Record NonRestrictEqs : Prop := {
        nonRestrictAlwaysEqs: AlwaysEqs;
        nonRestrictAuthUnsealed: x.(capSealed) = None;
        nonRestrictSealingKeysEq: z.(capSealingKeys) = y.(capSealingKeys);
        nonRestrictUnsealingKeysEq: z.(capUnsealingKeys) = y.(capUnsealingKeys);
        nonRestrictAddrsEq: z.(capAddrs) = y.(capAddrs) }.

    Record AttenuatePerms : Prop := {
        attenuatePerms: forall p, In p z.(capPerms) -> (In p x.(capKeepPerms) /\ In p y.(capPerms));
        attenuateKeepPerms: forall p, In p z.(capKeepPerms) ->
                                      (In p x.(capKeepPerms) /\ In p y.(capKeepPerms)) }.

    Record NonAttenuatePerms : Prop := {
        nonAttenuatePerms: z.(capPerms) = y.(capPerms);
        nonAttenuateKeepPerms: z.(capKeepPerms) = y.(capKeepPerms) }.

    Record LoadCap : Prop := {
        loadNonRestrictEqs: NonRestrictEqs;
        loadAuthPerm: In Perm.Load x.(capPerms) /\ In Perm.Cap x.(capPerms);
        loadFromAuth: exists a, In a x.(capAddrs) /\ In y (snd (Memory a));
        loadSealedEq: z.(capSealed) = y.(capSealed);
        loadAttenuatePerms: match y.(capSealed) with
                            | None => AttenuatePerms
                            | Some k => NonAttenuatePerms
                            end;
        (* This is also a quirk of CHERIoT as in the case of restricting caps.
           Ideally, no attenuation (implicit or explicit) must happen under a seal *)
        loadAttenuateStRegions: forall r, In r z.(capStRegions) ->
                                          (In r x.(capKeepStRegions) /\ In r y.(capStRegions));
        loadKeepStRegions: match y.(capSealed) with
                           | None => forall r, In r z.(capKeepStRegions) ->
                                               (In r x.(capKeepStRegions) /\ In r y.(capKeepStRegions))
                           | Some k => z.(capKeepStRegions) = y.(capKeepStRegions)
                           end}.

    Record SealUnsealEqs : Prop := {
        sealUnsealNonRestrictEqs: NonRestrictEqs;
        sealUnsealNonAttenuatePerms: NonAttenuatePerms;
        sealUnsealStRegionsEq: z.(capStRegions) = y.(capStRegions);
        sealUnsealKeepStRegionsEq: z.(capKeepStRegions) = y.(capKeepStRegions) }.

    (* Cap z is the sealed version of cap y using a key in x *)
    Record Seal : Prop := {
        sealOrigUnsealed: y.(capSealed) = None;
        sealNewSealed: exists k, In k x.(capSealingKeys) /\ z.(capSealed) = Some k }.

    Record Unseal : Prop := {
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
    | StepSeal x (xPf: ReachableCap x) y z (xyz: Seal x y z): ReachableCap z
    | StepUnseal x (xPf: ReachableCap x) y z (xyz: Unseal x y z): ReachableCap z.

    (* Transitively reachable addr listed with permissions and stRegions *)
    Inductive ReachableAddr: Addr -> list Perm.t -> list Region -> Prop :=
    | HasAddr c (cPf: ReachableCap c) a (ina: In a c.(capAddrs)) (notSealed: c.(capSealed) = None)
        perms (permsEq: perms = c.(capPerms)) stRegions (stRegionsEq: stRegions = c.(capStRegions))
      : ReachableAddr a perms stRegions.
  End Transitivity.
End Machine.

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
