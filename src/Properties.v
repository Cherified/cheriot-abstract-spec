From Stdlib Require Import List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Spec Utils Tactics.

Create HintDb invariants.
Import ListNotations.

Set Nested Proofs Allowed.

Module Configuration.
  Import Separation.

  Section __.
    Context [ISA: ISA_params].
    Context {Byte Key: Type}.
    Context {capEncodeDecode: @CapEncodeDecode Byte Key}.
    Notation Cap := (@Cap Key).
    Notation CapOrBytes := (@CapOrBytes Byte Key).
    Notation FullMemory := (@FullMemory Byte).
    Section Helpers.
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
        specialize (hupdate capa). rewrite loadFromAuthr in *.
        destruct (CapOrBytes_eq_dec (readCap mem capa) (inl y) ) as [Heq | Hneq].
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
      Lemma ReachableAddr_ValidUpdate:
        forall mem mem' caps caps' a sz p cs cbs,
          ReachableAddr mem' caps' a sz p cs cbs ->
          ValidMemUpdate mem caps mem' ->
          ReachableCaps mem caps caps' ->
          ReachableAddr mem caps a sz p cs cbs.
      Proof.
        intros. inv H. constructor; eauto. eapply ReachableCap_ValidUpdate; eauto.
      Qed.
      Definition ReachableReadAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
        exists p cs cbs ,
          ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Load p).
      Definition ReachableWriteAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
        exists p cs cbs ,
          ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Store p).
      Definition ReachableRWAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
        ReachableReadAddr mem caps a \/
        ReachableWriteAddr mem caps a.

      Lemma ReachableReadAddr_ValidUpdate:
        forall mem mem' caps caps' a,
          ReachableReadAddr mem' caps' a ->
          ValidMemUpdate mem caps mem' ->
          ReachableCaps mem caps caps' ->
          ReachableReadAddr mem caps a .
      Proof.
        cbv[ReachableReadAddr]. intros; destruct_products.
        do 3 eexists; split; eauto. by (eapply ReachableAddr_ValidUpdate).
      Qed.
      Lemma ReachableWriteAddr_ValidUpdate:
        forall mem mem' caps caps' a,
          ReachableWriteAddr mem' caps' a ->
          ValidMemUpdate mem caps mem' ->
          ReachableCaps mem caps caps' ->
          ReachableWriteAddr mem caps a .
      Proof.
        cbv[ReachableWriteAddr]. intros; destruct_products.
        do 3 eexists; split; eauto. by (eapply ReachableAddr_ValidUpdate).
      Qed.
      Lemma ReachableRWAddr_ValidUpdate:
        forall mem mem' caps caps' a,
          ReachableRWAddr mem' caps' a ->
          ValidMemUpdate mem caps mem' ->
          ReachableCaps mem caps caps' ->
          ReachableRWAddr mem caps a .
      Proof.
        cbv[ReachableRWAddr]. intros; destruct_products.
        destruct H; [ left; by (eapply ReachableReadAddr_ValidUpdate) | right; by (eapply ReachableWriteAddr_ValidUpdate) ].
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
        specialize hupdate with (capa := capa) (stDataCap := y) (2 := loadFromAuthr).
        destruct (CapOrBytes_eq_dec (readCap mem capa) (inl y) ) as [Heq | Hneq]; auto.
        exfalso.
        rewrite loadFromAuthr in *. propositional.
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
          eapply LoadCapUpdateDisjointUnchanged with (mem' := mem') (mem := mem); eauto.
        - eapply StepSeal with (3:= xyz); auto.
        - eapply StepUnseal with (3:= xyz); auto.
      Qed.

      Lemma ReachableAddrDisjointUnchanged:
        forall mem caps mem' t a sz p cs cbs,
          ReachableAddr mem' t a sz p cs cbs ->
          ValidMemCapUpdate mem caps mem' ->
          WriteReadDisjoint mem caps t ->
          ReachableAddr mem t a sz p cs cbs.
      Proof.
        intros * haddr hupdate hdisjoint.
        inv haddr. constructor; auto.
        eapply ReachableCapDisjointUnchanged'; eauto.
      Qed.

      Lemma ReachableReadAddrDisjointUnchanged:
        forall mem caps mem' t a,
          ReachableReadAddr mem' t a  ->
          ValidMemCapUpdate mem caps mem' ->
          WriteReadDisjoint mem caps t ->
          ReachableReadAddr mem t a.
      Proof.
        cbv[ReachableReadAddr].
        intros. destruct_products. do 3 eexists; split; eauto.
        eapply ReachableAddrDisjointUnchanged; eauto.
      Qed.

      Lemma ReachableWriteAddrDisjointUnchanged:
        forall mem caps mem' t a,
          ReachableWriteAddr mem' t a  ->
          ValidMemCapUpdate mem caps mem' ->
          WriteReadDisjoint mem caps t ->
          ReachableWriteAddr mem t a.
      Proof.
        cbv[ReachableWriteAddr].
        intros. destruct_products. do 3 eexists; split; eauto.
        eapply ReachableAddrDisjointUnchanged; eauto.
      Qed.

      Lemma ReachableRWAddrDisjointUnchanged:
        forall mem caps mem' t a,
          ReachableRWAddr mem' t a  ->
          ValidMemCapUpdate mem caps mem' ->
          WriteReadDisjoint mem caps t ->
          ReachableRWAddr mem t a.
      Proof.
        cbv[ReachableRWAddr].
        intros * haddr hupdate hdisjoint.
        destruct haddr.
        - left. eapply ReachableReadAddrDisjointUnchanged; eauto.
        - right. eapply ReachableWriteAddrDisjointUnchanged; eauto.
      Qed.

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

    Definition WFCompartment (compartment: Compartment) := True.

    (* Record WFCompartment (compartment: Compartment) := { *)
        (* WFCompartment_addrs: Disjoint compartment.(compartmentReadOnly) compartment.(compartmentGlobals); *)
    (* }. *)

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
          readCap mem capa = inl cap ->
          readTag mem capa = true.
      Proof.
        cbv[readCap readTag readMemTagCap bytesToCap].
        intros *. case_match; try congruence.
        rewrite andb_true_iff in *. destruct_products; auto.
      Qed.

      Lemma generalInstOkCommon:
        forall userSt mem sysSt istatus userSt' mem' sysSt' istatus' generalInst,
          WfGeneralInst generalInst ->
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
        - specialize hwf_sys with (1 := hmode) (2 := hpre) (mem := mem)
                                  (mepcc := thread_mepcc sysSt) (exnInfo := thread_exceptionInfo sysSt)
                                  (ts := thread_trustedStack sysSt) (ints := istatus).
          setoid_rewrite hinst in hwf_sys. destruct_products. auto.
        - cbv[capsOfUserTS capsOfSystemTS]. destruct_products.
          specialize hwf_userl with (1 := hpre) (pcc := thread_pcc userSt) (mem := mem).
          specialize hwf_userr with (1 := n) (rf := thread_rf userSt) (mem := mem) (sysCtx := (sysSt, istatus)).
          destruct userSt. cbv [Spec.thread_rf Spec.thread_pcc] in *.
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
          WfCallSentryInst callSentryInst srcReg optLink ->
          callSentryInst (userSt, mem) istatus = Ok (pcc', rf', istatus') ->
          ValidRf (thread_rf userSt) ->
          ValidRf rf' /\
          In Perm.Exec pcc'.(capPerms).
      Proof.
        cbv[WfCallSentryInst].
        intros * hwf hinst hpre.
        specialize hwf with (1 := hpre) (pcc := thread_pcc userSt) (ints := istatus) (mem := mem).
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
    Notation Config := (@Config ISA Byte Key).
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
        specialize ReachableCaps_ValidUpdate with (1 := hmem) (2 := hcaps) (3 := hcaps'); auto.
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
Lemma RWAddressDisjointUpdate_symmetry:
  forall mem xi xj,
  RWAddressesDisjoint mem xi xj <->
  RWAddressesDisjoint mem xj xi.
Proof.
  cbv[RWAddressesDisjoint].
  intuition eauto.
Qed.
Lemma RWAddressesDisjointImpliesWriteReadDisjoint:
  forall mem xi xj,
  RWAddressesDisjoint mem xi xj ->
  WriteReadDisjoint mem xi xj.
Proof.
  cbv[RWAddressesDisjoint WriteReadDisjoint ReachableRWAddr].
  intros. eapply H; eauto.
Qed.

Lemma RWAddressDisjointUpdate:
  forall mem mem' xi xi' xj,
  ValidMemUpdate mem xi mem' ->
  ReachableCaps mem xi xi' ->
  RWAddressesDisjoint mem xi xj ->
  RWAddressesDisjoint mem' xi' xj.
Proof.
  intros * hmem hreachable hdisjoint.
  destruct_products.
  cbv[RWAddressesDisjoint].
  intros * hcapi hcapj.
  eapply hdisjoint.
  - eapply ReachableRWAddr_ValidUpdate with (3 := hreachable) (2 := hmem); eauto.
  - unfold ValidMemUpdate in *. destruct_products.
    eapply ReachableRWAddrDisjointUnchanged with (mem := mem) (mem' := mem') (t:= xj); eauto.
    eapply RWAddressesDisjointImpliesWriteReadDisjoint; eauto.
Qed.

Lemma RWAddressDisjointUpdateUnchanged:
  forall mem mem' xi xj xk,
  ValidMemUpdate mem xk mem' ->
  RWAddressesDisjoint mem xi xj ->
  RWAddressesDisjoint mem xi xk ->
  RWAddressesDisjoint mem xj xk ->
  RWAddressesDisjoint mem' xi xj.
Proof.
  cbv[ValidMemUpdate].
  intros * hmem hdisjointij hdisjointik hdisjointjk. destruct_products.
  intros a hcapi hcapj.
  eapply ReachableRWAddrDisjointUnchanged with (mem := mem) (mem' := mem') (t:= xj) in hcapj; eauto.
  eapply ReachableRWAddrDisjointUnchanged with (mem := mem) (mem' := mem') (t:= xi) in hcapi; eauto.
  all: rewrite RWAddressDisjointUpdate_symmetry in *;
       try solve[eapply RWAddressesDisjointImpliesWriteReadDisjoint; eauto].
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
