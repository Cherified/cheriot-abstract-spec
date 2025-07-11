(*! Lemmas derived from the Spec *)
From Stdlib Require Import List Lia Bool Nat NArith.
Set Primitive Projections.
From cheriot Require Import Spec Utils Tactics.

Create HintDb invariants.
Import ListNotations.

Set Nested Proofs Allowed.

Section WithContext.
  Context [ISA: ISA_params].
  Context {Byte Key: Type}.
  Context {capEncodeDecode: @CapEncodeDecode Byte Key}.
  Notation FullMemory := (@FullMemory Byte).
  Notation Cap := (@Cap Key).
  Notation CapOrBytes := (@CapOrBytes Byte Key).
  Notation Machine := (@Machine Byte Key).
  Notation AddrOffset := nat (only parsing).
  Notation PCC := Cap (only parsing).
  Notation RegisterFile := (@RegisterFile Byte Key).
  Notation Thread := (@Thread Byte Key).

  Section ISA_params.
    Lemma ISA_CAPSIZE_BYTES_NONZERO:
      ISA_CAPSIZE_BYTES > 0.
    Proof.
      unfold ISA_CAPSIZE_BYTES.
      pose proof (PeanoNat.Nat.pow_nonzero 2 ISA_LG_CAPSIZE_BYTES). lia.
    Qed.
  End ISA_params.

  Section ReachabilityDefs.
  (* Addresses reachable with load permission. *)
    Definition ReachableReadAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs ,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Load p).

    (* Addresses reachable with write permission. *)
    Definition ReachableWriteAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs ,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Store p).

    (* Addresses reachable with execute permission. *)
    Definition ReachableExecAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs ,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Exec p).

    (* Addresses reachable with read or write permission. *)
    Definition ReachableRWAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      ReachableReadAddr mem caps a \/
        ReachableWriteAddr mem caps a.

    (* Addresses reachable with read, write, or execute permission. *)
    Definition ReachableRWXAddr (mem: FullMemory) (caps: list Cap) (a: Addr) :=
      exists p cs cbs,
        ReachableAddr mem caps a 1 p cs cbs /\ (In Perm.Load p \/ In Perm.Store p \/ In Perm.Exec p).

    Definition RWAddressesDisjoint (mem: FullMemory) (c1 c2: list Cap) : Prop :=
      forall a,
        ReachableRWAddr mem c1 a ->
        ReachableRWAddr mem c2 a ->
        False.

    Definition ReachableCapSubset (m_init m_cur: FullMemory) (caps_init caps_cur: list Cap) : Prop :=
      forall caps,
        ReachableCaps m_cur caps_cur caps ->
        ReachableCaps m_init caps_init caps.

    Definition WriteReadDisjoint (mem: FullMemory) (c1 c2: list Cap) : Prop :=
      forall a,
        ReachableWriteAddr mem c1 a ->
        ReachableReadAddr mem c2 a ->
        False.
  End ReachabilityDefs.

  Section CapStepLemmas.
    (* Attenuate is monotonic. *)
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

  End CapStepLemmas.

  Section ReachableCapLemmas.

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
  End ReachableCapLemmas.

  Section MemUpdateLemmas.
    (* After a valid memory update, if a cap can be loaded from the new memory
       then it must have been reachable from the old memory. *)
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

    Lemma LoadCapUpdate':
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
      forall mem mem' (caps caps': list Cap) c,
        ReachableCap mem' caps' c ->
        ValidMemUpdate mem caps mem' ->
        ReachableCaps mem caps caps' ->
        ReachableCap mem caps c.
    Proof.
      cbv [ReachableCaps].
      induction 1; intros * hupdate hcaps'; propositional.
      - auto.
      - eapply StepRestrict; eauto.
      - eapply LoadCapUpdate'; eauto.
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

  End MemUpdateLemmas.

  Section SeparationLemmas.
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
  End SeparationLemmas.

  Section WFInstructionLemmas.
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

  End WFInstructionLemmas.

  Section Step.
    Context {fetchAddrs: FullMemory -> Addr -> list Addr}.
    Context {decode: list Byte -> @Inst _ _ _ capEncodeDecode}.
    Context {pccNotInBounds : @EXNInfo Byte}.
    Notation MachineStep := (MachineStep fetchAddrs decode pccNotInBounds).
    Notation SameThreadStep := (SameThreadStep fetchAddrs decode pccNotInBounds).
    Notation ThreadStep := (ThreadStep fetchAddrs decode pccNotInBounds).

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
  End Step.
End WithContext.
