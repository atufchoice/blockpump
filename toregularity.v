Require Import List Logic Nat Omega FunctionalExtensionality ExtensionalityFacts ChoiceFacts Wellfounded.
Require Import Compare_dec EqNat Decidable ListDec FinFun.
Require Fin. 
Import ListNotations.
From Block   
Require Import pigeonhole lib definitions finite ramsey lemma3 lemma2choice lemma2nochoice. 

(* Every BC(k) language has finitely many derivatives *)
Theorem bc_to_finite_deriv : forall (k : block_pumping_constant) (L : {L | bc_sigma k L}),
    is_finite (fun l => is_deriv (proj1_sig L) l).
Proof.
  intros k L.
  assert (H_useful := @finite_conj_dep language). 
  spec H_useful (bc_sigma k) (is_deriv).
  spec H_useful (bc_k_is_finite k).
  assert (lemma3 := lemma3 k).
  assert (H_pre : (forall x : language,
                      bc_sigma k x -> forall x' : language, is_deriv x x' -> bc_sigma k x')).
  { intros l H_bc l_d H_deriv.
    spec lemma3 l H_bc. clear H_bc.
    destruct H_deriv as [x H_deriv].
    spec lemma3 l_d x.
    assert (is_derivative l l_d x).
    { unfold is_derivative. intro w. spec H_deriv w. assumption. }
    spec lemma3 H; clear H. assumption. }
  spec H_useful H_pre; clear H_pre.
  spec H_useful L. assumption.
Qed.

(* Setting up pigeonhole principle *) 
Definition get_prefix (w : word) (L : language) (i : nat) : language :=
  derivative_of L (firstn i w).

Definition get_prefix_indices (w : word) (L : language) (l : list nat) : list language :=
  map (get_prefix w L) l.

Definition pigeonlike (LS : equiv_classes) (L : list language)
           (H : forall l, In l L -> In l LS) (H_length : length LS < length L) :=
  pigeonhole_principle L LS H H_length. 

Lemma get_derivative_lang : forall (L : language) (l : list nat) (w : word) (n : nat),
    n < length l ->
    nth n (map (fun i : nat => derivative_of L (firstn i w)) l) (derivative_of L w)
    = derivative_of L (firstn (nth n l definitions.d) w). 
Proof.
  intros L l w n H_length.
  rewrite (nth_indep (map (fun i : nat => derivative_of L (firstn i w)) l)
                     (derivative_of L w)
                     (derivative_of L (firstn definitions.d w))). 
  rewrite (map_nth (fun i : nat => derivative_of L (firstn i w)) l definitions.d n).
  reflexivity.
  rewrite map_length. exact H_length. 
Qed.

Definition deriv_list (L : language) (w : word) (l : list nat) : list language :=
  get_prefix_indices w L l.

Lemma derivative_nil : forall (L : language),
    derivative_of L [] = L.
Proof.
  intro L.
  apply functional_extensionality.
  intro w. unfold derivative_of.
  rewrite app_nil_l. reflexivity.
Qed.

(* If L is in LS, then all derivatives of L are in LS *)
Lemma all_derivs_in : forall (LS : equiv_classes) (L : language),
    In L LS -> forall w, In (derivative_of L w) LS. 
Proof.
  intros LS L H_in w.
  destruct LS as [LS about_LS]; simpl in *.
  assert (about_LS_copy := about_LS).
  apply about_LS_copy.  exact H_in.
Qed.

Lemma all_derivs_in' : forall (L : language)
                         (LS : list language)
                         (H_reg : forall x, In x LS <-> is_deriv L x), 
    In L LS -> forall w, In (derivative_of L w) LS. 
Proof.
  intros LS L H_reg H_in w.
  apply H_reg. 
  unfold is_deriv, derivative_of.
  exists w. reflexivity.
Qed.

(* If L is in LS, then all derivatives in a list of derivatives of L are in LS *)
Lemma all_derivs_in_list : forall (LS : equiv_classes) (L : language) (ls : list language) (ln : list nat) (w : word),
    In L LS -> forall l', In l' (deriv_list L w ln) -> In l' LS. 
Proof.
  intros LS L ls ln w H_in l' H_in'.
  apply (In_nth (deriv_list L w ln) l' (derivative_of L w)) in H_in'.
  destruct H_in' as [i [H_i H_eq]].
  rewrite <- H_eq.
  unfold deriv_list, get_prefix_indices, get_prefix in *. 
  rewrite get_derivative_lang.
  apply all_derivs_in. exact H_in.
  rewrite map_length in H_i. exact H_i.
Qed.

Lemma all_derivs_in_list' : forall (L : language) (LS : list language)
                              (H_reg : forall x, In x LS <-> is_deriv L x)
                              (ls : list language) (ln : list nat) (w : word),
    In L LS -> forall l', In l' (deriv_list L w ln) -> In l' LS. 
Proof.
  intros L LS H_reg ls ln w H_in l' H_in'.
  apply (In_nth (deriv_list L w ln) l' (derivative_of L w)) in H_in'.
  destruct H_in' as [i [H_i H_eq]].
  rewrite <- H_eq.
  unfold deriv_list, get_prefix_indices, get_prefix in *. 
  rewrite get_derivative_lang.
  apply all_derivs_in'. exact H_reg. exact H_in.
  rewrite map_length in H_i. exact H_i.
Qed.

Definition is_suffix (w' w : word) : Prop :=
  exists i, skipn i w = w'.


(* ****************************** *)
(* **** Commutative triangle **** *)
(* ****************************** *)

(** Regular <-> block cancellable **) 
Theorem reg_to_bc : forall (L : language),
    regular L ->
    exists k, block_cancellable_matching_with k L.
Proof.
  intros L H_reg. 
  destruct H_reg as [LS H_in].
  destruct LS as [| LS_hd LS_tl].  
  - (* When LS is empty, there are no languages to be reasoned about. Boom! *)
    spec H_in L.
    assert (is_deriv L L).
    { exists ([] : word). intro w; rewrite app_nil_l; reflexivity. }
    apply H_in in H. inversion H. 
  - (* When LS contains at least one language, *)
    remember (LS_hd :: LS_tl) as LS. 
    assert (H_pc : length LS + 1 >= 2).
    { subst LS; simpl; omega. }
    exists (exist p_predicate (length LS + 1) H_pc). 
    intros w bps. 
    (* Now we argue about the word length and the length of the finite
       list of language equivalence classes *)
    (* First we want to combust the absurd breakpoints *) 
    assert (H_w_length : length w < length LS \/ length w >= length LS) by omega.
    destruct H_w_length as [boom | calm].
    + (* In the case of an explosion, *)
      destruct_bps bps about_bps.
      assert (H_boom := breakpoint_explosion_one).
      spec H_boom (exist (le 2) (length LS + 1) H_pc) w.
      simpl in H_boom.
      assert (retarded : length w < length LS + 1 - 1) by omega.
      spec H_boom retarded. exfalso.  apply (H_boom bps).
      assumption.  
    + (* In that case of pigeonhole principle, *)
      (* Trying to commute the easy way by sticking this in here *) 
      assert (about_LS : equiv_classes_pred LS).
        { unfold equiv_classes_pred. intros L' H_in' x'. 
          (* We must show that the derivative of L' with regard to some x
           is in the list which contains all derivatives of L *)
          (* This requires some transitivity argument on derivative-ness *)
          apply H_in.
          unfold is_deriv, derivative_of.
          spec H_in L'. apply H_in in H_in'.
          unfold is_deriv in H_in'.
          destruct H_in' as [s H_in'].
          exists (s ++ x').
          intro w'.
          spec H_in' (x' ++ w').
          rewrite app_assoc_reverse.
          assumption. } 
      destruct_bps bps about_bps.
      set (ld := deriv_list L w bps). 
      assert (H_length : length bps = length ld).
      { subst ld.
        unfold deriv_list, get_prefix_indices; now rewrite map_length. }
      assert (H_pre1 : forall l, In l ld -> In l LS). 
      intros L' H_in'. 
      assert (H_useful := all_derivs_in_list (exist _ LS about_LS) L ld bps w).
      simpl in H_useful.
      assert (H_obv : is_deriv L L).
      { exists ([] : word). intro; rewrite app_nil_l; reflexivity. }
      apply H_in in H_obv. spec H_useful H_obv.
      spec H_useful L' H_in'. assumption. 
      assert (H_pre2 : length LS < length ld) by omega.
      assert (H_pigeon := pigeonlike (exist _ LS about_LS) ld H_pre1 H_pre2).
      inversion H_pigeon.
      destruct H0 as [repeated_l [H_in1 H_in2]].
      apply (In_nth l1 repeated_l (derivative_of L w)) in H_in1;
        apply (In_nth l2 repeated_l (derivative_of L w)) in H_in2; 
        destruct H_in1 as [i [H_i H_in1]];
        destruct H_in2 as [j [H_j H_in2]].
      assert (H_length_split : length ld = length l1 + length l2). 
      { rewrite <- H. rewrite app_length. reflexivity. }
      (* Constructing the breakpoints! *)
      (* The first breakpoint is just i. *) 
      remember (nth i bps definitions.d) as bp1.
      (* The second breakpoint has to be offset by the length
         of the first list. *) 
      remember (nth (length l1 + j) bps definitions.d) as bp2.
      assert (about_bp1 : breakpoint_predicate bp1 (exist _ (length LS + 1) H_pc) w (exist _ bps about_bps)). rewrite Heqbp1. apply nth_In; simpl; omega. 
      assert (about_bp2 : breakpoint_predicate bp2 (exist _ (length LS + 1) H_pc) w (exist _ bps about_bps)). rewrite Heqbp2. apply nth_In; simpl; omega. 
      (* Supplying breakpoint witnesses! *) 
      exists (exist _ bp1 about_bp1).
      exists (exist _ bp2 about_bp2).
      simpl in *. split. rewrite Heqbp1, Heqbp2.
      { (* gt obligation *)
        destruct about_bps as [H_length_bps [H_incr_bps H_last_bps]].
        clear -H_incr_bps H_i H_j H_length H_length_split.
        spec H_incr_bps i (length l1 + j).
        apply H_incr_bps. omega. } 
      (* Now we get to the actual argument about word acceptance! *)
      clear about_bp1 about_bp2 about_bps H_pc H_pre1 H_pre2 H_pigeon.
      rewrite (nth_app_offset l1 l2 j (derivative_of L w)) in H_in2.
      rewrite <- (app_nth1 l1 l2 (derivative_of L w) H_i) in H_in1.
      subst ld. 
      rewrite H in *; clear H.
      unfold deriv_list, get_prefix_indices, get_prefix in *.
      rewrite get_derivative_lang in H_in1, H_in2. 
      2 : omega. 2 : omega. 
      rewrite <- Heqbp1 in H_in1.
      rewrite plus_comm in Heqbp2; rewrite <- Heqbp2 in H_in2.
      rewrite <- H_in2 in H_in1; clear -H_in1.
      assert (H_bridge : derivative_of
                           (derivative_of L (firstn bp1 w))
                           (skipn bp2 w) =
                         derivative_of
                           (derivative_of L (firstn bp2 w))
                           (skipn bp2 w)).
      { rewrite <- H_in1; reflexivity. }
      clear H_in1. 
      assert (H_eq := language_equality
                        (derivative_of (derivative_of L (firstn bp1 w)) (skipn bp2 w))
                        (derivative_of (derivative_of L (firstn bp2 w)) (skipn bp2 w))).
      destruct H_eq as [H_eq _].
      spec H_eq H_bridge ([] : word); clear H_bridge.
      split; intro H. 
      ++ destruct H_eq as [left _]. 
         rewrite chomp_deriv.  
         do 2 rewrite cat_deriv in left.
         rewrite firstn_skipn in left.
         apply left; rewrite chomp_deriv in H; assumption.
      ++ destruct H_eq as [_ right].
         rewrite chomp_deriv.
         do 2 rewrite cat_deriv in right. 
         rewrite firstn_skipn in right.
         rewrite chomp_deriv in H.
         apply right in H; assumption.
Qed.

(* Block cancellable -> regular *) 
Theorem bc_to_reg : forall (L : language),
    (exists k, block_cancellable_matching_with k L) -> regular L.
Proof.
  intros L [k H_BC].
  assert (H_useful := bc_to_finite_deriv k).
  spec H_useful (exist (bc_sigma k) L H_BC). exact H_useful.
Qed.

(** Regular <-> block pumpable **) 
Theorem reg_to_bp :
  forall (L : language), regular L -> exists k, block_pumpable_matching_with k L.
Proof.
  intros L H_reg. 
  destruct H_reg as [LS H_in].
  destruct LS as [| LS_hd LS_tl].  
  - (* When LS is empty, there are no languages to be reasoned about. Boom! *)
    spec H_in L.
    assert (is_deriv L L).
    { exists ([] : word). intro w; rewrite app_nil_l; reflexivity. }
    apply H_in in H. inversion H. 
  - (* When LS contains at least one language, *)
    remember (LS_hd :: LS_tl) as LS. 
    assert (H_pc : length LS + 1 >= 2).
    { subst LS; simpl; omega. }
    exists (exist p_predicate (length LS + 1) H_pc). 
    intros w bps. 
    (* Now we argue about the word length and the length of the finite
       list of language equivalence classes *)
    (* First we want to combust the absurd breakpoints *) 
    assert (H_w_length : length w < length LS \/ length w >= length LS) by omega.
    destruct H_w_length as [boom | calm].
    + (* In the case of an explosion, *)
      destruct_bps bps about_bps.
      assert (H_boom := breakpoint_explosion_one).
      spec H_boom (exist (le 2) (length LS + 1) H_pc) w.
      simpl in H_boom.
      assert (retarded : length w < length LS + 1 - 1) by omega.
      spec H_boom retarded. exfalso.  apply (H_boom bps).
      assumption.  
    + (* In that case of pigeonhole principle, *)
      (* Trying to commute the easy way by sticking this in here *) 
      assert (about_LS : equiv_classes_pred LS).
        { unfold equiv_classes_pred. intros L' H_in' x'. 
          (* We must show that the derivative of L' with regard to some x
           is in the list which contains all derivatives of L *)
          (* This requires some transitivity argument on derivative-ness *)
          apply H_in.
          unfold is_deriv, derivative_of.
          spec H_in L'. apply H_in in H_in'.
          unfold is_deriv in H_in'.
          destruct H_in' as [s H_in'].
          exists (s ++ x').
          intro w'.
          spec H_in' (x' ++ w').
          rewrite app_assoc_reverse.
          assumption. } 
      destruct_bps bps about_bps.
      set (ld := deriv_list L w bps). 
      assert (H_length : length bps = length ld).
      { subst ld.
        unfold deriv_list, get_prefix_indices; now rewrite map_length. }
      assert (H_pre1 : forall l, In l ld -> In l LS). 
      intros L' H_in'. 
      assert (H_useful := all_derivs_in_list (exist _ LS about_LS) L ld bps w).
      simpl in H_useful.
      assert (H_obv : is_deriv L L).
      { exists ([] : word). intro; rewrite app_nil_l; reflexivity. }
      apply H_in in H_obv. spec H_useful H_obv.
      spec H_useful L' H_in'. assumption. 
      assert (H_pre2 : length LS < length ld) by omega.
      assert (H_pigeon := pigeonlike (exist _ LS about_LS) ld H_pre1 H_pre2).
      inversion H_pigeon.
      destruct H0 as [repeated_l [H_in1 H_in2]].
      apply (In_nth l1 repeated_l (derivative_of L w)) in H_in1;
        apply (In_nth l2 repeated_l (derivative_of L w)) in H_in2; 
        destruct H_in1 as [i [H_i H_in1]];
        destruct H_in2 as [j [H_j H_in2]].
      assert (H_length_split : length ld = length l1 + length l2).  
      { rewrite <- H. rewrite app_length. reflexivity. }
      (* Finally we can start constructing the breakpoints! *)
      (* The first breakpoint is just i. *) 
      remember (nth i bps definitions.d) as bp1.
      (* The second breakpoint has to be offset by the length
         of the first list. *) 
      remember (nth (length l1 + j) bps definitions.d) as bp2.
      assert (about_bp1 : breakpoint_predicate bp1 (exist _ (length LS + 1) H_pc) w (exist _ bps about_bps)).
      { rewrite Heqbp1. apply nth_In; simpl; omega. }
      assert (about_bp2 : breakpoint_predicate bp2 (exist _ (length LS + 1) H_pc) w (exist _ bps about_bps)).
      { rewrite Heqbp2. apply nth_In; simpl; omega. }
      assert (H_bp1_lt := about_bp_length (exist _ (length LS + 1) H_pc)
                                         w
                                         (exist _ bps about_bps)
                                         (exist _ bp1 about_bp1)).
      assert (H_bp2_lt := about_bp_length (exist _ (length LS + 1) H_pc)
                                         w
                                         (exist _ bps about_bps)
                                         (exist _ bp2 about_bp2)).
      simpl in *. 
      (* Supplying breakpoint witnesses! *)
      (* At some point I need to preserve the hypothesis that
         bp1 < bp2 < length w *) 
      exists (exist _ bp1 about_bp1).
      exists (exist _ bp2 about_bp2).
      simpl in *.
      assert (H_temp : bp1 < bp2).
      { (* gt obligation *)
        rewrite Heqbp1, Heqbp2.
        destruct about_bps as [H_length_bps [H_incr_bps H_last_bps]].
        clear -H_incr_bps H_i H_j H_length H_length_split.
        spec H_incr_bps i (length l1 + j).
        apply H_incr_bps. omega. }
      split.
      exact H_temp. 
      (* Now we get to the actual argument about word acceptance! *)
      rewrite (nth_app_offset l1 l2 j (derivative_of L w)) in H_in2.
      rewrite <- (app_nth1 l1 l2 (derivative_of L w) H_i) in H_in1.
      subst ld. 
      rewrite H in *; clear H.
      unfold deriv_list, get_prefix_indices, get_prefix in *.
      rewrite get_derivative_lang in H_in1, H_in2. 
      2 : omega. 2 : omega. 
      rewrite <- Heqbp1 in H_in1.
      rewrite plus_comm in Heqbp2; rewrite <- Heqbp2 in H_in2.
      rewrite <- H_in2 in H_in1.
      clear -H_in1 H_bp1_lt H_bp2_lt H_temp. 
      (* ************************************************* *)
      (* Here is where the proof for bp -> regular_necc differs *)
      induction m as [|m IHm]. 
      -- (* The zero case is equivalent to proving bc *)
        unfold napp.
        rewrite app_nil_l.
        rewrite language_equality in H_in1.
        assert (H_bridge : forall w0 : word,
                   derivative_of L (firstn bp1 w ++ skipn bp2 w) w0
                   = derivative_of L (firstn bp2 w ++ skipn bp2 w) w0).
        { apply (extend_deriv (firstn bp1 w) (firstn bp2 w) (skipn bp2 w) L).
          intro w'.
          apply prop_ext.
          spec H_in1 w'; assumption. }
        clear H_in1.
        rewrite firstn_skipn in H_bridge.
        rewrite (chomp_deriv (firstn bp1 w ++ skipn bp2 w)).
        rewrite (chomp_deriv w).
        apply functional_extensionality in H_bridge. 
        rewrite H_bridge.
        split; intro H; assumption.
      -- (* Append the rest of the pumps onto (firstn bp2 w) *)
        (* But first, case analysis on whether bp2 = length w *)
        assert (H_eq : firstn bp1 w ++ pumpable_block bp1 bp2 w
                       = firstn bp2 w). 
        { apply left_mid. split. exact H_temp. exact H_bp2_lt. }
        clear H_bp1_lt H_temp.
        split; intro H. 
        ** simpl in H.
           assert (H_tmp : L (firstn bp2 w ++ napp m (pumpable_block bp1 bp2 w) ++ skipn bp2 w)).
           { rewrite <- H_eq. rewrite app_assoc_reverse.
             rewrite <- app_assoc in H. 
             exact H. } clear H_eq H. 
           assert (H_next : derivative_of L
                                          (firstn bp2 w)
                                          (napp m (pumpable_block bp1 bp2 w) ++ skipn bp2 w)) by exact H_tmp. clear H_tmp.
           rewrite <- H_in1 in H_next.
           unfold derivative_of in H_next.
           apply IHm in H_next. exact H_next.
        ** apply IHm in H. clear IHm.
           assert (H_next : derivative_of L
                                          (firstn bp1 w)
                                          (napp m (pumpable_block bp1 bp2 w) ++ skipn bp2 w)). 
           { unfold derivative_of. exact H. } clear H.
           rewrite H_in1 in H_next. 
           rewrite <- H_eq in H_next. clear H_in1 H_eq. 
           unfold derivative_of in H_next.
           rewrite app_assoc_reverse in H_next.
           simpl. rewrite app_assoc_reverse. exact H_next.
Qed.

(* Block pumpable -> regular *) 
Theorem bp_to_reg :
  forall (L : language) (k : block_pumping_constant),
    block_pumpable_matching_with k L -> regular L.
Proof.
  intros L k H_bp.
  assert (H_bridge : block_cancellable_matching_with k L).
  intros w bps.
  spec H_bp w bps.
  destruct H_bp as [i [j [H_lt H_pump]]]. 
  exists i, j. split. assumption.
  spec H_pump 0. unfold napp in H_pump.
  rewrite app_nil_l in H_pump. assumption.
  apply bc_to_reg.
  exists k. assumption.
Qed.

(** Block pumpable <-> block cancellable **)
(* Block pumpable -> block cancellable *)
Theorem bp_to_bc :
  forall (L : language) (k : block_pumping_constant),
    block_pumpable_matching_with k L ->
    block_cancellable_matching_with k L.
Proof.
  intros L k H_bp w bps.
  spec H_bp w bps.
  destruct H_bp as [i [j [H_lt H_pump]]]. 
  exists i, j. split. assumption.
  spec H_pump 0. unfold napp in H_pump.
  rewrite app_nil_l in H_pump. assumption.
Qed.

(* Block cancellable -> block pumpable *) 
Theorem bc_to_bp :
  forall (L : language) (k : block_pumping_constant),
    block_cancellable_matching_with k L ->
    exists (k' : block_pumping_constant), 
    block_pumpable_matching_with k' L.
Proof.
  intros L k H_bc.
  assert (H_reg : regular L).
  apply bc_to_reg. exists k.
  assumption.
  apply reg_to_bp. assumption.
Qed. 
