Require Import List Logic Nat Arith Bool Omega.
Require Import Compare_dec EqNat Decidable ListDec FinFun. 
Require Fin. 
Import ListNotations. 
From Block   
Require Import lib definitions finite ramsey lemma2nochoice.

Definition languager : Type := word -> bool. 

Definition bc_sigmar (k : block_pumping_constant) : languager -> Prop :=
  fun L : languager =>
    forall (s : word),
    forall (bl : breakpoint_set k s),
    exists (i j : breakpoint bl),
      i < j /\ L (firstn i s ++ skipn j s) = L s.

Definition bc_languager (k : block_pumping_constant) : Type :=
  { l : languager | bc_sigmar k l}. 

Definition bc_languager_proj1 {k : block_pumping_constant} (bcl : bc_languager k) :=
  match bcl with
  | exist _ b _ => b
  end.

Theorem unshear_bool_equiv :
  forall (k rk : block_pumping_constant)
    (lw : list word),
    unshear k rk lw = fun w => unshear_bool k rk lw w = true. 
Proof.
  intros k rk lw.
  unfold unshear. reflexivity.
Qed.

Definition agreement_upto_bool (k rk : block_pumping_constant) (l : bc_languager k) (lw : list word) (m : nat) :=
  forall w, In w lw <-> (length w <= m + rk /\ bc_languager_proj1 l w = true).

Definition shear_languager (n : nat) (l : languager) : languager :=
  fun w => (l w) && (length w <=? n).

Theorem IH_agreement_bool :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant), 
  forall (l : bc_languager k)
    (lw : list word)
    (m : nat),
    agreement_upto_bool k rk l lw m ->
    agreement_upto_bool k rk l (words_to_add_of_length (S m + rk) lw k ++ lw) (S m).
Proof.
  intros k.
  destruct k as [k about_k];
    unfold p_predicate in about_k.
  assert (H_pre : k > 0) by omega. 
  assert (H_ramsey := Ramsey_single_prop k H_pre).  
  destruct H_ramsey as [rk [about_rk H_ramsey]].
  assert (about_rk_two : rk >= 2) by omega.
  exists (exist p_predicate rk about_rk_two); simpl in *.
  intros l lw m IH.
  intros w; split; intro H.
  - (* Either the word is in the old list or it's in the new list *)
    apply in_app_or in H. 
    destruct H as [H_new | H_old].
    + (* In the case that the word is in the new list *)
      unfold words_to_add_of_length in H_new. 
      rewrite words_to_add_correct in H_new.
      destruct H_new as [H_all H_in].
      rewrite generate_words_length_correct in H_in.
      split. simpl. omega. 
      destruct l as [l about_l].
      assert (H_bc := about_l).
      spec H_bc w.
      destruct H_all as [lp [H_all H_chosen]]. 
      assert (about_lp : breakpoint_set_predicate lp w (exist p_predicate k about_k)).
      { apply iota_gives_bps. 
        rewrite H_in.
        unfold p_predicate in about_k. 
        simpl.  omega. assumption. } 
      specialize (H_bc (exist _ lp about_lp)).
      destruct H_bc as [i [j [i_lt_j about_i_j]]].
      simpl in *. rewrite <- about_i_j. 
      destruct i as [i about_i];
        destruct j as [j about_j]. 
      unfold breakpoint_predicate in *. 
      simpl in *.
      unfold are_all_pumps_prop in H_all. 
      assert (about_i_copy := about_i). 
      assert (about_j_copy := about_j).
      apply (In_nth _ _ definitions.d) in about_i.
      apply (In_nth _ _ definitions.d) in about_j.
      destruct about_i as [i_pos [i_lt i_eq]]. 
      destruct about_j as [j_pos [j_lt j_eq]].
      spec H_all i_pos j_pos.
      assert (H_pre' : i_pos < j_pos < length lp). 
      { split. destruct about_lp as [lp_length [lp_incr lp_last]].
        eapply increasing_nth_lt. exact lp_incr. assumption.
        assumption. rewrite <- i_eq in i_lt_j; rewrite <- j_eq in i_lt_j.
        assumption. assumption. } 
      spec H_all H_pre'. clear H_pre'.
      unfold cancelled_word in H_all.
      subst i j.
      spec IH (firstn (nth i_pos lp definitions.d) w ++
                      skipn (nth j_pos lp definitions.d) w).
      rewrite IH in H_all. destruct H_all as [_ goal].
      simpl in *. assumption.
    + (* In the case that the word is in the old list *)
      spec IH w. rewrite IH in H_old. 
      destruct H_old as [H_length H_mem].
      split. omega.
      assumption.
  - (* The new word is short and is in the language *)
    destruct H as [H_length H_bc]. 
    apply le_lt_or_eq in H_length.
    apply in_or_app. 
    destruct H_length as [H_old | H_new].
    + (* In the case that the new word is too short to be new *)
      right.
      replace (S m + rk) with (S (m + rk)) in H_old by omega. 
      apply lt_n_Sm_le in H_old.
      spec IH w. apply IH. split; assumption.
    + (* In the case that the new word is new *)
      left.
      unfold words_to_add_of_length. 
      rewrite words_to_add_correct.  
      (* Need Ramsey here *)
      (* Making sure to use the zero version *)
      split. 
      2 : rewrite generate_words_length_correct; assumption.
      unfold exists_all_pumps_bps_prop.
      unfold get_k_bps.
      assert (about_big_bps : breakpoint_set_predicate (iota 0 rk) w (exist _ rk about_rk_two)).
      { apply iota_bps. simpl in *; omega. }
      spec H_ramsey (iota 0 rk).
      spec H_ramsey. apply length_iota.
      spec H_ramsey (fun i j => bc_languager_proj1 l (cancelled_word w i j) = true).
      destruct H_ramsey as [[bps_yes [bps_length [bps_subseq about_bps_yes]]] | [bps_no [bps_length [bps_subseq about_bps_no]]]].  
      * (* Ramsey case yes *)  
        exists bps_yes. split.
        ** (* Pump correctness *) 
          unfold are_all_pumps_prop. 
          intros.
          rewrite bps_length in H. 
          spec about_bps_yes i j H.
          apply IH. split.
          (* Word is shorter obligation *) 
          simpl.  
          unfold cancelled_word.
          assert (H_useful := firstn_skipn_shortens w (nth i bps_yes d) (nth j bps_yes d)).
          assert (H_bps_incr : increasing bps_yes).
          { apply (subseq_incr (iota 0 rk) definitions.d).
            apply iota_increasing. assumption. }
          assert (bps_incr := H_bps_incr).  
          spec H_bps_incr i j.
          rewrite bps_length in H_bps_incr.
          spec H_bps_incr H. spec H_useful. rewrite H_new.
          split. assumption. simpl.
          assert (H_last := about_subseq_last bps_yes (iota 0 rk) definitions.d).
          spec H_last. rewrite bps_length; omega.
          spec H_last. rewrite length_iota; omega.
          spec H_last. apply iota_increasing.
          spec H_last bps_subseq.
          replace (last (iota 0 rk) d) with (rk - 1) in H_last.
          2 : rewrite iota_last_nonzero; omega.
          (* assert (H_trans1 := about_incr_length_last k definitions.d bps_yes).
          spec H_trans1. intro absurd. apply length_zero_iff_nil in absurd.
          omega. spec H_trans1 bps_length bps_incr. *)
          assert (H_trans := about_incr_nth_last definitions.d bps_yes bps_incr j). spec H_trans. rewrite bps_length; omega.
          omega. 
          rewrite H_new in H_useful. 
          simpl in H_useful. omega. 
          (* Language recognizes pumped word obligation *) 
          assumption.
        ** (* In choose *)
          apply choose_spec.
          rewrite length_iota. rewrite H_new. simpl. omega.
          split. assumption.
          assert (H_trans : subseq (iota 0 rk) (iota 0 (S (length w)))).
          apply subseq_grow. rewrite H_new. simpl; omega. 
          now apply (subseq_trans nat bps_yes (iota 0 rk) (iota 0 (S (length w)))).
      * (* Ramsey case no *) 
        destruct l as [l about_l].
        assert (about_l_copy := about_l).
        assert (bps_incr : increasing bps_no). 
        { apply (subseq_incr (iota 0 rk) definitions.d).
          apply iota_increasing. assumption. }
        assert (bps_bps_no : breakpoint_set_predicate bps_no w (exist _ k about_k)). 
        { split. simpl. assumption.
          split. assumption. 
          assert (H_last := about_subseq_last (iota 0 rk) bps_no definitions.d). 
          rewrite bps_length in H_last.
          spec H_last. rewrite length_iota. 
          assumption. spec H_last about_k. 
          apply (Nat.le_trans (last bps_no d) (last (iota 0 rk) d) (length w)).
          apply about_subseq_last.
          omega. rewrite length_iota. assumption.
          apply iota_increasing. assumption.
          rewrite H_new. rewrite iota_last_nonzero.
          simpl. omega. omega. } 
        spec about_l_copy w.
        specialize (about_l_copy (exist _ bps_no bps_bps_no)).
        destruct about_l_copy as [i [j [H_ij_lt H_in]]].
        destruct i as [i about_i];
          unfold breakpoint_predicate in about_i. 
        destruct j as [j about_j];
          unfold breakpoint_predicate in about_j.
        simpl in *.
        apply (In_nth _ _ definitions.d) in about_i.
        apply (In_nth _ _ definitions.d) in about_j.
        destruct about_i as [i_pos [i_pos_lt i_pos_eq]].
        destruct about_j as [j_pos [j_pos_lt j_pos_eq]].
        spec about_bps_no i_pos j_pos.
        rewrite <- i_pos_eq in H_ij_lt.
        rewrite <- j_pos_eq in H_ij_lt. 
        spec about_bps_no.
        split.
        now apply (increasing_nth_lt bps_no definitions.d bps_incr i_pos j_pos).
        omega.
        rewrite <- H_in in H_bc. unfold cancelled_word in about_bps_no.
        rewrite i_pos_eq, j_pos_eq in about_bps_no. contradiction.
Qed.
(* This lemma is done *)

Lemma IH_chuck_step_bool :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant), 
  forall (l : bc_languager k) (lw : list word) (m : nat),
    agreement_upto_bool k rk l lw m ->
    agreement_upto_bool k rk l (chuck k rk (S m) lw) (S m).
Proof.
  intros k.
  assert (H_useful := IH_agreement_bool k).
  destruct H_useful as [rk H_useful].
  exists rk. intros l lref m H_base. 
  specialize (H_useful l lref m H_base).
  rewrite filter_equiv in H_useful.
  unfold chuck. assumption.
Qed.

(* For every k there exists an rk such that for all bc_k languages 
   and lists that agree with them, we can safely chuck_length *) 
Lemma IH_chuck_bool :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant),
  forall (l : bc_languager k) (lw : list word),
    agreement_upto_bool k rk l (chuck_length k rk 0 lw) 0 ->
    forall (m : nat),
      agreement_upto_bool k rk l (chuck_length k rk m lw) m.
Proof. 
  intros k.
  destruct (IH_chuck_step_bool k) as [rk H_useful].
  exists rk. intros l lw H_base m.
  induction m.
  - (* Base case, assumption *)
    simpl in *.
    assumption.
  - (* Inductive step *)
    simpl. 
    apply H_useful. assumption. 
Qed.

Theorem unshear_correctness_bool :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant),
  forall (l : bc_languager k) (lw : list word),
    agreement_upto_bool k rk l (chuck_length k rk 0 lw) 0 ->
    (forall (w : word),
        In w lw <-> (shear_languager rk (unshear_bool k rk lw)) w = true)
    /\ (forall (w : word), unshear_bool k rk lw w = bc_languager_proj1 l w).
Proof. 
  intros k.
  assert (H_chuck := IH_chuck_bool k).
  destruct H_chuck as [rk H_chuck]. 
  exists rk.
  intros bcl lw H_base.
  split.
  - (* Proving theorem_the_first, essentially *)
    intro w.
    spec H_chuck bcl lw H_base.
    split; intro H.  
    + (* --> *)  
      unfold unshear, unshear_bool, shear_languager.
      rewrite andb_lazy_alt.
      assert (H_obv : is_member w (chuck_length k rk (length w) lw) = true). 
      { rewrite is_member_correct.
        red in H_chuck. apply H_chuck. split.
        omega.
        destruct bcl as [bcl about_bcl]. simpl in *.
        red in H_base. apply H_base in H. simpl in *.
        tauto. } 
      rewrite H_obv. red in H_base.  
      assert (H_obv' : is_member w (chuck_length k rk 0 lw) = true).
      { simpl. rewrite is_member_correct. assumption. }
      rewrite is_member_correct in H_obv'.
      rewrite H_base in H_obv'.
      destruct H_obv' as [goal _].
      rewrite Nat.add_0_l in goal.
      apply leb_correct. assumption. 
    + (* <-- *)
      apply H_base. 
      unfold unshear, unshear_bool, shear_languager in H.
      apply andb_prop in H.
      destruct H as [H_in H_length].
      split.
      rewrite Nat.add_0_l.
      apply leb_complete. assumption. 
      spec H_chuck (length w).
      spec H_chuck w.
      rewrite is_member_correct in H_in.
      rewrite H_chuck in H_in.
      destruct H_in as [_ goal].
      exact goal.
  - (* Proving theorem_the_second, essentially *) 
    spec H_chuck bcl lw H_base.
    intro w. 
    + (* --> *)
      spec H_chuck (length w).
      spec H_chuck w. 
      unfold unshear_bool.
      assert (is_member w (chuck_length k rk (length w) lw) = true <->
              bc_languager_proj1 bcl w = true). 
      split; intro H.
      rewrite is_member_correct in H.
      apply H_chuck in H. destruct H as [_ goal]; assumption.
      assert (length w <= length w + rk /\ bc_languager_proj1 bcl w = true).
      split. omega. assumption.
      rewrite <- H_chuck in H0.
      apply is_member_correct. assumption.
      apply eq_true_iff_eq in H.
      assumption.
Qed.
  
Theorem is_finite_subseq_wf_bool :
  forall (k rk : block_pumping_constant),
    is_finite (fun lw => subseq lw (generate_words_upto rk) /\
                      exists (l : bc_languager k), agreement_upto_bool k rk l lw 0). 
Proof.   
  intros.
  now apply (is_finite_conj (fun lw => subseq lw (generate_words_upto rk))
                            (fun lw => exists (l : bc_languager k), agreement_upto_bool k rk l lw 0)
                            (is_finite_shortwords rk)). 
Qed.

Theorem get_list_shear_languager :
  forall (l : languager) (rk : nat),
  exists (L : list word),
    forall (w : word), In w L <-> shear_languager rk l w = true. 
Proof.
  intros l rk. 
  remember (generate_words_upto rk) as W.
  assert (forall w, shear_languager rk l w = true -> In w W).
  { intros. unfold shear_languager in H.
    apply andb_prop in H. 
    destruct H as [_ goal].
    apply leb_complete in goal.
    subst. 
    apply generate_words_upto_correct. assumption. }
  assert (forall W1 W2,
             (forall w, In w W <-> In w (W1 ++ W2)) ->
             (exists L, sublist L W1
                   /\ forall w : word,
                   (In w L -> shear_languager
                               rk l w = true)
                   /\ (shear_languager rk l w = true -> (In w L \/ In w W2)))).
  { induction W1; intros.
    * exists nil. split. red. auto.
      intros. split; intro.
      inversion H1. right. simpl in H0. apply H0, H, H1.
    * simpl in H0. specialize (IHW1 (a :: W2)). spec IHW1.
      intros lw. spec H0 lw. 
      split; intro. rewrite H0 in H1. destruct H1.
      subst. apply in_or_app. right. apply in_eq.
      apply in_or_app. apply in_app_or in H1.
      destruct H1. left; assumption. right.
      apply in_cons; assumption.
      apply in_app_or in H1. destruct H1.
      apply H0. right. apply in_or_app. left; assumption.
      destruct H1. apply H0. left; assumption.
      apply H0. right; apply in_or_app; right; assumption. 
      destruct IHW1 as [L [? ?]].
      case_eq (shear_languager rk l a); intro. 
    + exists (a :: L). split. repeat intro.
      destruct H4. left. assumption. right. apply H1. assumption.
      intros. split. intro. destruct H4. subst. assumption.
      specialize (H2 w). destruct H2. apply H2, H4.
      specialize (H2 w). destruct H2. intro H5. spec H4 H5.
      destruct H4 as [? | [? | ?]].
      left. right. assumption.
      left. left. assumption.
      right. assumption.
    + exists L. split. 
      right. apply H1, H4.
      intros. spec H2 w. destruct H2.
      split. assumption.
      intros. specialize (H4 H5).
      destruct H4. left. assumption.
      destruct H4. subst.
      rewrite H3 in H5; inversion H5. 
      right. assumption. }
  specialize (H0 W nil). spec H0.
  rewrite app_nil_r. split; trivial.
  destruct H0 as [L [? ?]]. exists L.
  intro w. spec H1 w. destruct H1. split; intro.
  apply H1, H3.
  apply H2 in H3. destruct H3. assumption. inversion H3. 
Qed. 

Theorem get_nodup_list_shear_languager :
  forall (l : languager) (rk : nat),
  exists (L : list word),
    (subseq L (generate_words_upto rk)) /\
     forall (w : word), In w L <-> shear_languager rk l w = true. 
Proof.
  intros l rk.
  assert (H_useful := get_list_shear_languager l rk).
  destruct H_useful as [L H_useful].
  exists (filter (fun w => andb (length w <=? rk) (is_member w L)) (generate_words_upto rk)).
  split.
  now apply filter_subseq_correct.
  intros w; split; intro.
  apply filter_In in H.
  destruct H.
  apply H_useful.
  apply andb_prop in H0. 
  destruct H0.
  rewrite is_member_correct in H1.
  assumption.
  apply filter_In. split.
  unfold shear_languager in H.
  apply andb_prop in H. destruct H.
  apply generate_words_upto_correct.
  apply leb_complete. assumption.
  assert (H_copy := H). 
  apply H_useful in H.
  apply andb_true_intro. split.
  unfold shear_languager in H_copy.
  apply andb_prop in H_copy.
  destruct H_copy.
  assumption. apply is_member_correct.
  assumption. 
Qed. 

Theorem get_list_shear_bc_languager :
  forall (k rk : block_pumping_constant) (l : bc_languager k),
  exists (L : list word),
    (subseq L (generate_words_upto rk))  /\
    forall (w : word), In w L <-> shear_languager rk (bc_languager_proj1 l) w = true. 
Proof.
  intros k rk l. 
  assert (H_useful := get_nodup_list_shear_languager (bc_languager_proj1 l) rk).
  destruct H_useful as [L H_useful].
  exists L. assumption. 
Qed.

Theorem bc_dec_k_is_finite_nochoice_bool :
    forall (k : block_pumping_constant),
    is_finite (bc_sigmar k).
Proof.
  intros k.  
  assert (H_blink := unshear_correctness_bool k).
  destruct H_blink as [rk H_blink].
  assert (H_fin := is_finite_subseq_wf_bool k rk).
  destruct H_fin as [llw about_llw].  
  exists (map (unshear_bool k rk) llw). 
  intro l. 
  split; intro H.
  + (* We have a language that's in our constructed list *) 
    rewrite in_map_iff in H.  
    destruct H as [wf_sl [H_eq H_in]].
    (* By that we know it must have come from some short list *)
    spec about_llw wf_sl. 
    rewrite about_llw in H_in; clear about_llw. 
    destruct H_in as [_ [bcl_witness H_witness]].
    (* And by some reasoning, we can build to bcl_witness *)
    spec H_blink bcl_witness wf_sl H_witness.
    destruct H_blink as [H1 H2].
    rewrite <- H_eq.
    intro w. intros bl.
    destruct bcl_witness as [bcl about_bcl] . 
    assert (about_bcl_copy := about_bcl).
    spec about_bcl_copy w bl.
    destruct about_bcl_copy as [i [j [H_lt bcl_eq]]].
    exists i, j. split. assumption.
    do 2 rewrite H2. simpl. assumption.
  + rewrite in_map_iff.
    specialize (H_blink (exist _ l H)). 
    assert (H_getlist := get_list_shear_bc_languager k rk (exist _ l H)).   
    destruct H_getlist as [wf_list [wf_subseq about_wf_list]].
    exists wf_list. 
    assert (H_pre : agreement_upto_bool k rk (exist (bc_sigmar k) l H) wf_list 0).
    { intros w. spec about_wf_list w. 
      split; intro H_tmp.
      rewrite about_wf_list in H_tmp.
      unfold shear_languager in H_tmp.
      apply andb_prop in H_tmp.
      destruct H_tmp as [H_in H_length].
      split. rewrite Nat.add_0_l.
      apply leb_complete. assumption.
      assumption.
      destruct H_tmp. apply about_wf_list.
      unfold shear_languager.
      rewrite andb_lazy_alt. rewrite H1.
      rewrite Nat.add_0_l in H0. apply leb_correct in H0.
      assumption. } 
    spec H_blink wf_list H_pre. 
    destruct H_blink as [H1 H2].
    split.
    simpl in H2.
    apply functional_extensionality. assumption.
    apply about_llw. split.
    exact wf_subseq. exists (exist (bc_sigmar k) l H). assumption.
Qed.


