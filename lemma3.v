Require Import List Logic Nat Omega ListDec.
Import ListNotations.
From Block  
Require Import finite lib definitions ramsey lemma2choice. 

(* ***************** *)
(* **** Lemma 3 **** *)
(* ***************** *)
(* "If L is in C_k then so is L_s for any s in the alphabet" *)
Lemma lemma3 : forall (k : block_pumping_constant) (L : language),
    block_cancellable_matching_with k L ->
    forall (Ld : language) (x : word), is_derivative L Ld x -> block_cancellable_matching_with k Ld. 
Proof. 
  intros k L H_BC Ld x H_Lx w bps.
  assert (H_non_empty :=  about_bps_nonempty k w bps). 
  (* Case analysis on w at this step, absurdo the empty string *) 
  destruct w.
  - (* When the word is empty, explosion occurs *)
    spec H_BC ([] : word) bps.
    destruct H_BC as [bp1 [bp2 [H_lt H_BC]]].
    destruct_bps bps about_bps.
    destruct about_bps as [H_length [H_incr H_last]].
    unfold length in H_last; inversion H_last.
    assert (H_useful := about_incr_length_last k definitions.d bps). 
    spec H_useful H_non_empty H_length H_incr.
    rewrite H0 in H_useful.
    destruct k as [k about_k]. unfold p_predicate in about_k.
    simpl in H_useful; omega.
  - (* We need to basically argue that the derivative word's breakpoints
       set can also be breakpoints for the larger word. *)
    (* bps is a breakpoint set for some random word in the derivative. *)
    (* We need to extract two breakpoints, and then manipulate them
       into breakpoints for the original word by incrementing by length. *)
    (** Setting the strong induction on word length requires some proof engineering **)
    remember (length x) as n.  
    assert (H_move := Nat.eq_refl (length x)).
    rewrite <- Heqn in H_move at 2. clear Heqn. 
    generalize dependent x. 
    (** Strong induction on word length! **)
    induction n as [|n IHn] using strong_induction; intros x H_Lx H_x_length. 
    + (* When the derivative marker is epsilon, Ld = L *)
      (* So we use exactly the same breakpoint set, no shifting! *)
      apply length_zero_iff_nil in H_x_length.
      subst x. 
      spec H_BC (t::w) bps. 
      destruct H_BC as [bp1 [bp2 [H_lt H_BC]]].
      exists bp1, bp2.
      split. assumption.
      assert (H_Lx_copy := H_Lx);
      spec H_Lx (t::w);
      spec H_Lx_copy (firstn bp1 (t :: w) ++ skipn bp2 (t :: w));
      rewrite app_nil_l in *.
      split; intro H.
      ++ apply H_Lx; apply H_BC; apply H_Lx_copy; assumption. 
      ++ apply H_Lx_copy; apply H_BC; apply H_Lx; assumption.
         (* Done with base case! *)
    + (* I need to shift all the breakpoints in bps rightwards by length x *) 
      remember (map (plus n) bps) as shifted_bps.
      assert (H_guarantee := shifted_gt bps n). 
      (* Now I need to show that these can also make a set of breakpoints *)
      assert (about_shifted_bps : breakpoint_set_predicate shifted_bps (x++t::w) k).
      { destruct_bps bps about_bps. 
        destruct about_bps as [H_length [H_incr H_last]].
        subst shifted_bps. 
        split.
        rewrite map_length. assumption.
        split. now apply (about_plus_increasing n).
        rewrite app_length. rewrite plus_comm.
        assert (H_last_copy := H_last). 
        rewrite about_last_nth in H_last_copy.
        rewrite about_last_nth. 
        rewrite map_length.
        (* Switch the default variable *) 
        replace (nth (length bps - 1) (map (add n) bps) definitions.d)
          with (nth (length bps - 1) (map (add n) bps) (add n definitions.d)).
        2 : { eapply (@nth_indep nat). rewrite map_length.
              destruct k as [k about_k]; unfold p_predicate in about_k.
              rewrite H_length. simpl; omega. }
        rewrite map_nth. rewrite unfold_length_S. simpl; omega. } 
      (* Now we have the breakpoint set to feed to BC(k, L) *) 
      spec H_BC (x++t::w) (exist (fun l => breakpoint_set_predicate l (x++t::w) k) shifted_bps about_shifted_bps).   
      (* Now we can get the breakpoints from BC(k, L) *)
      destruct H_BC as [bp1 [bp2 [H_lt H_BC]]].
      destruct_bp bp1 about_bp1; destruct_bp bp2 about_bp2. 
      (* Now we want to argue that shifting them back,
       these again-shifted breakpoints are also breakpoints for bps *)
      assert (about_bp1' : breakpoint_predicate (bp1-n) k (t::w) bps). 
      { (* Proving that the first one still is *)
        unfold breakpoint_predicate.
        unfold breakpoint_predicate in about_bp1.
        simpl in *.
        rewrite Heqshifted_bps in about_bp1.
        (* Now we have something that looks straightforward *)
        (* In nat, as long as you're adding then minusing you're fine. *)
        apply (in_map (fun a => a - n) (map (add n) bps) bp1) in about_bp1.
        assert ((map (fun a : nat => a - n) (map (add n) bps)) = bps).
        { rewrite map_map.
          now apply map_plus_minus. } 
        rewrite H in about_bp1. exact about_bp1. }
      assert (about_bp2' : breakpoint_predicate (bp2-n) k (t::w) bps).  
      { (* Proving that the second one still is *)
        unfold breakpoint_predicate.
        unfold breakpoint_predicate in about_bp2.
        simpl in *.
        rewrite Heqshifted_bps in about_bp2.
        (* Now we have something that looks straightforward *)
        (* In nat, as long as you're adding then minusing you're fine. *)
        apply (in_map (fun a => a - n) (map (add n) bps) bp2) in about_bp2.
        assert ((map (fun a : nat => a - n) (map (add n) bps)) = bps).
        { rewrite map_map.
          now apply map_plus_minus. } 
        rewrite H in about_bp2; exact about_bp2. }
      (* Proving the extra obligation for nats and zeroes *)
      exists (exist _ (bp1 - n) about_bp1').
      exists (exist _ (bp2 - n) about_bp2').
    simpl in *. split.
    apply lt_minus_n. assumption.
    { apply H_guarantee. rewrite <- Heqshifted_bps.
      unfold breakpoint_predicate in about_bp1.
      simpl in about_bp1; assumption. }
    assert (H_keep1 : bp1 >= n). 
    { apply H_guarantee. rewrite <- Heqshifted_bps.
      unfold breakpoint_predicate in about_bp1.
      simpl in about_bp1; assumption. }
    assert (H_keep2 : bp2 >= n). 
    { apply H_guarantee. rewrite <- Heqshifted_bps.
      unfold breakpoint_predicate in about_bp2.
      simpl in about_bp2; assumption. }
    (* Somewhere I needed to reassure the proof context that all bp1's are
       greater than n *)
    assert (H_Lx_copy := H_Lx). 
    clear -H_BC H_Lx H_Lx_copy H_x_length H_keep1 H_keep2.
    subst n.
    assert (H_useful := about_deriv_eq bp1 bp2 x (t::w) H_keep1 H_keep2).
    split; intro H_in. 
      ++ spec H_Lx (t::w). apply H_Lx.
         apply H_BC.
         clear H_BC H_Lx. 
         rewrite <- H_useful. 
         spec H_Lx_copy (firstn (bp1 - length x) (t :: w) ++ skipn (bp2 - length x) (t :: w)).
         apply H_Lx_copy; assumption. 
      ++ spec H_Lx (t::w).
         apply H_Lx in H_in. clear H_Lx.
         apply H_BC in H_in.
         spec H_Lx_copy (firstn (bp1 - (length x)) (t :: w) ++ skipn (bp2 - (length x)) (t :: w)).
         apply H_Lx_copy.
         rewrite H_useful; assumption.
Qed.

Lemma lemma3' : forall (k : block_pumping_constant) (L : language),
    block_cancellable_matching_with k L ->
    forall (Ld : language), is_deriv L Ld -> block_cancellable_matching_with k Ld. 
Proof. 
  intros k L H_bc. 
  assert (H_useful := lemma3 k L H_bc).
  intros Ld H_deriv.
  destruct H_deriv as [x H_deriv].
  spec H_useful Ld x.
  spec H_useful. red. intros.
  spec H_deriv w. tauto. assumption.
Qed.

(* A dependent version of lemma3 *)
Lemma lemma3_dep : forall (k : block_pumping_constant) (L : {l | bc_sigma k l}),
    forall (Ld : language) (x : word), is_derivative (proj1_sig L) Ld x ->
                                  block_cancellable_matching_with k Ld.
Proof.
  intros k L_dep L_d x H_deriv.
  assert (H_useful := lemma3 k (proj1_sig L_dep)).
  destruct L_dep as [L_dep H_BC].
  spec H_useful H_BC L_d x.
  spec H_useful H_deriv. assumption. 
Qed.
