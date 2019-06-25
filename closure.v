Require Import PeanoNat Le Gt Minus Bool Lt List Arith Nat Omega ExtensionalityFacts Logic.
Import ListNotations.
From Block  
Require Import lib definitions ramsey.

(* ***************** *)
(* **** Closure **** *)
(* ***************** *)

(* Closure properties of block-pumpable languages *)
Lemma paranoia : forall {X : Type} (P : Prop) (Q : X -> Prop),
    (forall x : X, P -> Q x) <-> (P -> forall x, Q x).
Proof.
  intros; split; intros.
  spec H x H0. assumption.
  spec H H0. 
  exact (H x).
Qed.

(* Paper states result for two languages with the same pumping constant! *)
Lemma bp_intersect_closure : forall (l1 l2 : language) (k1: block_pumping_constant),
    block_pumpable_with k1 l1 ->
    block_pumpable_with k1 l2 ->
    exists k' : block_pumping_constant,
      block_pumpable_with k' (intersection_lang l1 l2). 
Proof.
  intros l1 l2 k H_L H_L'.
  assert (H_ramsey := Theorem_of_Ramsey_duo_prop k).
  destruct H_ramsey as [k' [H_lt H_ramsey]]. 
  exists k'.
  intros w H_mem bps.
  spec H_ramsey w bps (is_pump l1 w). 
  destruct H_mem as [H_mem H_mem'].
  destruct H_ramsey as [bps' [H_sublist H_ramsey]].
  spec H_L w H_mem bps'; spec H_L' w H_mem' bps'.
  destruct H_ramsey as [left | right].
  + (* case1 : is pump for L1 *)
    destruct H_L' as [bp1 [bp2 H_L']].
    spec left bp1 bp2. 
    destruct H_L' as [H_lt' H_L']; spec left H_lt'.
    destruct bp1 as [bp1 about_bp1];
      destruct bp2 as [bp2 about_bp2].
    assert (breakpoint_predicate bp1 k' w bps).
    { unfold breakpoint_predicate.
        unfold sublist in H_sublist;
        spec H_sublist bp1 about_bp1;
        assumption. }
    assert (breakpoint_predicate bp2 k' w bps).
    { unfold breakpoint_predicate.
        unfold sublist in H_sublist;
        spec H_sublist bp2 about_bp2;
        assumption. }
    exists (exist _ bp1 H).
    exists (exist _ bp2 H0).
    split; simpl. assumption.
    intro m; unfold intersection_lang; split.
    unfold is_pump in left. simpl in *.
    spec left m. assumption. 
    spec H_L' m. exact H_L'.
  + (* case2 : is not pump for L1 *)
    destruct H_L as [bp1 [bp2 H_L]].
    spec right bp1 bp2. clear H_lt.
    destruct H_L as [H_lt H_L]; spec right H_lt.
    unfold is_pump in right. 
    exfalso. apply right.
    intro m. 
    exact (H_L m). 
Qed.
(* This uses LEM *) 

Lemma bp_union_closure : forall (l1 l2 : language) (k : block_pumping_constant),
    block_pumpable_with k l1 ->
    block_pumpable_with k l2 ->
    exists k' : block_pumping_constant,
      block_pumpable_with k' (union_lang l1 l2).
Proof.
  intros l1 l2 k H_L H_L'.
  assert (H_ramsey := Theorem_of_Ramsey_duo_prop k).
  destruct H_ramsey as [k' [_ H_ramsey]]. 
  exists k'.
  intros w H_mem bps.
  spec H_ramsey w bps (is_pump l1 w).
  destruct H_ramsey as [bps' [H_sublist [left | right]]]. 
  ++ (* case1 : is pump for L1 *)
     destruct H_mem as [H_mem | H_mem'].
    +++ spec H_L w H_mem bps'.
        destruct H_L as [bp1 [bp2 [H_lt H_L]]].
        spec left bp1 bp2 H_lt; unfold is_pump in left.
        assert (breakpoint_predicate bp1 k' w bps).
        { unfold breakpoint_predicate.
          destruct bp1 as [bp1 about_bp1];
            unfold sublist in H_sublist;
            spec H_sublist bp1 about_bp1;
            assumption. }
        assert (breakpoint_predicate bp2 k' w bps).
        { unfold breakpoint_predicate.
          destruct bp2 as [bp2 about_bp2];
            unfold sublist in H_sublist;
            spec H_sublist bp2 about_bp2;
            assumption. }
        destruct bp1 as [bp1 about_bp1];
          destruct bp2 as [bp2 about_bp2].
        exists (exist _ bp1 H).
        exists (exist _ bp2 H0).
        split; simpl in *. exact H_lt.
        intro m.
        left; spec H_L m; assumption.
    +++ spec H_L' w H_mem' bps'.
        destruct H_L' as [bp1 [bp2 [H_lt H_L']]].
        spec left bp1 bp2 H_lt; unfold is_pump in left.
        assert (breakpoint_predicate bp1 k' w bps).
        { unfold breakpoint_predicate.
          destruct bp1 as [bp1 about_bp1];
            unfold sublist in H_sublist;
            spec H_sublist bp1 about_bp1;
            assumption. }
        assert (breakpoint_predicate bp2 k' w bps).
        { unfold breakpoint_predicate.
          destruct bp2 as [bp2 about_bp2];
        unfold sublist in H_sublist;
        spec H_sublist bp2 about_bp2;
        assumption. }
        destruct bp1 as [bp1 about_bp1];
          destruct bp2 as [bp2 about_bp2].
        exists (exist _ bp1 H).
        exists (exist _ bp2 H0).
        split; simpl in *. exact H_lt.
        intro m.
        right; spec H_L' m; assumption.
  ++ (* case1 : is not pump for L1 *)
    destruct H_mem as [H_mem | H_mem'].
    +++ spec H_L w H_mem bps'.
        destruct H_L as [bp1 [bp2 [H_lt H_L]]].
        spec right bp1 bp2 H_lt; unfold is_pump in right.
        assert (breakpoint_predicate bp1 k' w bps).
        { unfold breakpoint_predicate.
          destruct bp1 as [bp1 about_bp1];
            unfold sublist in H_sublist;
            spec H_sublist bp1 about_bp1;
            assumption. }
        assert (breakpoint_predicate bp2 k' w bps).
        { unfold breakpoint_predicate.
          destruct bp2 as [bp2 about_bp2];
            unfold sublist in H_sublist;
            spec H_sublist bp2 about_bp2;
            assumption. }
        destruct bp1 as [bp1 about_bp1];
          destruct bp2 as [bp2 about_bp2].
        exists (exist _ bp1 H).
        exists (exist _ bp2 H0).
        split; simpl in *. exact H_lt.
        intro m.
        left; spec H_L m; assumption. 
    +++ spec H_L' w H_mem' bps'.
        destruct H_L' as [bp1 [bp2 [H_lt H_L']]].
    destruct bp1 as [bp1 about_bp1];
      destruct bp2 as [bp2 about_bp2].
    assert (breakpoint_predicate bp1 k' w bps).
    { unfold breakpoint_predicate.
        unfold sublist in H_sublist;
        spec H_sublist bp1 about_bp1;
        assumption. }
    assert (breakpoint_predicate bp2 k' w bps).
    { unfold breakpoint_predicate.
        unfold sublist in H_sublist;
        spec H_sublist bp2 about_bp2;
        assumption. }
    exists (exist _ bp1 H).
    exists (exist _ bp2 H0).
    split; simpl in *. assumption.
    intro m. spec H_L' m; right; assumption.
Qed.
(* This uses LEM *)
                                                                           
Lemma bp_concat_closure : forall (l1 l2 : language) (k : block_pumping_constant),
    block_pumpable_with k l1 ->
    block_pumpable_with k l2 ->
    exists k' : block_pumping_constant,
      block_pumpable_with k' (concat_lang l1 l2). 
Proof.
  intros L L' k H_L H_L'.
  (** Constructing block pumping constant **) 
  assert (p_predicate (k+k)).
  { destruct k as [k about_k]; unfold p_predicate in *; simpl; omega. } 
  (* The new block pumping constant is 2k *)  
  exists (exist _ (k+k) H); intros w H_mem bps.
  destruct H_mem as [w1 [w2 [H_split [H_mem1 H_mem2]]]].
  (** Case analysis on breakpoints position in word **) 
  (* Either all of w1's breakpoints are in itself,
     or all of w2's breakpoints are in itself *) 
  assert (nth (k-1) bps definitions.d <= (length w1) \/ (length w1) < nth (k-1) bps definitions.d) by omega.
  (* Bookkeeping for later *)  
  assert (H_split_bps := firstn_skipn k bps).
  assert (H_useful := sublist_preserves_increasing bps
                                                   (firstn k bps)
                                                   (skipn k bps)
                                                   definitions.d). 
  symmetry in H_split_bps; spec H_useful H_split_bps. 
  (* With all this information in place, destruct! *) 
  destruct H0 as [left | right]. 
  - (* In the case that all of w1's breakpoints are in itself *)
    (** Constructing breakpoint set for left case **) 
    assert (about_bps1 : breakpoint_set_predicate (firstn k bps) w1 k). 
    { destruct_bps bps about_bps.
      destruct about_bps as [H_length [H_incr H_last]].
      spec H_useful H_incr; destruct H_useful as [H_incr_left _].
      unfold breakpoint_set_predicate; repeat split.
      + rewrite firstn_length.
        rewrite H_length. 
        apply min_plus.
      + exact H_incr_left.
      + rewrite about_last_nth in *.
        rewrite firstn_length; rewrite H_length; rewrite min_plus.
        (* Replacing firstn bps with bps *)
        replace (nth (k-1) (firstn k bps) definitions.d)
          with (nth (k-1) bps definitions.d).
        2 : { assert (H_useful := about_firstn_app (k - 1)
                                                   (firstn k bps)
                                                   (skipn k bps)).
              assert (H_obv : k - 1 <= length (firstn k bps)).
              { rewrite firstn_length;
                  rewrite H_length;
                  rewrite min_plus; omega. } 
              spec H_useful H_obv; clear H_obv.
              assert (H_useful' := length_nth_in (firstn k bps)
                                                 (skipn k bps)
                                                 (k - 1)
                                                 definitions.d).
              assert (H_obv : k - 1 < length (firstn k bps)).
              { rewrite firstn_length. rewrite H_length.
                rewrite min_plus.
                unfold p_predicate in H; omega. }
              spec H_useful' H_obv; clear H_obv.
              rewrite <- H_split_bps in H_useful'.
              assumption. }
        exact left. } 
    (** Passing breakpoint set to L1 **) 
    remember (exist (fun l => breakpoint_set_predicate l w1 k) (firstn k bps) about_bps1) as bps1.
    spec H_L w1 H_mem1 bps1.
    (** Acquiring breakpoints from L1 **) 
    destruct H_L as [bp1 [bp2 [H_lt H_L]]].
    (** Constructing new breakpoints for concat language **)
    assert (about_bp1 : breakpoint_predicate bp1 (exist _ (k+k) H) w bps).
    { destruct_bp bp1 about_bp1.
      subst bps1. 
      unfold breakpoint_predicate in *; simpl.
      rewrite H_split_bps.
      apply in_or_app. left.
      assumption. }
    assert (about_bp2 : breakpoint_predicate bp2 (exist _ (k+k) H) w bps).
    { destruct_bp bp2 about_bp2.
      subst bps1. 
      unfold breakpoint_predicate in *; simpl.
      rewrite H_split_bps.
      apply in_or_app. left.
      assumption. }
    (** Supplying breakpoints to concat language **) 
    exists (exist (fun i => breakpoint_predicate i (exist (p_predicate) (k+k) H) w bps) bp1 about_bp1).
    exists (exist (fun i => breakpoint_predicate i (exist (p_predicate) (k+k) H) w bps) bp2 about_bp2).
    split. simpl; assumption.
    intro m; simpl in *.
    (** Pumping the left word **) 
    spec H_L m.
    exists (firstn bp1 w1 ++ napp m (pumpable_block bp1 bp2 w1) ++ skipn bp2 w1), w2; split. 
    2 : split; assumption.
    do 2 rewrite <- app_assoc.
    (** Piecewise showing that result word is in concat language **) 
    (* Chunk the first *)
    replace (firstn bp1 w) with (firstn bp1 w1). 
    2 : { rewrite H_split. 
          rewrite (about_firstn_app bp1 w1 w2). reflexivity.
          apply about_bp_length. }
    (* Chunk the second *)
    replace (napp m (pumpable_block bp1 bp2 w)) with
        (napp m (pumpable_block bp1 bp2 w1)).
    2 : { rewrite H_split. unfold pumpable_block.
          rewrite skipn_app_in.
          rewrite (about_firstn_app (bp2 - bp1) (skipn bp1 w1) w2).
          reflexivity.
          rewrite about_length_skipn.
          assert (bp2 <= length w1) by apply about_bp_length.
          omega.
          assert (bp2 <= length w1) by apply about_bp_length.
          omega. }
    (* Chunk the third *)
    (* This is the place to do case analysis on the position of bp2! *)
    assert (H_disj := about_bp_length k w1 bps1 bp2).
    apply le_lt_or_eq in H_disj.
    destruct H_disj as [trivial | eq].
    -- (* In the non-rightmost case, *) 
       replace (skipn bp2 w) with (skipn bp2 w1 ++ w2).
       2 : { rewrite <- skipn_app_in. 
             rewrite H_split; reflexivity.
             (* I need this to be strictly less than... *)
             exact trivial. } 
       reflexivity.
    -- (* In the rightmost case, *)
      rewrite eq at 2 4. 
      rewrite H_split. rewrite skipn_length.
      rewrite skipn_app_first. auto (* Getting rid of random nil app *). 
      reflexivity.
  - (* In the case that all of w2's breakpoints are in itself *)
    (** Constructing breakpoint set for right case **)
    (* An important bit of imformation about bps2 for later *)
    assert (H_impt : forall x : nat, In x (skipn k bps) -> x >= length w1).
    intros n H_in_n.
    apply (In_nth _ _ definitions.d) in H_in_n. 
    destruct H_in_n as [i [i_lt about_i]]. 
    rewrite (nth_app_offset (firstn k bps) (skipn k bps) i definitions.d) in about_i. 
    rewrite <- H_split_bps in about_i.
    rewrite firstn_length in about_i.
    { destruct_bps bps about_bps;
        destruct about_bps as [H_length [H_incr H_last]].
      rewrite H_length in about_i; rewrite min_plus in about_i. 
      spec H_incr (k - 1) (i + k). 
      assert (H_obv : k - 1 < i + k < length bps).
      { rewrite H_length. unfold p_predicate in H. 
        rewrite plus_comm. rewrite about_length_skipn in i_lt.
        rewrite H_length in i_lt. omega. }
      spec H_incr H_obv; clear H_obv. 
      omega. } 
    assert (about_bps2 : breakpoint_set_predicate (minus_map (length w1) (skipn k bps)) w2 k).
      { destruct_bps bps about_bps;
          destruct about_bps as [H_length [H_incr H_last]].
        spec H_useful H_incr; destruct H_useful as [_ H_incr_right]. 
        unfold breakpoint_set_predicate; repeat split.
        + unfold minus_map; rewrite map_length.
          rewrite about_length_skipn. 
          rewrite H_length. 
          omega. 
        + apply about_minus_increasing.
          assert (H_useful := sublist_preserves_increasing bps
                                                           (firstn k bps)
                                                           (skipn k bps)
                                                           definitions.d).
          exact H_incr_right.  
          rewrite (nth_app_offset (firstn k bps) (skipn k bps) 0 definitions.d). 
          rewrite Nat.add_0_l.
          rewrite firstn_length. rewrite H_length; rewrite min_plus.
          rewrite <- H_split_bps.
          spec H_incr (k-1) k.
          assert (H_obv : k - 1 < k < length bps).
          { rewrite H_length; unfold p_predicate in H; omega. }
          spec H_incr H_obv; clear H_obv.
          omega. 
        + rewrite about_last_nth in *.  
          unfold minus_map at 1; rewrite map_length;
            rewrite about_length_skipn;
            rewrite H_length;
            replace (k+k-k-1) with (k-1) by omega.
          rewrite (nth_indep (minus_map (length w1) (skipn k bps))
                             definitions.d
                             (reverse_arg_minus (length w1) definitions.d)). 
          rewrite about_minus_nth. 
          2 : { unfold minus_map; rewrite map_length.
                rewrite about_length_skipn. rewrite H_length.
                unfold p_predicate in H. omega. }
          replace (length w2) with (length w - length w1).
          2 : { rewrite H_split. rewrite app_length. omega. }
          apply Nat.sub_le_mono_r.
          rewrite (nth_app_offset (firstn k bps) (skipn k bps) (k-1) definitions.d).
          rewrite <- H_split_bps.
          rewrite firstn_length.
          rewrite H_length; rewrite min_plus.
          rewrite H_length in H_last.
          rewrite plus_comm.
          rewrite Nat.add_sub_assoc.
          exact H_last.
          unfold p_predicate in H; omega. } 
      (** Passing breakpoint set to L2 **) 
      remember (exist (fun l => breakpoint_set_predicate l w2 k)
                      (minus_map (length w1) (skipn k bps))
                      about_bps2) as bps2.  
      spec H_L' w2 H_mem2 bps2.
      (** Acquiring breakpoints from L2 **) 
      destruct H_L' as [bp1 [bp2 [H_lt H_L']]].
      (* Getting some information about bp1, bp2 *)
      destruct_bp bp1 about_bp1; destruct_bp bp2 about_bp2.
      unfold breakpoint_predicate in about_bp1, about_bp2.
      subst bps2. simpl in *.
      apply (In_nth _ _ definitions.d) in about_bp1;
        apply (In_nth _ _ definitions.d) in about_bp2.
      destruct about_bp1 as [i [i_lt about_i]];
        destruct about_bp2 as [j [j_lt about_j]].
      unfold minus_map, reverse_arg_minus in i_lt, j_lt; rewrite map_length in i_lt, j_lt. 
      (** Constructing new breakpoints for the concat language **)
      (* Maybe if we voice these breakpoints differently *)
      assert (about_bp1 : breakpoint_predicate (bp1 + length w1)
                                               (exist p_predicate (k+k) H)
                                               w
                                               bps). 
      { unfold breakpoint_predicate.
        rewrite H_split_bps.
        apply in_or_app; right.
        assert (H_escape := map_minus_plus (skipn k bps) (length w1)). 
        assert (H_step := in_map (fun x => x + length w1) (minus_map (length w1) (skipn k bps)) bp1).
        rewrite <- about_i in H_step at 1. 
        assert (H_pre : In (nth i (minus_map (length w1) (skipn k bps)) definitions.d)
                           (minus_map (length w1) (skipn k bps))).
        { apply nth_In. unfold minus_map, reverse_arg_minus; rewrite map_length.
          assumption. }
        spec H_step H_pre; clear H_pre.
        unfold minus_map, reverse_arg_minus in H_step.
        rewrite map_map in H_step.
        spec H_escape H_impt. 
        rewrite <- H_escape. assumption.  } 
      assert (about_bp2 : breakpoint_predicate (bp2 + length w1)
                                               (exist p_predicate (k+k) H)
                                               w bps).
      { unfold breakpoint_predicate.
        rewrite H_split_bps.
        apply in_or_app; right.
        assert (H_escape := map_minus_plus (skipn k bps) (length w1)). 
        assert (H_step := in_map (fun x => x + length w1) (minus_map (length w1) (skipn k bps)) bp2).
        rewrite <- about_j in H_step at 1. 
        assert (H_pre : In (nth j (minus_map (length w1) (skipn k bps)) definitions.d)
                           (minus_map (length w1) (skipn k bps))).
        { apply nth_In. unfold minus_map, reverse_arg_minus; rewrite map_length.
          assumption. }
        spec H_step H_pre; clear H_pre.
        unfold minus_map, reverse_arg_minus in H_step.
        rewrite map_map in H_step.
        spec H_escape H_impt. 
        rewrite <- H_escape. assumption. }
      (** Supplying breakpoints to concat language **) 
      exists (exist (fun i => breakpoint_predicate i (exist (p_predicate) (k+k) H) w bps) (bp1 + length w1) about_bp1).
      exists (exist (fun i => breakpoint_predicate i (exist (p_predicate) (k+k) H) w bps) (bp2 + length w1) about_bp2).
      simpl in *. 
      split. omega. 
      intro m. 
      (** Pumping the right word **) 
      spec H_L' m.
      exists w1, (firstn bp1 w2 ++ napp m (pumpable_block bp1 bp2 w2) ++ skipn bp2 w2); split. 
      2 : split; assumption.
      (** Piecewise showing that result word is in concat language **) 
      (* Chunk the first *)
      replace (firstn (bp1 + length w1) w) with (w1 ++ firstn bp1 w2). 
      2 : { rewrite H_split. 
            rewrite <- firstn_app_2.
            rewrite plus_comm; reflexivity. }
      (* Chunk the second *)
      replace (napp m (pumpable_block (bp1 + length w1) (bp2 + length w1) w)) with
          (napp m (pumpable_block bp1 bp2 w2)). 
      2 : {  unfold pumpable_block.
             replace (skipn bp1 w2) with (skipn (bp1 + length w1) w).
             2 : { rewrite H_split.
                   rewrite plus_comm.
                   rewrite skipn_app_out. 
                   replace (length w1 + bp1 - length w1) with bp1.
                   reflexivity. omega. omega. }
             replace (bp2 + length w1 - (bp1 + length w1)) with (bp2 - bp1) by omega.
             reflexivity. }
      (* Chunk the third *)
      replace (skipn (bp2 + length w1) w) with (skipn bp2 w2). 
      2 : { rewrite H_split. rewrite skipn_app_out.
            replace (bp2 + length w1 - length w1) with bp2 by omega. reflexivity.
            omega. }
      rewrite app_assoc_reverse. reflexivity.
Qed.

