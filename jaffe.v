Require Import Arith Bool Nat List Omega Logic.
Import ListNotations. 
From Block 
Require Import pigeonhole lib definitions lemma2choice lemma2nochoice toregularity.

(** Jaffe's pumping condition **)
Definition jaffe_pumpable_with (k : nat) (L : language) :=
  forall (y : word),
    length y = k ->
    exists (u v w : word),
      y = u ++ v ++ w
      /\ v <> []
      /\ forall (h : nat) (z : word),
          L (u ++ napp h v ++ w ++ z) <->
          L (y ++ z).

(** Jaffe's pumping condition explicit with derivatives **) 
Definition jaffe_pumpable_with_hide (k : nat) (L : language) :=
  (forall (y : word),
      length y = k ->
      exists (u v w : word),
        y = u ++ v ++ w
        /\ v <> []
        /\ forall (h : nat),
            derivative_of L (u ++ napp h v ++ w) = derivative_of L y).

Theorem jaffe_pumpable_with_equiv :
  forall (k : nat) (L : language),
    jaffe_pumpable_with k L <-> 
    jaffe_pumpable_with_hide k L. 
Proof.
  intros k L; split; intro H;
  intros y H_length;
  spec H y H_length;
  destruct H as [u [v [w [H_split [H_neq H]]]]];
  exists u, v, w.
  - repeat split. assumption. assumption.
    intro h. spec H h.
    apply language_equality. intro w'.
    spec H w'. unfold derivative_of.
    do 2 rewrite <- app_assoc. assumption.
  - repeat split; try assumption; intro;
      spec H h; rewrite language_equality in H;
        spec H z. apply H. 
    unfold derivative_of.
    do 2 rewrite <- app_assoc. assumption.
    unfold derivative_of in H.
    do 2 rewrite <- app_assoc in H. apply H.
    assumption.
Qed.

(** Proving Regular <-> Jaffe **)
(* Regular -> Jaffe *) 
Theorem reg_to_jaffe :
  forall (L : language),
    regular L ->
    exists (k : nat), jaffe_pumpable_with k L.
Proof.
  intros L H_reg.  
  destruct H_reg as [LD H_reg].  
  exists (S (length LD)). 
  (* For every S (length LD) derivatives you can always
     find a repeat. *)
  (* No prefix x this time! *)
  intros y H_length. 
  assert (H_pigeon := @pigeonhole_principle language).
  (* Heavens forbid we construct the derivative list this way. 
  spec H_pigeon language (map (fun x => derivative_of L x) (map (fun x => [x]) y)) LD. *)
  (* Instead the list we want is more like this: *)
  remember (deriv_list L y (iota 0 (length y))) as LD'.
  assert (about_LD'_length : length LD' = length y).  
  { rewrite HeqLD'. unfold deriv_list, get_prefix_indices.
    rewrite map_length. rewrite length_iota. reflexivity. }
  (* Except we must remember to append the x on, 
     because we are trailing prefixes *) 
  spec H_pigeon LD' LD.
  (* Proving first pigeon obligation *) 
  assert (H_pre :  (forall x : language, In x LD' -> In x LD)).
  { intros l H_mem.
    assert (H_useful := all_derivs_in_list' L LD H_reg LD' (iota 0 (length y)) y).
    assert (In L LD). apply H_reg.
    exists ([] : word). intro w; rewrite app_nil_l; reflexivity.
    spec H_useful H; clear H.
    rewrite HeqLD' in H_mem; spec H_useful l H_mem. exact H_useful. }
  spec H_pigeon H_pre; clear H_pre. 
  (* Proving second pigeon obligation *) 
  assert (H_pre2 : length LD < length LD'). 
  { rewrite HeqLD'.
    unfold deriv_list, get_prefix_indices.
    rewrite map_length, length_iota, H_length.
    omega. }
  spec H_pigeon H_pre2; clear H_pre2.
  (* Now we are in place to use pigeon *) 
  (* The tactic here is inversion. *)
  inversion H_pigeon.
  destruct H as [rep_lang [H_in1 H_in2]]; clear H_pigeon.
  assert (H_in' : In rep_lang (l1 ++ l2)). 
  { apply (in_or_app l1 l2 rep_lang); left; assumption. } 
  rewrite H0 in H_in'.
  assert (H_eq_len : length y = length l1 + length l2).
  { rewrite <- about_LD'_length. rewrite <- H0.
    rewrite app_length. reflexivity. } 
  (* Now we commence derivative label extraction. *)
  apply (In_nth _ _ (get_prefix y L 0)) in H_in1.
  apply (In_nth _ _ (get_prefix y L 0)) in H_in2.
  destruct H_in1 as [i [H_i H_nth_i]];
    destruct H_in2 as [j [H_j H_nth_j]].
  (* Re-expressing the indices in terms of the entire word *) 
  assert (H_rewrite := length_nth_in l1 l2 i (get_prefix y L 0) H_i).
  rewrite <- H_rewrite in H_nth_i; clear H_rewrite.
  rewrite (nth_app_offset l1 l2 j) in H_nth_j.
  rewrite H0 in H_nth_i, H_nth_j.
  rewrite HeqLD' in H_nth_i, H_nth_j. 
  unfold deriv_list, get_prefix_indices in H_nth_i, H_nth_j.
  rewrite (map_nth (get_prefix y L) (iota 0 (length y))) in H_nth_i, H_nth_j.
  unfold get_prefix in H_nth_i, H_nth_j.
  rewrite nth_iota in H_nth_i, H_nth_j.
  rewrite Nat.add_0_l in H_nth_i, H_nth_j.
  2 : omega. 2 : omega.   
  (* The derivatives labels correspond to the word prefixes
     indexed by i and (j + length l1) in word y *)
  exists (firstn i y), (pumpable_block i (length l1 + j) y), (skipn (length l1 + j) y).
  split.
  (* Proving concatenation *)
  rewrite app_assoc. rewrite (left_mid y i (length l1 + j)).
  rewrite firstn_skipn. reflexivity. split. omega.
  rewrite <- about_LD'_length. 
  rewrite <- H0. rewrite app_length. omega.
  (* Proving non-empty middle part *)
  split. intro absurd.
  unfold pumpable_block in absurd.
  apply firstn_nil_inversion in absurd.
  destruct absurd. omega.
  rewrite about_length_skipn in H.
  omega.
  induction h as [|h IHh]; intro z. 
  - (* When we Jaffe-cancel *)
    unfold napp. rewrite app_nil_l.
    assert (H_split_y := firstn_skipn (length l1 + j) y).
    rewrite <- H_split_y at 3.
    rewrite chomp_deriv.
    rewrite <- cat_deriv. rewrite H_nth_i.
    rewrite app_assoc_reverse.
    rewrite (chomp_deriv (firstn (length l1 + j) y ++ skipn (length l1 + j) y ++ z)).
    rewrite <- (cat_deriv (firstn (length l1 + j) y)).
    rewrite plus_comm in H_nth_j; 
      rewrite H_nth_j. easy.  
  - (* When we Jaffe pump, *)
    simpl (* unfold napp *).  
    spec IHh z.
    rewrite chomp_deriv in IHh.
    rewrite <- cat_deriv in IHh.
    rewrite H_nth_i in IHh.
    rewrite <- H_nth_j in IHh.
    rewrite cat_deriv in IHh.
    rewrite <- chomp_deriv in IHh. 
    replace (firstn (j + length l1) y) with
        (firstn i y ++ (pumpable_block i (length l1 + j) y)) in IHh.
    2 : { rewrite left_mid. rewrite plus_comm.
          reflexivity. split. omega.
          rewrite H_length.
          assert (length (l1 ++ l2) = length LD').
          rewrite H0; reflexivity.
          assert (length l1 + j < length (l1 ++ l2)).
          rewrite app_length; omega.
          unfold deriv_list, get_prefix_indices, get_prefix in HeqLD'.
          rewrite app_length in H. 
          omega. }
    rewrite app_assoc_reverse in IHh.
    rewrite app_assoc_reverse. exact IHh.
Qed.

(* Helper lemma for Jaffe -> Regular *)   
Lemma jaffe_helper :
  forall (k : nat) (L : language),
    jaffe_pumpable_with k L ->
    forall x, exists v, length v <= k /\
              derivative_of L x = derivative_of L v.
Proof.
  intros k L H_JP x. 
  remember (length x) as n.
  assert (H_move := Nat.eq_refl (length x)).
  rewrite <- Heqn in H_move at 2. clear Heqn. 
  generalize dependent x.
  induction n as [|n IHn] using strong_induction';
    intros x H_x_length. 
  - exists x. split. rewrite H_x_length; omega.
    reflexivity. 
  - assert (length x < k \/ length x >= k) by omega.
    destruct H as [H_le | H_gt].
    exists x. split. omega. reflexivity.
    spec H_JP (firstn k x). spec H_JP.
    rewrite firstn_length_le. reflexivity. omega. 
    destruct H_JP as [u [v [w [H_split [H_neq H_JP]]]]].
    spec H_JP 0.
    unfold napp in H_JP. 
    assert (derivative_of L (u ++ w) = derivative_of L (firstn k x)).
    apply language_equality. intro z.
    spec H_JP z.
    rewrite app_nil_l in H_JP.
    unfold derivative_of. rewrite <- app_assoc. assumption.
    clear H_JP.
    assert (derivative_of L ((u ++ w) ++ (skipn k x)) =
            derivative_of L x).
    { rewrite <- (firstn_skipn k x) at 2.
      apply (extend_deriv_proper L (u++w)).
      assumption. }
    spec IHn (length ((u ++ w) ++ skipn k x)).
    spec IHn. rewrite app_length.
    rewrite about_length_skipn. 
    rewrite H_x_length.
    assert (length (u ++ w) < k).
    { assert (length (u ++ w) < length (u ++ v ++ w)).
      repeat rewrite app_length.
      rewrite plus_assoc.
      assert (length v > 0).
      destruct v. contradiction.
      simpl; omega. omega.
      rewrite <- H_split in H1.
      rewrite firstn_length_le in H1. 
      assumption. assumption. }
    omega. 
    spec IHn (u++w++skipn k x).
    spec IHn. rewrite app_assoc. reflexivity.
    destruct IHn as [v' [v'_length v'_deriv]].
    exists v'. rewrite <- app_assoc in H0.
    split. assumption. rewrite <- H0. rewrite v'_deriv.
    reflexivity.
Qed. 

Theorem jaffe_to_reg :
  forall (k : nat) (L : language),
    jaffe_pumpable_with k L ->
    regular L. 
Proof. 
  intros k L H_JP.
  rewrite jaffe_pumpable_with_equiv in H_JP. 
  (* We're going to try for something *)
  exists (map (fun w => derivative_of L w) (generate_words_upto k)).
  intro l; split; intro H.
  - unfold is_deriv.
    rewrite in_map_iff in H.
    
destruct H as [x [x_label x_length]].
    exists x. 
    apply language_equality.
    symmetry; assumption.
  - (* This is the tricky direction, proving that all derivatives of L 
       are indeed in this list of derivatives with short labels *)
    rewrite in_map_iff.
    unfold is_deriv in H.
    destruct H as [x H].
    assert (length x <= k \/ length x > k) by omega.
    destruct H0 as [x_le | x_gt].
    + (* In the case that x is sufficiently short *)
      exists x. split. symmetry. 
      rewrite language_equality. assumption.
      apply generate_words_upto_correct. assumption. 
    + (* In the case that x is too long, we need to find an equivalent *)
      assert (H_useful := jaffe_helper k L).
      spec H_useful. rewrite jaffe_pumpable_with_equiv.
      assumption. spec H_useful x.
      destruct H_useful as [v [v_length v_eq]].
      exists v. split. apply language_equality in H.
      rewrite H. symmetry; assumption.
      rewrite generate_words_upto_correct. assumption.
Qed.
(* This uses prop_ext and functional_extensionality *)

      
      
