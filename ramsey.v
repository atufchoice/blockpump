Require Import List Logic Nat Arith Bool Omega Classical.
Require Import Compare_dec EqNat Decidable ListDec FinFun. 
Require Fin. 
Import ListNotations.
From Block   
Require Import lib definitions.

Definition Ramsey_of {X : Type} (r s : nat) (H_r : r > 0) (H_s : s > 0) (rk : nat) (d : X) :=
  forall l : list X, length l = rk ->
                forall f : X -> X -> bool,
                (exists bl : list X, length bl = r /\ subseq bl l /\
                               forall i j : nat, i < j < r ->
                                          f (nth i bl d) (nth j bl d) = true)
                \/ (exists bl : list X, length bl = s /\ subseq bl l /\ 
                                  forall i j : nat, i < j < s ->
                                             f (nth i bl d) (nth j bl d) = false). 

Definition Ramsey_of_prop {X : Type} (r s : nat) (H_r : r > 0) (H_s : s > 0) (rk : nat) (d : X) :=
  forall l : list X, length l = rk ->
                forall P : X -> X -> Prop,
                (exists bl : list X, length bl = r /\ subseq bl l /\
                               forall i j : nat, i < j < r ->
                                          P (nth i bl d) (nth j bl d))
                \/ (exists bl : list X, length bl = s /\ subseq bl l /\ 
                                  forall i j : nat, i < j < s ->
                                             ~ P (nth i bl d) (nth j bl d)). 

Lemma one : 1 > 0. Proof. omega. Qed. 

Theorem Ramsey_of_one {X : Type} :
  forall (k : nat) (H_k : k > 0) (d : X),
    Ramsey_of 1 k one H_k 1 d /\
    Ramsey_of k 1 H_k one 1 d.
Proof.
  intros k H_k d; split; red; repeat split; try omega; intros l H_l f. 
  - left. exists l. split. assumption.
    split. apply subseq_refl. intros. omega. 
  - right. exists l. split. assumption.
    split. apply subseq_refl. intros. omega.
Qed.

Theorem Ramsey_of_one_prop {X : Type} :
  forall (k : nat) (H_k : k > 0) (d : X),
    Ramsey_of_prop 1 k one H_k 1 d /\
    Ramsey_of_prop k 1 H_k one 1 d.
Proof.
  intros k H_k d; split; red; repeat split; try omega; intros l H_l f. 
  - left. exists l. split. assumption.
    split. apply subseq_refl. intros. omega. 
  - right. exists l. split. assumption.
    split. apply subseq_refl. intros. omega.
Qed.

Theorem Ramsey_inductive_step {X : Type} :
  forall (r s : nat) (H_r : r > 0) (H_s : s > 0) (d : X),
  exists rk : nat,
    Ramsey_of r s H_r H_s rk d.
Proof.
  intros r s.
  remember (r + s) as k.
  revert r s Heqk. 
  induction k as [|k IHk] using strong_induction; intros.
  - symmetry in Heqk; apply plus_is_O in Heqk.
    destruct Heqk; subst. inversion H_r.
  - destruct r as [|r]. inversion H_r.
    destruct s as [|s]. inversion H_s.
    destruct r as [|r].
    (* Pseudo base case, when r = 1 *) 
    exists 1. 
    apply (Ramsey_of_one (S s) H_s d).
    (* Pseudo base case, when s = 1 *)
    destruct s as [|s].
    exists 1. 
    apply (Ramsey_of_one (S (S r)) H_r d).
    (* Finally, everything is big enough *) 
    destruct k. omega. destruct k. omega. 
    (* Both (S r) and (S s) are greater than or equal to 1, 
       and therefore (S (S k)) is greater than or equal to two *)
    (* Reminder : r = S r, s = S s, k = S (S k) *) 
    spec IHk (S k). 
    spec IHk. omega.
    assert (IHk_copy := IHk).
    spec IHk (S r) (S (S s)).
    spec IHk_copy (S (S r)) (S s).
    spec IHk. omega. spec IHk_copy. omega.
    assert (H_pre1 : S r > 0) by omega.
    spec IHk H_pre1 H_s.
    spec IHk_copy H_r.
    assert (H_pre2 : S s > 0) by omega.
    spec IHk_copy H_pre2.
    spec IHk d. spec IHk_copy d.
    destruct IHk as [rk1 IHk1].
    destruct IHk_copy as [rk2 IHk2].
    exists (rk1 + rk2); red; intros l H_l f. 
    red in IHk1, IHk2.
    destruct l as [|v l_rest]. 
    (* Inversioning the base case list *)
    + unfold length in H_l. symmetry in H_l.
      apply plus_is_O in H_l. destruct H_l; subst.
      spec IHk1 ([] : list X).
      spec IHk1. reflexivity.
      spec IHk1 f. destruct IHk1;
      destruct H as [bl_absurd [absurd_length [absurd_subseq _]]];
      assert (bl_absurd = []) by (apply (subseq_nil_nil); assumption);
      subst; simpl in absurd_length; inversion absurd_length.
    + (* Now we have a pivot vertex *)
      remember (filter (fun n => f v n) l_rest) as M. 
      remember (filter (fun n => negb (f v n)) l_rest) as N.
      assert (length M + length N = length l_rest).
      { subst; apply filter_length. }
      simpl in H_l.
      assert (length M >= rk1 \/ length N >= rk2) by omega. 
      destruct H0 as [red | blue]. 
      * (* In the case that M has a red K_(S s) *)
        clear IHk2.
        assert (H_get := get_subseq M rk1 red).
        assert (H_trans : subseq M l_rest) by (subst M; apply (filter_subseq_correct')).
        destruct H_get as [red_list [H_red_length H_red_subseq]].
        spec IHk1 red_list H_red_length f. 
        destruct IHk1 as [left | right].
        ** destruct left as [bl [bl_length [bl_subseq bl_color]]].
           left. exists (v :: bl). repeat split.
           simpl; omega. apply subseq_hm.
           do 2 (eapply subseq_trans; eauto).
           (* Boom! *) 
           intros.
           destruct j. 
           omega. destruct i.
           (* When we're looking at the head, i.e. v *) 
           { simpl. subst M.
             assert (subseq bl (filter (fun n => f v n) l_rest)). 
             eapply subseq_trans; eauto.
             apply subseq_incl in H1. spec H1 (nth j bl d).
             spec H1. apply nth_In. omega.
             apply filter_In in H1. destruct H1 as [_ goal].
             exact goal. } 
           spec bl_color i j.
           spec bl_color. omega.
           simpl. assumption.
        ** destruct right as [bl [bl_length [bl_subseq bl_color]]].
           right. exists bl. repeat split.
           assumption. apply subseq_hn.
           do 2 (eapply subseq_trans; eauto).
           assumption.
      * (* In the case that N has a blue K_r *)
        clear IHk1.
        assert (H_get := get_subseq N rk2 blue).
        assert (H_trans : subseq N l_rest) by (subst N; apply (filter_subseq_correct')).
        destruct H_get as [blue_list [H_blue_length H_blue_subseq]].
        spec IHk2 blue_list H_blue_length f.
        destruct IHk2 as [left | right].
        ** destruct left as [bl [bl_length [bl_subseq bl_color]]].
           left. exists bl. repeat split.
           assumption. apply subseq_hn.
           do 2 (eapply subseq_trans; eauto).
           assumption.
        ** destruct right as [bl [bl_length [bl_subseq bl_color]]].
           right. exists (v :: bl). repeat split.
           simpl; omega. apply subseq_hm.
           do 2 (eapply subseq_trans; eauto).
           (* Boom! *) 
           intros.
           destruct j. 
           omega. destruct i. simpl. subst M.
           { simpl. subst N.
             assert (subseq bl (filter (fun n => negb (f v n)) l_rest)). 
             eapply subseq_trans; eauto.
             apply subseq_incl in H1. spec H1 (nth j bl d).
             spec H1. apply nth_In. omega.
             apply filter_In in H1. destruct H1 as [_ goal].
             apply negb_true_iff in goal. exact goal. }
           spec bl_color i j.
           spec bl_color. omega.
           simpl. assumption.
Qed.

Print Assumptions Ramsey_inductive_step. 
(* This requires no additional axioms *) 

(* Ramsey in Prop *) 
Lemma filterprop_vanilla : forall X (P : X -> Prop) (L : list X),
    exists L',
      forall x, In x L' <-> (In x L /\ P x).
Proof.
  induction L. exists nil. split. inversion 1. intros [? _]. inversion H.
  destruct IHL as [L' ?]. destruct (classic (P a)).
  exists (a :: L'). split; intros. destruct H1. split. left. assumption. subst. assumption.
  split. right. apply H in H1. destruct H1. assumption.
  apply H in H1. destruct H1. assumption.
  destruct H1. destruct H1. left. assumption.
  right. apply H. split; assumption.
  exists L'. split; intros.
  apply H in H1. destruct H1. split. right. assumption. assumption.
  apply H. destruct H1. destruct H1. subst. contradiction.
  split; assumption.
Qed.

Lemma filterprop_armed : forall X (P : X -> Prop) (L : list X),
    forall (Q : list X -> Prop)
      (f : list X -> list X)
      (H_correct : forall l : list X, Q (f l) /\ (forall w, In w (f l) <-> In w l)), 
    exists L', Q L' /\ 
          forall x, In x L' <-> (In x L /\ P x). 
Proof. 
  intros.
  destruct (filterprop_vanilla X P L) as [L_vanilla about_L_vanilla].
  exists (f L_vanilla).
  spec H_correct L_vanilla. 
  destruct H_correct.
  split. assumption.
  intro; split; intro. apply about_L_vanilla.
  apply H0. assumption. apply about_L_vanilla in H1.
  spec H0 x. apply H0. assumption.
Qed.

Lemma filterprop_vanilla_dep : forall X (D : X -> Prop) (P : {x | D x} -> Prop) (L : list {x | D x}),
    exists L', (* sublist L' L /\ *)
      forall x, In x L' <-> (In x L /\ P x).
Proof.
  induction L. exists nil. split. inversion 1. intros [? _]. inversion H.
  destruct IHL as [L' ?]. destruct (classic (P a)).
  exists (a :: L'). split; intros. destruct H1. split. left. assumption. subst. assumption.
  split. right. apply H in H1. destruct H1. assumption.
  apply H in H1. destruct H1. assumption.
  destruct H1. destruct H1. left. assumption.
  right. apply H. split; assumption.
  exists L'. split; intros.
  apply H in H1. destruct H1. split. right. assumption. assumption.
  apply H. destruct H1. destruct H1. subst. contradiction.
  split; assumption.
Qed.


Theorem filterprop_subseq_both :
   forall (X : Type) (P : X -> Prop) (L : list X),
   exists L' L'': list X, length L' + length L'' = length L /\
                     subseq L' L /\ subseq L'' L /\
                     (forall x : X, In x L' <-> In x L /\ P x) /\
                     (forall x : X, In x L'' <-> In x L /\ ~ P x). 
Proof.
  induction L as [|hd tl IHL].
  + exists nil, nil. repeat split.
    apply subseq_nil.
    apply subseq_nil.
    inversion H.
    inversion H.
    intros [absurd _]; inversion absurd.
    inversion H.
    inversion H.
    intros [absurd _]; inversion absurd.
  + destruct IHL as [L' [L'' [H_length [H_subseq' [H_subseq'' [H_in1 H_in2]]]]]].
    destruct (classic (P hd)).
    * exists (hd :: L'), L''. repeat split.
      simpl; omega.
      now apply subseq_hm.
      now apply subseq_hn.
      destruct H0 as [H_eq | H_tl]. 
      subst. apply in_eq.
      apply H_in1 in H_tl. destruct H_tl as [goal _].
      right; assumption.
      destruct H0 as [H_eq | H_tl].
      subst; assumption.
      apply H_in1 in H_tl. destruct H_tl as [_ goal]; assumption.
      intro. destruct H0 as [[H_eq | H_tl] H_P].
      subst. apply in_eq.
      right. apply H_in1. split; assumption.
      apply H_in2 in H0. destruct H0 as [goal _]; right; assumption.
      apply H_in2 in H0; destruct H0 as [_ goal]; assumption.
      intros [H_in H_notP]. apply H_in2.
      destruct H_in as [H_eq | H_tl].
      subst. contradiction.
      split; assumption.
    * exists L', (hd :: L''). repeat split.
      simpl; omega.
      now apply subseq_hn.
      now apply subseq_hm.
      apply H_in1 in H0.
      destruct H0 as [goal _]; right; assumption.
      apply H_in1 in H0. destruct H0 as [_ goal]; assumption.
      intros [H_in H_P].
      destruct H_in as [H_eq | H_tl]. 
      subst. contradiction.
      apply H_in1. split; assumption.
      destruct H0 as [H_eq | H_tl].
      subst. apply in_eq. apply H_in2 in H_tl.
      destruct H_tl as [goal _]; right; assumption.
      destruct H0 as [H_eq | H_tl].
      subst. assumption.
      apply H_in2 in H_tl.
      destruct H_tl as [_ goal]; assumption.
      intros [H_in H_notP]. destruct H_in as [H_eq | H_tl].
      subst. apply in_eq. right. apply H_in2.
      tauto. 
Qed.

Theorem Ramsey_inductive_step_prop {X : Type} :
  forall (r s : nat) (H_r : r > 0) (H_s : s > 0) (d : X),
  exists rk : nat,
    Ramsey_of_prop r s H_r H_s rk d.
Proof.
  intros r s.
  remember (r + s) as k.
  revert r s Heqk. 
  induction k as [|k IHk] using strong_induction; intros.
  - symmetry in Heqk; apply plus_is_O in Heqk.
    destruct Heqk; subst. inversion H_r.
  - destruct r as [|r]. inversion H_r.
    destruct s as [|s]. inversion H_s.
    destruct r as [|r].
    (* Pseudo base case, when r = 1 *) 
    exists 1. 
    apply (Ramsey_of_one_prop (S s) H_s d).
    (* Pseudo base case, when s = 1 *)
    destruct s as [|s].
    exists 1. 
    apply (Ramsey_of_one_prop (S (S r)) H_r d).
    (* Finally, everything is big enough *) 
    destruct k. omega. destruct k. omega. 
    (* Both (S r) and (S s) are greater than or equal to 1, 
       and therefore (S (S k)) is greater than or equal to two *)
    (* Reminder : r = S r, s = S s, k = S (S k) *) 
    spec IHk (S k). 
    spec IHk. omega.
    assert (IHk_copy := IHk).
    spec IHk (S r) (S (S s)).
    spec IHk_copy (S (S r)) (S s).
    spec IHk. omega. spec IHk_copy. omega.
    assert (H_pre1 : S r > 0) by omega.
    spec IHk H_pre1 H_s.
    spec IHk_copy H_r.
    assert (H_pre2 : S s > 0) by omega.
    spec IHk_copy H_pre2.
    spec IHk d. spec IHk_copy d.
    destruct IHk as [rk1 IHk1].
    destruct IHk_copy as [rk2 IHk2].
    exists (rk1 + rk2); red; intros l H_l f. 
    red in IHk1, IHk2.
    destruct l as [|v l_rest]. 
    (* Inversioning the base case list *)
    + unfold length in H_l. symmetry in H_l.
      apply plus_is_O in H_l. destruct H_l; subst.
      spec IHk1 ([] : list X).
      spec IHk1. reflexivity.
      spec IHk1 f. destruct IHk1;
      destruct H as [bl_absurd [absurd_length [absurd_subseq _]]];
      assert (bl_absurd = []) by (apply (subseq_nil_nil); assumption);
      subst; simpl in absurd_length; inversion absurd_length.
    + (* Now we have a pivot vertex *)
      assert (H_list := filterprop_subseq_both _ (f v) l_rest).
      destruct H_list as [M [N [MN_length [M_subseq [N_subseq [H_trans H_trans']]]]]]. 
      simpl in H_l.  
      assert (length M >= rk1 \/ length N >= rk2) by omega. 
      destruct H as [red | blue]. 
      * (* In the case that M has a red K_(S s) *)
        clear IHk2.
        assert (H_get := get_subseq M rk1 red).
        destruct H_get as [red_list [H_red_length H_red_subseq]].
        spec IHk1 red_list H_red_length f. 
        destruct IHk1 as [left | right].
        ** destruct left as [bl [bl_length [bl_subseq bl_color]]].
           left. exists (v :: bl). repeat split.
           simpl; omega. apply subseq_hm.
           do 2 (eapply subseq_trans; eauto).
           (* Boom! *) 
           intros.
           destruct j. 
           omega. destruct i. 
           (* When we're looking at the head, i.e. v *) 
           { simpl. apply H_trans. 
             apply subseq_incl in H_red_subseq.
             spec H_red_subseq (nth j bl d).
             apply H_red_subseq.
             apply subseq_incl in bl_subseq.
             spec bl_subseq (nth j bl d).
             apply bl_subseq. apply nth_In. omega. }
           spec bl_color i j.
           spec bl_color. omega.
           simpl. assumption.
        ** destruct right as [bl [bl_length [bl_subseq bl_color]]].
           right. exists bl. repeat split.
           assumption. apply subseq_hn.
           do 2 (eapply subseq_trans; eauto).
           assumption.
      * (* In the case that N has a blue K_r *)
        clear IHk1.
        assert (H_get := get_subseq N rk2 blue).
        destruct H_get as [blue_list [H_blue_length H_blue_subseq]].
        spec IHk2 blue_list H_blue_length f.
        destruct IHk2 as [left | right].
        ** destruct left as [bl [bl_length [bl_subseq bl_color]]].
           left. exists bl. repeat split.
           assumption. apply subseq_hn.
           do 2 (eapply subseq_trans; eauto).
           assumption.
        ** destruct right as [bl [bl_length [bl_subseq bl_color]]].
           right. exists (v :: bl). repeat split.
           simpl; omega. apply subseq_hm.
           do 2 (eapply subseq_trans; eauto).
           (* Boom! *) 
           intros.
           destruct j. 
           omega. destruct i. simpl. 
           { simpl. 
             apply H_trans'.
             apply subseq_incl in H_blue_subseq.
             spec H_blue_subseq (nth j bl d).
             apply H_blue_subseq.
             apply subseq_incl in bl_subseq.
             spec bl_subseq (nth j bl d).
             apply bl_subseq. apply nth_In. omega. }
           spec bl_color i j.
           spec bl_color. omega.
           simpl. assumption.
Qed.

Theorem Ramsey_single :
  forall (k : nat),
    k > 0 -> 
    exists rk : nat, rk >= k /\ 
              forall l : list nat, length l = rk ->
                            forall f : nat -> nat -> bool,
                              (exists bl : list nat, length bl = k /\ subseq bl l /\
                                              forall i j : nat, i < j < k ->
                                                         f (nth i bl d) (nth j bl d) = true)
                              \/ (exists bl : list nat, length bl = k /\ subseq bl l /\ 
                                                forall i j : nat, i < j < k ->
                                                           f (nth i bl d) (nth j bl d) = false). 
Proof.
  intros k H_gt_zero. 
  assert (H_one := @Ramsey_of_one nat).
  assert (H_step := @Ramsey_inductive_step nat).
  spec H_one k H_gt_zero d. 
  specialize (H_step k k H_gt_zero H_gt_zero d).
  destruct k. inversion H_gt_zero.
  destruct k.
  destruct H_one as [rk H_one].
  exists 1.
  split. omega.
  exact H_one. destruct H_step as [rk H_step].
  assert (rk >= S (S k) \/ rk < S (S k)) by omega. 
  destruct H as [yes | no].
  exists rk. split.
  assumption. assumption.
  exists rk. clear H_one.
  red in H_step.
  spec H_step (iota 0 rk). spec H_step.
  apply length_iota. spec H_step (fun i j : nat => true).
  destruct H_step. destruct H.
  destruct H. destruct H0.
  apply short_subseq_inversion in H0. inversion H0.
  rewrite H. rewrite length_iota. assumption.
  destruct H. destruct H.
  destruct H0. apply short_subseq_inversion in H0.
  inversion H0. rewrite H. rewrite length_iota; assumption.
Qed.

Theorem Ramsey_single_prop :
  forall (k : nat),
    k > 0 -> 
    exists rk : nat, rk >= k /\ 
              forall l : list nat, length l = rk ->
                            forall f : nat -> nat -> Prop,
                              (exists bl : list nat, length bl = k /\ subseq bl l /\
                                              forall i j : nat, i < j < k ->
                                                         f (nth i bl d) (nth j bl d))
                              \/ (exists bl : list nat, length bl = k /\ subseq bl l /\ 
                                                forall i j : nat, i < j < k ->
                                                           ~ f (nth i bl d) (nth j bl d)). 
Proof.
  intros k H_gt_zero. 
  assert (H_one := @Ramsey_of_one_prop nat).
  assert (H_step := @Ramsey_inductive_step_prop nat).
  spec H_one k H_gt_zero d.
  specialize (H_step k k H_gt_zero H_gt_zero d).
  destruct k. inversion H_gt_zero.
  destruct k. exists 1. 
  split. omega.
  destruct H_one. assumption. 
  destruct H_step as [rk H_step].
  assert (rk >= S (S k) \/ rk < S (S k)) by omega.
  destruct H as [yes | no].
  exists rk. split.
  assumption. assumption.
  exists rk. clear H_one.
  red in H_step.
  spec H_step (iota 0 rk). spec H_step.
  apply length_iota. spec H_step (fun i j : nat => True).
  destruct H_step. destruct H.
  destruct H. destruct H0.
  apply short_subseq_inversion in H0. inversion H0.
  rewrite H. rewrite length_iota. assumption.
  destruct H. destruct H.
  destruct H0. apply short_subseq_inversion in H0.
  inversion H0. rewrite H. rewrite length_iota; assumption.
Qed.   

Theorem Theorem_of_Ramsey_duo :
  forall (k : block_pumping_constant),
    exists rk : block_pumping_constant, rk >= k /\ 
      forall w : word,
      forall bps : breakpoint_set rk w,
      forall (P : nat -> nat -> Prop)
        (f : nat -> nat -> bool)
        (H : forall i j, (f i j = true <-> P i j) /\
                    (f i j = false <-> ~ P i j)),
        exists bps' : breakpoint_set k w,
          sublist bps' bps /\
          ((forall bp1 bp2 : breakpoint bps',
              bp1 < bp2 -> (P bp1 bp2))
          \/  (forall bp1 bp2 : breakpoint bps',
                 bp1 < bp2 -> ~ (P bp1 bp2))).
Proof.
  intro k. 
  assert (H_ramsey := Ramsey_single k).
  destruct k as [k about_k]; unfold p_predicate in about_k. 
  spec H_ramsey. simpl; omega.
  destruct H_ramsey as [rk [rk_fact H_ramsey]].
  simpl in rk_fact. 
  assert (about_rk : rk >= 2). omega. 
  exists (exist p_predicate rk about_rk).
  split. simpl. assumption.
  intros w bps P f f_correct.
  destruct bps as [bps [bps_length [bps_incr bps_last]]].
  simpl in *. 
  spec H_ramsey bps bps_length f.
  destruct H_ramsey as [yes | no]. 
  - destruct yes as [bps_yes [bps_yes_length [bps_yes_subseq yes]]]. 
    assert (breakpoint_set_predicate bps_yes w (exist _ k about_k)).
    { repeat split. simpl. assumption.
      now apply (subseq_incr bps).
      assert (H_trans := about_subseq_last bps_yes bps d).
      spec H_trans. rewrite bps_yes_length; omega.
      spec H_trans. rewrite bps_length; omega.
      spec H_trans. assumption.
      spec H_trans. exact bps_yes_subseq.
      now apply (le_trans (last bps_yes d) (last bps d) (length w)). }
      exists (exist _ bps_yes H); simpl in *.
      split.
      apply subseq_incl in bps_yes_subseq. 
      assumption.
      left. intros.
      destruct bp1 as [bp1 about_bp1]; 
        destruct bp2 as [bp2 about_bp2]; 
        unfold breakpoint_predicate in *. 
      simpl in *. 
      apply (In_nth _ _ d) in about_bp1.
      apply (In_nth _ _ d) in about_bp2.
      destruct about_bp1 as [i [i_pos i_eq]].
      destruct about_bp2 as [j [j_pos j_eq]].
      spec yes i j. spec yes.
      rewrite bps_yes_length in i_pos, j_pos.
      split.
     eapply increasing_nth_lt.
     destruct H as [_ [bps_yes_incr bps_yes_last]].
     exact bps_yes_incr. rewrite bps_yes_length; assumption.
     rewrite bps_yes_length; assumption.
     rewrite i_eq, j_eq.  assumption. assumption.
     spec f_correct (nth i bps_yes d) (nth j bps_yes d).
     rewrite <- i_eq. rewrite <- j_eq.
    destruct f_correct as [f_correct _].
    apply f_correct. assumption.
  - destruct no as [bps_no [bps_no_length [bps_no_subseq no]]]. 
    assert (breakpoint_set_predicate bps_no w (exist _ k about_k)).
    { repeat split. simpl. assumption.
      now apply (subseq_incr bps).
      assert (H_trans := about_subseq_last bps_no bps d).
      spec H_trans. rewrite bps_no_length; omega.
      spec H_trans. rewrite bps_length; omega.
      spec H_trans. assumption.
      spec H_trans. exact bps_no_subseq.
      now apply (le_trans (last bps_no d) (last bps d) (length w)). }
    exists (exist _ bps_no H); simpl in *.
    split.
    apply subseq_incl in bps_no_subseq. 
    assumption.
    right. intros.
    destruct bp1 as [bp1 about_bp1]; 
      destruct bp2 as [bp2 about_bp2]; 
      unfold breakpoint_predicate in *. 
    simpl in *. 
    apply (In_nth _ _ d) in about_bp1.
    apply (In_nth _ _ d) in about_bp2.
    destruct about_bp1 as [i [i_pos i_eq]].
    destruct about_bp2 as [j [j_pos j_eq]].
    spec no i j. spec no.
    rewrite bps_no_length in i_pos, j_pos.
    split.
    eapply increasing_nth_lt.
    destruct H as [_ [bps_no_incr bps_no_last]].
    exact bps_no_incr. rewrite bps_no_length; assumption.
    rewrite bps_no_length; assumption.
    rewrite i_eq, j_eq.  assumption. assumption.
    spec f_correct (nth i bps_no d) (nth j bps_no d).
    rewrite <- i_eq. rewrite <- j_eq.
    destruct f_correct as [_ f_correct].
    apply f_correct. assumption.
Qed. 


Theorem Theorem_of_Ramsey_duo_prop :
  forall (k : block_pumping_constant),
    exists rk : block_pumping_constant, rk >= k /\ 
      forall w : word,
      forall bps : breakpoint_set rk w,
      forall (P : nat -> nat -> Prop),
        exists bps' : breakpoint_set k w,
          sublist bps' bps /\
          ((forall bp1 bp2 : breakpoint bps',
              bp1 < bp2 -> (P bp1 bp2))
          \/  (forall bp1 bp2 : breakpoint bps',
                 bp1 < bp2 -> ~ (P bp1 bp2))).
Proof.
  intro k. 
  assert (H_ramsey := Ramsey_single_prop k).
  destruct k as [k about_k]; unfold p_predicate in about_k. 
  spec H_ramsey. simpl; omega.
  destruct H_ramsey as [rk [rk_fact H_ramsey]].
  simpl in rk_fact. 
  assert (about_rk : rk >= 2). omega. 
  exists (exist p_predicate rk about_rk).
  split. simpl. assumption.
  intros w bps P.
  destruct bps as [bps [bps_length [bps_incr bps_last]]].
  simpl in *. 
  spec H_ramsey bps bps_length P.
  destruct H_ramsey as [yes | no]. 
  - destruct yes as [bps_yes [bps_yes_length [bps_yes_subseq yes]]]. 
    assert (breakpoint_set_predicate bps_yes w (exist _ k about_k)).
    { repeat split. simpl. assumption.
      now apply (subseq_incr bps).
      assert (H_trans := about_subseq_last bps_yes bps d).
      spec H_trans. rewrite bps_yes_length; omega.
      spec H_trans. rewrite bps_length; omega.
      spec H_trans. assumption.
      spec H_trans. exact bps_yes_subseq.
      now apply (le_trans (last bps_yes d) (last bps d) (length w)). }
      exists (exist _ bps_yes H); simpl in *.
      split.
      apply subseq_incl in bps_yes_subseq. 
      assumption.
      left. intros.
      destruct bp1 as [bp1 about_bp1]; 
        destruct bp2 as [bp2 about_bp2]; 
        unfold breakpoint_predicate in *. 
      simpl in *. 
      apply (In_nth _ _ d) in about_bp1.
      apply (In_nth _ _ d) in about_bp2.
      destruct about_bp1 as [i [i_pos i_eq]].
      destruct about_bp2 as [j [j_pos j_eq]].
      spec yes i j. spec yes.
      rewrite bps_yes_length in i_pos, j_pos.
      split.
     eapply increasing_nth_lt.
     destruct H as [_ [bps_yes_incr bps_yes_last]].
     exact bps_yes_incr. rewrite bps_yes_length; assumption.
     rewrite bps_yes_length; assumption.
     rewrite i_eq, j_eq.  assumption. assumption.
     rewrite <- i_eq. rewrite <- j_eq.
     apply yes. 
  - destruct no as [bps_no [bps_no_length [bps_no_subseq no]]]. 
    assert (breakpoint_set_predicate bps_no w (exist _ k about_k)).
    { repeat split. simpl. assumption.
      now apply (subseq_incr bps).
      assert (H_trans := about_subseq_last bps_no bps d).
      spec H_trans. rewrite bps_no_length; omega.
      spec H_trans. rewrite bps_length; omega.
      spec H_trans. assumption.
      spec H_trans. exact bps_no_subseq.
      now apply (le_trans (last bps_no d) (last bps d) (length w)). }
    exists (exist _ bps_no H); simpl in *.
    split.
    apply subseq_incl in bps_no_subseq. 
    assumption.
    right. intros.
    destruct bp1 as [bp1 about_bp1]; 
      destruct bp2 as [bp2 about_bp2]; 
      unfold breakpoint_predicate in *. 
    simpl in *. 
    apply (In_nth _ _ d) in about_bp1.
    apply (In_nth _ _ d) in about_bp2.
    destruct about_bp1 as [i [i_pos i_eq]].
    destruct about_bp2 as [j [j_pos j_eq]].
    spec no i j. spec no.
    rewrite bps_no_length in i_pos, j_pos.
    split.
    eapply increasing_nth_lt.
    destruct H as [_ [bps_no_incr bps_no_last]].
    exact bps_no_incr. rewrite bps_no_length; assumption.
    rewrite bps_no_length; assumption.
    rewrite i_eq, j_eq.  assumption. assumption.
    rewrite <- i_eq. rewrite <- j_eq.
    apply no.
Qed. 

