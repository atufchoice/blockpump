Require Import List Logic Nat Arith Bool Omega.
Require Import Compare_dec EqNat Decidable ListDec FinFun. 
Require Fin. 
Import ListNotations. 
From Block   
Require Import lib definitions finite ramsey.

(** Proving the finiteness of block cancellable with k languages
    without the Axiom of Choice **)

(** Step 1 : Building a computable unshear function **)

(* Word-specific membership checking function *)
Fixpoint is_member (w : word) (l : list word) : bool :=
  match l with
  | [] => false
  | hd :: tl => if (word_eq w hd)
               then true
               else is_member w tl
  end.

Definition is_member_prop (w : word) (l : list word) : Prop :=
  In w l. 

Lemma is_member_correct : forall l w, is_member w l = true <-> is_member_prop w l. 
Proof. 
  intros l w.
  induction l as [|hd tl IHl].
  - split; intro H. 
    + unfold is_member in H; inversion H.  
    + inversion H.
  - split; intro H.
    + simpl in H.
      assert (H_dec := word_eq_dec w hd).
      destruct H_dec as [eq | neq].
      rewrite eq in H.
      simpl. left. apply word_eq_refl in eq.
      symmetry; assumption.
      apply (Bool.not_true_is_false (word_eq w hd)) in neq.
      rewrite neq in H. 
      simpl. right. apply IHl; assumption.
    + apply in_inv in H.
      destruct H as [eq | neq].
      rewrite eq.
      simpl.
      assert (word_eq w w = true).
      { rewrite word_eq_refl. reflexivity. }
      rewrite H. reflexivity.
      simpl. 
      assert (H_dec := word_eq_dec w hd).
      destruct H_dec as [Heq | Hneq].
      rewrite Heq. reflexivity.
      apply (Bool.not_true_is_false (word_eq w hd)) in Hneq.
      rewrite Hneq.
      apply IHl. exact neq.
Qed.

Lemma is_member_correct' : forall l w, is_member w l = false <-> ~ In w l. 
Proof.
  intros. 
  apply mirror_reflect.
  intros; apply is_member_correct.
Qed.

(* List of all k-size breakpoint sets for a word *)
Definition get_k_bps (w : word) (k : nat) : list (list nat) :=
  choose (iota 0 (S (length w))) k.

(* For correctness proof about get_k_bps *) 
(* Any iota of good length can form a breakpoint set *) 
Lemma iota_bps :
  forall (w : word) (n : nat) (about_n : p_predicate n),
    n <= S (length w) -> 
    breakpoint_set_predicate (iota 0 n) w (exist p_predicate n about_n). 
Proof.
  intros w n about_n H_length.
  unfold breakpoint_set_predicate; repeat split.
  - (* Length obligation *)
    rewrite length_iota. reflexivity.
  - (* Increasing obligation *)
    now apply iota_increasing.
  - rewrite iota_last_nonzero.
    omega. destruct n.
    unfold p_predicate in about_n. inversion about_n.
    omega.
Qed.

(* Key lemma : choice function gives us breakpoint sets! *) 
Lemma iota_gives_bps :
  forall (w : word) (k : block_pumping_constant) (l : list nat),
    length w >= k -> 
    In l (choose (iota 0 (S (length w))) k) -> 
    breakpoint_set_predicate l w k.
Proof.
  intros w k l H_length H_in.
  apply choose_spec in H_in. 
  2 : { rewrite length_iota. omega. } 
  destruct H_in as [H_eq H_subseq].
  assert (H_incr : increasing l). 
  { assert (H_useful := subseq_incr (iota 0 (S (length w)))).
    spec H_useful definitions.d (iota_increasing 0 (S (length w)) definitions.d).
    spec H_useful l. apply H_useful; assumption.  }
  unfold breakpoint_set_predicate; repeat split.
  - (* Length obligation *)
    exact H_eq. 
  - (* Increasing obligation! *)
    exact H_incr.
  - (* Last obligation *)
    assert (H_trans : last (iota 0 (S (length w))) definitions.d  = S (length w) - 1).
    { rewrite iota_last_nonzero. omega. 
      intro absurd. rewrite absurd in H_subseq.
      simpl in H_subseq. inversion H_subseq. rewrite <- H in H_eq.
      unfold length in H_eq.
      destruct k; simpl in *.
      rewrite <- H_eq in p. unfold p_predicate in p; inversion p. }
    assert (H_useful := about_subseq_last l (iota 0 (S (length w)))).
    assert (length l >= 2).
    { destruct k. unfold p_predicate in p. simpl in *. omega. }
    assert (length (iota 0 (S (length w))) >= 2).
    { rewrite length_iota. destruct k. unfold p_predicate in p.
      simpl in *. omega. }
    spec H_useful definitions.d H H0.
    spec H_useful (iota_increasing 0 (S (length w)) definitions.d).
    spec H_useful H_subseq.
    omega.
Qed.

(* Condition checker : for one k-breakpoint set, all canceled words are in reference list *) 
Fixpoint are_all_pumps_helper (w : word) (l : list word) (hd : nat) (tl : list nat) : bool :=
  match tl with
  | [] => true
  | h :: t => if is_member (cancelled_word w hd h) l
              then are_all_pumps_helper w l hd t
              else false
  end.

(* Correctness for are_all_pumps_helper *) 
Definition are_all_pumps_helper_prop (w : word) (l : list word) (hd : nat) (tl : list nat) : Prop :=
  forall (j : nat),
    In j tl -> In (cancelled_word w hd j) l. 

Theorem are_all_pumps_helper_correct :
  forall (w : word) (l : list word) (hd : nat) (tl : list nat),
    are_all_pumps_helper w l hd tl = true <->
    are_all_pumps_helper_prop w l hd tl. 
Proof.
  intros w l hd tl.
  induction tl as [|hd' tl' IHtl].
  - (* Base case *)
    split; intro H.
    + intros j H_absurd; inversion H_absurd.
    + simpl; reflexivity.
  - (* Induction step *)
    split; intro H.
    + (* First direction, computational -> propositional *)
      simpl in H.
      case_eq (is_member (cancelled_word w hd hd') l).
      ++ (* When the new head forms a pump *)
        intro H_true. 
        rewrite H_true in H.
        rewrite IHtl in H. 
        intros j H_in.
        destruct H_in.
        subst j. apply is_member_correct in H_true. 
        exact H_true.
        spec H j H0. exact H.
      ++ (* When the new head doesn't form a pump *)
        intro H_false. 
        rewrite H_false in H. 
        inversion H.
    + (* Second direction, propositional -> computational *)
      simpl.
      case_eq (is_member (cancelled_word w hd hd') l).
      ++ (* When the new head forms a pump *)
        intro H_true.
        rewrite IHtl.
        intros j H_in.
        spec H j. 
        assert (In j (hd' :: tl')). apply in_cons. exact H_in.
        spec H H0; clear H0. exact H.
      ++ (* When the new head doesn't form a pump *)
        intro H_false. 
        (* Now we find a contradiction *)
        spec H hd' (in_eq hd' tl').
        rewrite is_member_correct' in H_false.
        contradiction.
Qed.

Theorem are_all_pumps_helper_correct' :
  forall (w : word) (l : list word) (hd : nat) (tl : list nat),
    are_all_pumps_helper w l hd tl = false <->
    ~ (are_all_pumps_helper_prop w l hd tl).
Proof.
  intros w l hd tl.
  eapply mirror_reflect. 
  apply are_all_pumps_helper_correct. 
Qed.

Fixpoint are_all_pumps (w : word) (l : list word) (bps : list nat) : bool :=
  match bps with
  | [] => true
  | hd :: tl => if are_all_pumps_helper w l hd tl
               then are_all_pumps w l tl
               else false
  end.

Definition are_all_pumps_prop (w : word) (l : list word) (bps : list nat) : Prop :=
  forall (i j : nat),
    i < j < (length bps) ->
    In (cancelled_word w (nth i bps d) (nth j bps d)) l.

Lemma are_all_pumps_correct :
  forall (w : word) (l : list word) (bps : list nat),
    are_all_pumps w l bps = true <->
    are_all_pumps_prop w l bps. 
Proof. 
  intros w l bps.
  induction bps as [|bp tl IHbps].
  - (* Base case *)
    split; intro H.
    + intros i j H_lt. unfold length in H_lt; inversion H_lt.
      inversion H1. 
    + simpl. reflexivity.
  - (* Induction step *)
    split; intro H. 
    + intros i j H_lt. 
      simpl in H. 
      (* Critically, the case distinction has to happen here! *) 
      destruct j.
      inversion H_lt; omega. 
      assert (H_about_j : In (nth j tl definitions.d) tl).
      { destruct H_lt. simpl in H1.
        apply lt_S_n in H1.
        now apply nth_In. }
      (* Critically, this fact has to enter here : *) 
      assert (i = j \/ i < j) by omega.
      assert (j < length tl).
      { rewrite unfold_length_S in H_lt. destruct H_lt; omega. }
      destruct H0 as [eq | lt].
      (* Critically, now destruct! *)
      * (* When i = j *)
        (* Critically, now destruct again! *)
        case_eq (are_all_pumps_helper w l bp tl); [intro H_yes | intro H_no]. 
        ** (* When i = j and the new list is all pumps *)
            rewrite H_yes in H;
            rewrite IHbps in H;
            rewrite are_all_pumps_helper_correct in H_yes. 
          unfold are_all_pumps_helper_prop in H_yes.
          rewrite unfold_nth_Sn_tl. subst i.
          destruct j.
          spec H_yes (nth 0 tl definitions.d).
          spec H_yes H_about_j.
          exact H_yes.
          spec H j (S j).
          assert (j < S j < length tl).
          { split. omega. exact H1. }
          spec H H0; clear H0.
          rewrite unfold_nth_Sn_tl. exact H.
        ** (* When i = j and the new list is not all pumps *)
          (* We find a contradiction *)
            rewrite H_no in H; inversion H.
      *  (* When i < j *)
        (* Critically, now destruct again! *)
        case_eq (are_all_pumps_helper w l bp tl); [intro H_yes | intro H_no]. 
        ** (* When i < j and the new list is all pumps *)
            rewrite H_yes in H;
            rewrite IHbps in H;
            rewrite are_all_pumps_helper_correct in H_yes. 
          unfold are_all_pumps_helper_prop in H_yes.
          rewrite unfold_nth_Sn_tl.
          destruct i. rewrite nth_zero.
          now apply (H_yes (nth j tl definitions.d)).
          rewrite unfold_nth_Sn_tl.
          (* Now the i-th element is not in tl *)
          spec H i j.
          assert (i < j < length tl).
          { split. destruct H_lt; omega. exact H1. }
          spec H H0; clear H0. assumption.
        ** (* When i < j and the new list is not all pumps. *)
            rewrite H_no in H. inversion H.
    + (* Propositional -> computational *)
      (* Basically the same thing but in reverse. *)
      simpl.
      case_eq (are_all_pumps_helper w l bp tl); [intro H_yes | intro H_no]. 
      ** (* When all pumps, *)
        rewrite are_all_pumps_helper_correct in H_yes;
          rewrite IHbps.
        unfold are_all_pumps_helper_prop in H_yes.
        intros i j H_lt.
        assert (In (nth j tl definitions.d) tl).
        { apply nth_In; omega. }
        destruct i. spec H 1 (S j).
        assert (1 < S j < length (bp :: tl)).
        { rewrite unfold_length_S. omega. }
        spec H H1; clear H1.
        simpl in *; exact H.
        spec H (S (S i)) (S j).
        assert (S (S i) < (S j) < length (bp :: tl)).
        { destruct H_lt; split. apply lt_n_S; exact H1.
          rewrite unfold_length_S; omega. }
        spec H H1. do 2 rewrite unfold_nth_Sn_tl in H. exact H.
      ** (* When not all pumps, *)
        exfalso (* We find a contradiction *). 
        rewrite are_all_pumps_helper_correct' in H_no.
        apply H_no. intros i j.
        unfold are_all_pumps_prop in H.
        spec H 0.
        apply (In_nth _ _ definitions.d) in j.
        destruct j as [i_pos [i_length i_nth]].
        destruct i_pos. 
        destruct tl. inversion i_length.
        rewrite nth_zero in i_nth. subst n.
        spec H 1.
        assert (0 < 1 < length (bp :: i :: tl)).
        { split; simpl; omega. }
        spec H H0. unfold nth in H. 
        exact H. rewrite nth_zero in H. subst i. spec H (S (S i_pos)).
        assert (0 < S (S i_pos) < length (bp :: tl)).
        { split. omega. rewrite unfold_length_S. omega. }
        spec H H0. exact H.
Qed.

(* Check that some k-size breakpoint set contains all pumps *)
Definition exists_all_pumps_bps (w : word) (l : list word) (k : nat) : bool :=
  existsb (are_all_pumps w l) (get_k_bps w k).

Definition exists_all_pumps_bps_prop (w : word) (l : list word) (k : nat) : Prop :=
  exists lp : list nat,
    are_all_pumps_prop w l lp /\ In lp (get_k_bps w k).

Lemma exists_all_pumps_bps_correct :
  forall (w : word) (l : list word) (k : nat),
    exists_all_pumps_bps w l k = true <-> exists_all_pumps_bps_prop w l k. 
Proof.
  intros w l k.
  split; intro H.
  - unfold exists_all_pumps_bps in H.
    rewrite (existsb_exists (are_all_pumps w l) (get_k_bps w k)) in H.
    destruct H as [bps [bps_in about_bps]].
    unfold exists_all_pumps_bps_prop.
    exists bps. split.
    apply are_all_pumps_correct. exact about_bps. exact bps_in.
  - unfold exists_all_pumps_bps.
    rewrite (existsb_exists (are_all_pumps w l) (get_k_bps w k)).
    destruct H as [bps [about_bps bps_in]].
    exists bps.
    split. exact bps_in.
    rewrite are_all_pumps_correct. exact about_bps.
Qed.
(* And this is the condition we are looking for! *)

(* This is the namespace for our algorithm condition *) 
Definition check (w : word) (l : list word) (k : nat) :=
  exists_all_pumps_bps w l k.

(* Generating words of a certain length *)
Fixpoint app_map (l : list word) : list word :=
  match l with
  | [] => []
  | hd :: tl => (aa::hd) :: (bb::hd) :: (cc::hd) :: app_map tl
  end.

Fixpoint repeatedly_apply {X : Type} (n : nat) (f : X -> X) (x : X) : X :=
  match n with
  | 0 => x
  | S n' => repeatedly_apply n' f (f x)
  end.

Definition generate_words_of_length (n : nat) : list word :=
  repeatedly_apply n (app_map) [[]].

Lemma app_map_grow1: forall n l,
  (forall w, In w l -> length w = n) ->
  (forall w, In w (app_map l) -> length w = S n).
Proof.
  induction l; intros. inversion H0.
  simpl in *. destruct H0 as [? | [? | [? | ?]]]; subst; simpl; 
  try (f_equal; apply H; left; reflexivity).
  apply IHl. intros. apply H. right. apply H1.
  apply H0.
Qed.

Lemma app_map_grow2: forall n l,
  (forall w, length w = n -> In w l) ->
  (forall w, length w = S n -> In w (app_map l)).
Proof. 
  destruct w; inversion 1.
  specialize (H w H2).
  clear -H. 
  induction l. inversion H.
  destruct H. subst w.
  destruct t. left. reflexivity.
  right. left. reflexivity.
  right. right. left. reflexivity.
  right. right. right. apply IHl. apply H.
Qed.

Theorem app_map_grow: forall n l,
  (forall w, In w l <-> length w = n) ->
  (forall w, In w (app_map l) <-> length w = S n).
Proof.
  intros n l H w. split; intro;
  [apply app_map_grow1 with l | apply app_map_grow2 with n];
  intros; try assumption; apply H; assumption.
Qed.

Lemma repeatedly_apply_app_map :
  forall (n : nat) (L : list (list T)) (j : nat),
    (forall w, In w L <-> length w = j) ->
    forall (w : word),
    In w (repeatedly_apply n app_map L)
    <-> length w = n + j.
Proof.
  induction n; simpl; intros. apply H. 
  specialize (IHn (app_map L) (S j)).
  replace (S (n + j)) with (n + S j) by omega.
  apply IHn. apply app_map_grow. apply H.
Qed.

Theorem generate_words_length_correct :
  forall (n : nat) (w : word),
    In w (generate_words_of_length n) <-> length w = n.
Proof.
  unfold generate_words_of_length. intros.
  replace n with (n + 0) at 2 by omega.
  apply repeatedly_apply_app_map.
  destruct w0; simpl; split.
  * reflexivity.
  * left. reflexivity.
  * intros [? | []]. inversion H.
  * inversion 1.
Qed.

Fixpoint generate_words_upto (n : nat) :=
  match n with
  | 0 => [[]]
  | S n' => (generate_words_of_length (S n')) ++ generate_words_upto n'
  end.
Lemma generate_words_upto_correct : forall (n : nat) (w : word),
    In w (generate_words_upto n) <-> length w <= n.
Proof.
  intros n w.
  induction n as [|n IHn].
  - simpl. split; intro H.
    destruct H. rewrite <- H.
    unfold length; reflexivity.
    inversion H.
    left. 
    inversion H. apply length_zero_iff_nil in H1.
    symmetry; assumption.
  - split; intro H.
    + simpl in H.
      apply in_app_or in H.
      destruct H as [left | right]. 
      * rewrite generate_words_length_correct in left.
        omega.
      * rewrite IHn in right. omega.
    + simpl.
      apply le_lt_or_eq in H.
      apply in_or_app. 
      destruct H as [left | right].
      * right.  assert (length w <= n) by omega.
        apply IHn in H. assumption.
      * left.
        rewrite generate_words_length_correct.
        assumption.
Qed. 

(* Begin detouring *)
Fixpoint words_to_add (lref : list word) (k : nat) (l : list word) : list word :=
  match l with
  | [] => []
  | hd :: tl => if check hd lref k
               then hd :: words_to_add lref k tl
               else words_to_add lref k tl 
  end.

Definition words_to_add_prop (lref : list word) (k : nat) (l : list word) (w : word) :=
  exists_all_pumps_bps_prop w lref k /\ In w l. 

Theorem words_to_add_correct :
  forall (l lref : list word) (k : nat),
  forall (w : word),
    In w (words_to_add lref k l) <-> words_to_add_prop lref k l w.
Proof.
(* The following proof is when check = exists_all_pumps_bps *) 
  intros l lref k w.
  induction l as [|hd tl IHl]. 
  - (* Base case *)
    split; intro H.
    + (* In -> properties *)
      simpl in H. inversion H.
    + (* Properties -> In *)
      destruct H. inversion H0.
  - (* Inductive step *)
    split; intro H.
    + (* In -> properties *)
      simpl in H.
      case_eq (check hd lref k); intro H_case;
        rewrite H_case in H. 
      * destruct H as [H_eq | H_tl].
        ** (* w = hd *)
          subst hd. split.
          apply exists_all_pumps_bps_correct. exact H_case.
          apply in_eq.
        ** (* In w tl *)
          rewrite IHl in H_tl.
          destruct H_tl. split. assumption.
          apply in_cons. assumption.
      * rewrite IHl in H. destruct H.
        split. exact H. apply in_cons. exact H0.
    + (* Properties -> In *)
      simpl. 
      case_eq (check hd lref k); intro H_case.
      (* Can't left/right yet! *) 
      destruct H. destruct H0 as [H_eq | H_tl].
      rewrite <- H_eq. apply in_eq.
      right. apply IHl; split; assumption.
      apply IHl.
      destruct H.
      destruct H0 as [H_eq | H_tl].
      rewrite <- H_eq in H. rewrite <- exists_all_pumps_bps_correct in H.
      unfold check in H_case; rewrite H in H_case. inversion H_case.
      split; assumption.
Qed. 

Theorem words_to_add_correct' :
  forall (l lref : list word) (k : nat),
  forall (w : word),
    ~ In w (words_to_add lref k l) <-> ~ words_to_add_prop lref k l w.
Proof.
  intros. apply not_iff_compat. 
  apply words_to_add_correct.
Qed.

(* Add all words of a certain length that satisfy condition above: *)
Definition words_to_add_of_length (n : nat) (lref : list word) (k : nat) : list word :=
  words_to_add lref k (generate_words_of_length n). 

Definition words_to_add_of_length_prop (n : nat) (lref : list word) (k : nat) (w : word) :=
  exists_all_pumps_bps_prop w lref k
  (* /\ all_exists_pumps_bps_prop w lref k *) 
  /\ length w = n.

Theorem words_to_add_of_length_correct :
  forall (n : nat) (lref : list word) (k : nat),
  forall (w : word),
    In w (words_to_add_of_length n lref k) <-> words_to_add_of_length_prop n lref k w.
Proof.
  intros n lref k w.
  split; intro H.
  - (* In -> properties *)
    unfold words_to_add_of_length in H.
    rewrite (words_to_add_correct (generate_words_of_length n) lref k w) in H. 
    destruct H as [H_correct H_in].
    split. exact H_correct.
    rewrite generate_words_length_correct in H_in.
    assumption.
  - (* Properties -> In *)
    unfold words_to_add_of_length.
    rewrite (words_to_add_correct (generate_words_of_length n) lref k w).
    split. destruct H.
    exact H. destruct H as [H_correct H_length].
    rewrite generate_words_length_correct. exact H_length.
Qed.
(* End detouring *)

(* Chuck in all the words of a length that pass check *)
Definition to_chuck (k : nat) (lref : list word) (n : nat) :=
  filter (fun w => check w lref k) (generate_words_of_length n).

Definition chuck (k rk n : nat) (lref : list word) :=
  filter (fun w => check w lref k) (generate_words_of_length (n + rk)) ++ lref.

Definition to_chuck_prop (n : nat) (lref : list word) (k : nat) (w : word) :=
  exists_all_pumps_bps_prop w lref k
  /\ length w = n.

Definition chuck_prop (k rk n : nat) (lref : list word) (w : word) :=
  (exists_all_pumps_bps_prop w lref k /\ length w = n + rk)
\/ In w lref.

(* Some detouring is done here, but oh well *)
Theorem filter_equiv :
  forall (k n : nat) (lref : list word),
    words_to_add_of_length n lref k =
    filter (fun w => check w lref k) (generate_words_of_length n).
Proof.
  intros k n lref.
  unfold words_to_add_of_length.
  induction (generate_words_of_length n).
  - compute; reflexivity. 
  - simpl. case_eq (check a lref k); intro H_case.
    rewrite IHl. reflexivity.
    exact IHl.
Qed.

Theorem filter_add_correct :
  forall (lref : list word) (k : nat) (n : nat) (w : word),
    In w (to_chuck k lref n) <-> to_chuck_prop n lref k w.
Proof.
  intros. unfold to_chuck. rewrite <- filter_equiv.
  apply words_to_add_of_length_correct. 
Qed.

Lemma chuck_correct :
  forall (lref : list word) (k rk n : nat) (w : word),
    In w (chuck k rk n lref) <-> chuck_prop k rk n lref w.  
Proof.
  intros. unfold chuck. split; intro.
  apply in_app_or in H. destruct H.
  unfold chuck_prop. left. 
  now apply filter_add_correct.
  right. assumption.
  destruct H. apply in_or_app. left.
  now apply filter_add_correct.
  apply in_or_app. right; assumption.
Qed.

Fixpoint chuck_length (k rk n : nat) (lref : list word) :=
  match n with
  | 0 => lref
  | S n' => chuck k rk n (chuck_length k rk n' lref)
  end.

(* The m here is protrusion length *)
Definition bc_language_dec_proj1 {k : block_pumping_constant} (bcl : bc_language_dec k) :=
  match bcl with
  | exist _ b _ => b
  end.

Definition agreement_upto (k rk : block_pumping_constant) (l : bc_language_dec k) (lw : list word) (m : nat) :=
  forall w, In w lw <-> (length w <= m + rk /\ bc_language_dec_proj1 l w).

(* Defining inverse function as word -> bool *) 
Definition unshear_bool (k rk : nat) (lref : list word) : word -> bool :=
  fun w => is_member w (chuck_length k rk (length w) lref).

(* Defining inverse function as word -> Prop *)
Definition unshear (k rk : nat) (lref : list word) : word -> Prop :=
  fun w => unshear_bool k rk lref w = true.

(* Defining short languages *) 
Definition shear_language (n : nat) (l : language) : language :=
  fun w => l w /\ length w <= n.

Theorem IH_agreement :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant), 
  forall (l : bc_language_dec k)
    (lw : list word)
    (m : nat),
    agreement_upto k rk l lw m ->
    agreement_upto k rk l (words_to_add_of_length (S m + rk) lw k ++ lw) (S m).
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
      destruct H_bc as [H_dec H_bc].
      spec H_bc w.
      destruct H_all as [lp [H_all H_chosen]]. 
      assert (about_lp : breakpoint_set_predicate lp w (exist p_predicate k about_k)).
      { apply iota_gives_bps. 
        rewrite H_in.
        unfold p_predicate in about_k. 
        simpl.  omega. assumption. } 
      specialize (H_bc (exist _ lp about_lp)).
      destruct H_bc as [i [j [i_lt_j about_i_j]]].
      simpl in *. apply about_i_j. 
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
      spec H_ramsey (fun i j => bc_language_dec_proj1 l (cancelled_word w i j)).
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
        destruct about_l_copy as [l_dec about_l_copy].
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
        apply H_in in H_bc. unfold cancelled_word in about_bps_no.
        rewrite i_pos_eq, j_pos_eq in about_bps_no. contradiction.
Qed.
(* This lemma is done *)

(* Reminder to self: m in agreement_upto is protrusion *) 
Lemma IH_chuck_step :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant), 
  forall (l : bc_language_dec k) (lw : list word) (m : nat),
    agreement_upto k rk l lw m ->
    agreement_upto k rk l (chuck k rk (S m) lw) (S m).
Proof.
  intros k.
  assert (H_useful := IH_agreement k).
  destruct H_useful as [rk H_useful].
  exists rk. intros l lref m H_base. 
  specialize (H_useful l lref m H_base).
  rewrite filter_equiv in H_useful.
  unfold chuck. assumption.
Qed.

(* For every k there exists an rk such that for all bc_k languages 
   and lists that agree with them, we can safely chuck_length *) 
Lemma IH_chuck :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant),
  forall (l : bc_language_dec k) (lw : list word),
    agreement_upto k rk l (chuck_length k rk 0 lw) 0 ->
    forall (m : nat),
      agreement_upto k rk l (chuck_length k rk m lw) m.
Proof. 
  intros k.
  destruct (IH_chuck_step k) as [rk H_useful].
  exists rk. intros l lw H_base m.
  induction m.
  - (* Base case, assumption *)
    simpl in *.
    assumption.
  - (* Inductive step *)
    simpl. 
    apply H_useful. assumption. 
Qed.

Theorem unshear_correctness :
  forall (k : block_pumping_constant),
  exists (rk : block_pumping_constant),
  forall (l : bc_language_dec k) (lw : list word),
    agreement_upto k rk l (chuck_length k rk 0 lw) 0 ->
    (forall (w : word),
        In w lw <-> (shear_language rk (unshear k rk lw)) w)
    /\ unshear k rk lw = (bc_language_dec_proj1 l).
Proof. 
  intros k.
  assert (H_chuck := IH_chuck k).
  destruct H_chuck as [rk H_chuck]. 
  exists rk.
  intros bcl lw H_base.
  split.
  - (* Proving theorem_the_first, essentially *)
    intro w.
    spec H_chuck bcl lw H_base.
    split; intro H.  
    + (* --> *) 
      unfold unshear, unshear_bool, shear_language.
      split. 
      2 : { spec H_base w. apply H_base.
            simpl. exact H. }
      rewrite is_member_correct.
      spec H_chuck (length w). 
      apply H_chuck. split. omega.
      spec H_base w.
      rewrite H_base in H.
      destruct H as [_ goal].
      exact goal.
    + (* <-- *)
      apply H_base. 
      unfold unshear, unshear_bool, shear_language in H.
      rewrite is_member_correct in H.
      destruct H as [H_in H_length].
      split. omega.
      spec H_chuck (length w).
      spec H_chuck w. rewrite H_chuck in H_in.
      destruct H_in as [_ goal].
      exact goal.
  - (* Proving theorem_the_second, essentially *) 
    spec H_chuck bcl lw H_base. 
    apply language_equality; intro w.
    split; intro H.
    + (* --> *)
      spec H_chuck (length w).
      spec H_chuck w. 
      unfold unshear, unshear_bool in H.
      rewrite is_member_correct in H.
      rewrite H_chuck in H.
      destruct H as [_ goal].
      exact goal. 
    + (* <-- *)
      unfold unshear, unshear_bool. rewrite is_member_correct.
      spec H_chuck (length w). apply H_chuck.
      split. omega. assumption.
Qed.

(** Step 2 : Proving that well-formed short languages are finite **) 
Definition is_finite {X : Type} (P : X -> Prop) : Prop :=
  exists L : list X, forall (x : X), In x L <-> P x.

(* Mini nifty subseq library *) 
Theorem behead_eq :
  forall (hd d : word) (lw : list word),
    behead lw d = hd ->
    (lw = [] /\ d = hd) \/
    exists tl, lw = hd :: tl.
Proof.
  intros.
  destruct lw.
  left. 
  split. reflexivity.
  compute in H. assumption.
  right. 
  simpl in H. subst. exists lw. reflexivity.
Qed.

Theorem subseq_cons :
  forall (l : list word) (hd : word) (tl : list word),
    subseq (hd :: tl) l ->
    subseq tl l.
Proof.
  induction l as [|hd tl IHl]; intros. 
  - apply subseq_nil_inversion in H. 
    inversion H.
  - inversion H; subst. clear H.
    apply subseq_hn. assumption.
    apply subseq_hn. 
    apply (IHl hd0 tl0). assumption.
Qed.

Theorem subseq_cons_or :
  forall (hd : word) (tl lw : list word),
    subseq lw (hd :: tl) ->
    subseq lw tl \/ exists tl', lw = hd :: tl' /\ subseq tl' tl. 
Proof.
  intros hd tl lw H_subseq.
  generalize dependent hd.
  generalize dependent tl. 
  induction lw; intros.
  left; constructor.
  inversion H_subseq; subst.
  - apply (subseq_cons _ hd) in H_subseq.
    spec IHlw tl hd H_subseq.
    destruct IHlw.
    right. exists lw. split.
    reflexivity. exact H.
    destruct H. 
    destruct H. right. exists lw.
    split. reflexivity. assumption.
  - left; assumption.
Qed.

Theorem subseq_finite :
  forall (l : list word),
    is_finite (fun s => subseq s l).
Proof.
  induction l as [|h tl IHl]. 
  - exists [ [] ].
    intro; split; intros.
    inversion H. subst; constructor.
    inversion H0. inversion H. unfold In. left; reflexivity.
  - destruct IHl as [llw IHl].
    exists (llw ++ map (fun lw => [h] ++ lw) llw).
    intro lw; split; intro H.
    + apply in_app_or in H.
      destruct H as [H_old | H_new].
      * rewrite IHl in H_old.
        apply subseq_hn. assumption.
      * apply in_map_iff in H_new.
        destruct H_new as [t [H_eq H_in]].
        subst lw.
        replace (h :: tl) with ([h] ++ tl) by easy.
        apply subseq_app. apply subseq_refl.
        apply IHl. assumption.
    + apply in_app_iff.
      replace (h :: tl) with ([h] ++ tl) in H by easy.
      apply subseq_cons_or in H. 
      destruct H as [left | right].
      apply IHl in left. left; assumption.
      destruct right as [right_tl [H_split H_subseq]].
      subst. right.
      apply in_map_iff. exists right_tl.
      split. trivial.
      apply IHl. assumption.
Qed.

Theorem is_finite_shortwords :
  forall (n : nat),
    is_finite (fun lw => subseq lw (generate_words_upto n)). 
Proof.
  intro n. 
  now apply (subseq_finite (generate_words_upto n)). 
Qed.                              

(* Languages that satisfy P in list L are finite *)
Lemma p_in_list_finite_dec : forall (P : word -> Prop) (L : list word) (Hdec : language_decidability P),
    is_finite (fun l => P l /\ In l L).
Proof.  
  intros P LS Hdec. 
  induction LS as [|new_x old_xes IHL].
  + (* In the base case, the candidate list is empty,
     so the finite list is also empty *)
    exists nil.
    intros x; split.
    intro H_in; split. inversion H_in. exact H_in.
    intro H; destruct H as [_ H_mem]; exact H_mem. 
  + (* In the inductive step, the candidate list grows by one x,
       and the new finite list must include it if it satisfies P *)
    destruct IHL as [L' IHL].
    destruct (Hdec new_x).
    ++ (* When new_x satisfies P *) 
      exists (new_x :: L'). 
      intros x; split; intros H_in.
      +++ apply in_inv in H_in;
            destruct H_in as [H_eq | H_in].
          split. rewrite H_eq in H; assumption.
          rewrite <- H_eq; apply in_eq.
          split. spec IHL x; destruct IHL as [left _];
                   spec left H_in. destruct left; assumption.
          apply in_cons.
          spec IHL x; destruct IHL as [left _].
          spec left H_in; destruct left; assumption.
      +++ destruct H_in. 
          apply in_inv in H1.
          destruct H1. rewrite H1; apply in_eq.
          apply in_cons. spec IHL x.
          destruct IHL as [_ IHL].
          apply IHL; split; assumption.
    ++ (* When new_x doesn't satisfy P, toss it out *)
      exists L'.
      intro x; split; intros H_in.
      +++ split. spec IHL x; destruct IHL as [IHL _];
            spec IHL H_in; destruct IHL; assumption. 
          apply in_cons.
          spec IHL x; destruct IHL as [IHL _];
            spec IHL H_in; destruct IHL; assumption.
      +++ destruct H_in as [H_P H_in].
          apply in_inv in H_in.
          destruct H_in as [H_absurd | H_in].
          subst x; contradiction.
          spec IHL x. apply IHL; split; assumption.
Qed.

Lemma is_finite_conj {X : Type} : forall (P : X -> Prop) (Q : X -> Prop),
    is_finite (fun l => P l) ->
    is_finite (fun l => P l /\ Q l). 
Proof.     
  intros P Q H_fin.
  destruct H_fin as [ls H_fin]. 
  assert (H_useful := p_in_list_finite Q ls).
  destruct H_useful as [LS H_useful]. 
  exists LS.
  intro l; spec H_fin l; spec H_useful l; split; intro H.
  - split;
    apply H_useful in H; destruct H as [H_Q H_in];
    apply H_fin in H_in; assumption.
  - destruct H as [H_P H_Q].
    apply H_fin in H_P.
    apply H_useful; split; assumption.
Qed.

Theorem is_finite_subseq_wf :
  forall (k rk : block_pumping_constant),
    is_finite (fun lw => subseq lw (generate_words_upto rk) /\
                      exists (l : bc_language_dec k), agreement_upto k rk l lw 0). 
Proof.   
  intros.
  now apply (is_finite_conj (fun lw => subseq lw (generate_words_upto rk))
                            (fun lw => exists (l : bc_language_dec k), agreement_upto k rk l lw 0)
                            (is_finite_shortwords rk)). 
Qed.

(* Extracting a list of words from a decidable language *)
Theorem shear_language_decidable :
  forall (l : language) (rk : nat) (l_dec : language_decidability l),
  forall w, shear_language rk l w \/ ~ shear_language rk l w.
Proof.
  intros l rk l_dec w. 
  unfold shear_language.
  assert (length w <= rk \/ length w > rk) by omega. 
  destruct H. destruct (l_dec w); tauto. 
  right. intro. omega. 
Qed.

Theorem get_list_shear_language :
  forall (l : language) (Hdec : language_decidability l) (rk : nat),
  exists (L : list word),
    forall (w : word), In w L <-> shear_language rk l w. 
Proof.
  intros l Hdec rk. 
  remember (generate_words_upto rk) as W.
  assert (forall w, shear_language rk l w -> In w W).
  { intros. destruct H. subst.
    apply generate_words_upto_correct. trivial. }
  assert (forall W1 W2,
             (forall w, In w W <-> In w (W1 ++ W2)) ->
             (exists L, sublist L W1
                   /\ forall w : word,
                   (In w L -> shear_language rk l w)
                   /\ (shear_language rk l w -> (In w L \/ In w W2)))).
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
      assert (Hsheardec := shear_language_decidable l rk Hdec a). 
      destruct Hsheardec. 
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
      destruct H4. subst. contradiction.
      right. assumption. }
  specialize (H0 W nil). spec H0.
  rewrite app_nil_r. split; trivial.
  destruct H0 as [L [? ?]]. exists L.
  intro w. spec H1 w. destruct H1. split; intro.
  apply H1, H3.
  apply H2 in H3. destruct H3. assumption. inversion H3. 
Qed. 

Theorem filter_subseq_correct :
  forall (l : list word) (f : word -> bool),
    subseq (filter f l) l.
Proof.
  induction l as [|hd tl IHl]; intros.
  intros. compute; constructor.
  spec IHl f.
  simpl.
  case_eq (f hd); intros.
  constructor; assumption.
  constructor; assumption. 
Qed.

Fixpoint intersect (l1 l2 : list word) :=
  match l1 with
  | hd :: tl => if is_member hd l2
               then hd :: intersect tl l2
               else intersect tl l2
  | [] => []
  end.

Theorem intersect_correctness :
  forall (l1 l2 : list word),
  forall w, In w (intersect l1 l2) ->
       In w l1 /\ In w l2.
Proof.
  intros l1 l2 w H_in.
  induction l1 as [|hd1 tl1 IHl1].
  - compute in H_in; inversion H_in.
  - simpl in H_in.
    case_eq (is_member hd1 l2); intro.
    + rewrite H in H_in.
      apply in_inv in H_in.
      destruct H_in as [H_eq | H_in].
      * subst.
        split. 
        apply in_eq.
        apply is_member_correct in H.
        assumption.
      * spec IHl1 H_in.
        destruct IHl1.
        split. apply in_cons; assumption.
        assumption.
    + rewrite H in H_in.
      spec IHl1 H_in. 
      destruct IHl1. split.
      apply in_cons; assumption. assumption.
Qed.

Theorem get_nodup_list_shear_language :
  forall (l : language) (Hdec : language_decidability l) (rk : nat),
  exists (L : list word),
    (subseq L (generate_words_upto rk)) /\
     forall (w : word), In w L <-> shear_language rk l w. 
Proof.
  intros l Hdec rk.
  assert (H_useful := get_list_shear_language l Hdec rk).
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
  unfold shear_language in H. destruct H.
  apply generate_words_upto_correct; assumption.
  assert (H_copy := H). 
  apply H_useful in H.
  apply andb_true_intro. split.
  unfold shear_language in H_copy. destruct H_copy.
  apply Nat.leb_le. assumption.
  rewrite is_member_correct. assumption. 
Qed. 

Theorem get_list_shear_bc_language :
  forall (k rk : block_pumping_constant) (l : bc_language_dec k) (Hdec : language_decidability (bc_language_dec_proj1 l)),
  exists (L : list word),
    (subseq L (generate_words_upto rk))  /\
    forall (w : word), In w L <-> shear_language rk (bc_language_dec_proj1 l) w. 
Proof.
  intros k rk l Hdec. 
  assert (H_useful := get_nodup_list_shear_language (bc_language_dec_proj1 l) Hdec rk).
  destruct H_useful as [L H_useful].
  exists L. assumption. 
Qed.

(** Step 3 : Grand finale! **) 
Theorem bc_dec_k_is_finite_nochoice :
    forall (k : block_pumping_constant),
    is_finite (bc_sigma_dec k).
Proof.
  intros k.  
  assert (H_blink := unshear_correctness k).
  destruct H_blink as [rk H_blink].
  assert (H_fin := is_finite_subseq_wf k rk).
  destruct H_fin as [llw about_llw]. 
  exists (map (unshear k rk) llw).
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
    rewrite H2.
    destruct bcl_witness.
    simpl. 
    assumption.
  + rewrite in_map_iff. 
    specialize (H_blink (exist _ l H)). 
    assert (H_getlist := get_list_shear_bc_language k rk (exist _ l H)).   
    destruct H_getlist as [wf_list [wf_subseq about_wf_list]].
    destruct H as [Hdec H]. simpl. red. now apply Hdec.
    exists wf_list. 
    assert (H_pre : agreement_upto k rk (exist (bc_sigma_dec k) l H) wf_list 0).
    { intros w. spec about_wf_list w.
      split; intro H_tmp.
      rewrite about_wf_list in H_tmp.
      unfold shear_language in H_tmp.
      destruct H_tmp as [H_in H_length].
      split. omega. assumption.
      destruct H_tmp. apply about_wf_list.
      unfold shear_language; split. assumption. omega. }
    spec H_blink wf_list H_pre. 
    destruct H_blink as [H1 H2].
    split. simpl in H2; assumption.
    apply about_llw. split.
    exact wf_subseq. exists (exist (bc_sigma_dec k) l H). assumption.
Qed.

Print Assumptions bc_dec_k_is_finite_nochoice.

(* Way 1 : definitional decidability of languages *)
(* Refer to lemma2nochoicebool.v *)

(* Way 2 : Law of Excluded Middle for language decidability *) 
Require Import Classical.

Theorem bc_k_is_finite_lem :
    forall (k : block_pumping_constant),
    is_finite (bc_sigma k).
Proof. 
  intro k.  
  replace (bc_sigma k) with (bc_sigma_dec k).
  apply bc_dec_k_is_finite_nochoice.
  unfold bc_sigma_dec, bc_sigma.
  apply functional_extensionality.
  intro l.
  apply prop_ext.
  split; intro H. 
  tauto. split. intro w; apply (classic (l w)).
  assumption.
Qed.

(* Way 3 : Explicit decision procedure for some language *) 
Parameter decider : forall (l : language), forall (w : word), l w \/ ~ l w. 

Theorem bc_k_is_finite_decider :
    forall (k : block_pumping_constant),
    is_finite (bc_sigma k).
Proof.
  intro k.  
  replace (bc_sigma k) with (bc_sigma_dec k).
  apply bc_dec_k_is_finite_nochoice.
  unfold bc_sigma_dec, bc_sigma.
  apply functional_extensionality.
  intro l.
  apply prop_ext.
  split; intro H. 
  tauto. split. intro w; apply decider.
  assumption.  
Qed.
