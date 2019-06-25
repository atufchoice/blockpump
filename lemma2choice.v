Require Import List Logic Nat Omega FunctionalExtensionality ExtensionalityFacts ChoiceFacts Wellfounded Classical.
Require Import Compare_dec EqNat Decidable ListDec FinFun.
Require Fin. 
Import ListNotations.
From Block  
Require Import finite lib definitions ramsey. 

(* ********************* *)
(* **** Finite-hood **** *)
(* ********************* *)

(* Words up to length n are finite *)  
Lemma wordlength_finite : forall (n : nat),
    is_finite (fun (w : word) => length w <= n).
Proof.
  unfold is_finite. 
  induction n as [|n IHn].  
  + (* When length is zero, finite because no words exist *)
    exists [[]; []]. intro w; split.
    (* Left direction *) 
    ++ intro H_absurd; inversion H_absurd.
       rewrite <- H; reflexivity.
       inversion H. 
       rewrite <- H0; reflexivity. inversion H0. 
    (* Right direction *) 
    ++ intro H_length; inversion H_length.
       rewrite length_zero_iff_nil in H0.
       rewrite H0. constructor. reflexivity. 
  + (* When the length is n, finite because adding an extra symbol
       onto all words in a finite list of words keeps the list finite *)  
    destruct IHn as [L IHn].
    exists (map (fun w => aa :: w) L ++ 
           map (fun w => bb :: w) L ++ 
           map (fun w => cc :: w) L ++ L).
    intro w; split; intros H.
    (* Left direction *) 
    ++ repeat rewrite in_app_iff in H; 
         repeat rewrite in_map_iff in H.  
       destruct H as [[h [H_h H_mem]] |
                      [[h [H_h H_mem]] |
                       [[h [H_h H_mem]] | ?]]]. 
       (* When the word is in appended original list *) 
       +++ spec IHn h. 
           rewrite <- H_h.
           apply IHn in H_mem.
           rewrite unfold_length_S.
           apply (le_n_S (length h) n); exact H_mem.
       +++ spec IHn h. 
           rewrite <- H_h.
           apply IHn in H_mem.
           rewrite unfold_length_S.
           apply (le_n_S (length h) n); exact H_mem.
       +++ spec IHn h. 
           rewrite <- H_h.
           apply IHn in H_mem.
           rewrite unfold_length_S.
           apply (le_n_S (length h) n); exact H_mem.
       (* When the word is in the original list *) 
       +++ constructor.
           spec IHn w.
           apply IHn in H.
           exact H.
    (* Right direction *) 
    ++ repeat rewrite in_app_iff; repeat rewrite in_map_iff.
       apply le_lt_or_eq in H.
       destruct H as [H_lt | H_eq].
       +++ spec IHn w.
           apply lt_n_Sm_le in H_lt.
           apply IHn in H_lt.
           right; right; right; exact H_lt. 
       +++ destruct w. 
           inversion H_eq.
           spec IHn w.
           rewrite unfold_length_S in H_eq.
           apply Nat.succ_inj in H_eq.
           rewrite H_eq in IHn.
           assert (n <= n) by omega.
           apply IHn in H.
           destruct t.
           left; exists w.
           split; try reflexivity; assumption.
           right; left; exists w; split; try reflexivity; assumption.
           right; right; left; exists w; split; try reflexivity; assumption.
Qed.

Definition grow_lang (L : language) (new : word) : language :=
  fun w => L w \/ w = new.

(* Languages containing words in some finite set of words are finite *) 
Lemma shortlang_finite : forall (LW : list word),
    is_finite (fun L : word -> Prop => forall w : word, L w -> In w LW).
Proof.
  intros LW.  
  induction LW as [|hd tl IHl].
  (* When the list of words is empty, the language is empty *) 
  + exists ((fun w : word => False) :: nil).
    intro L; split.
    ++ intros H w H_mem.
       inversion H.
       rewrite <- H0 in H_mem.
       contradiction.
       inversion H0. 
    ++ intro H.
       unfold In.
       left. apply functional_extensionality.
       intro abword.
       apply prop_ext. split.
       intro false; inversion false.
       intro Habsurd; spec H abword; apply H in Habsurd.
       inversion Habsurd.
  (* When the list of words is non-empty, *) 
  + destruct IHl as [LS IHl].  
    (* LS is a list of languages containing only words in tl *)
    (* Now I need to construct a list of languages containing words in hd :: tl *)
    unfold is_finite.
    exists (LS ++ (map (fun L => grow_lang L hd) LS)).
    
    intros lang; split; intros.
    simpl. 
    apply in_app_or in H.
    destruct H. 
    right.
    (* *)
    spec IHl lang. destruct IHl. spec H1 H. apply H1. exact H0.
    case_eq (word_eq hd w); intro.
    left. rewrite word_eq_refl in H1. assumption. right.
    rewrite in_map_iff in H.
    destruct H as [lang' [? ?]].
    spec IHl lang'.  
    rewrite IHl in H2. apply H2. unfold grow_lang in H.
    subst lang. destruct H0. assumption.
    rewrite word_eq_refl' in H1. symmetry in H; contradiction.
    apply in_or_app.    
    destruct (classic (lang hd)).    
    right.
    rewrite in_map_iff. 
    set (lang' := fun w => lang w /\ w <> hd).
    exists lang'.
    split.
    unfold grow_lang, lang'.
    apply functional_extensionality. intro w. apply prop_ext; split; intro.
    destruct H1. tauto. rewrite H1. apply H0.
    case_eq (word_eq w hd); intro.
    right. rewrite word_eq_refl in H2. assumption.
    rewrite word_eq_refl' in H2. tauto. 
    rewrite IHl.
    intros.
    spec H w.
    unfold lang' in H1. destruct H1.
    spec H H1. destruct H; auto.
    symmetry in H. contradiction.
    left. 
    apply IHl.
    intros.
    spec H w H1. destruct H. 2 : auto. subst hd. contradiction.
Qed.


(* ******************* *)
(* **** Factories **** *)
(* ******************* *)

(* A function which takes a language and returns a language
   which only accepts the short strings from that language *)
(* Wrong version had an extra universal quantifier *) 
Definition filter_shortlang (n : nat) : language -> language :=
  fun L : language => (fun w : word => L w /\ length w <= n).

(* Sanity check for filter_shortlang *)
Lemma filter_shortlang_sane :
  forall n1 n2,
    n1 < n2 ->
    forall (L : language) (w : word), 
      filter_shortlang n1 L w -> filter_shortlang n2 L w.
Proof.
  intros n1 n2 H_lt L w H_in_longer. 
  unfold filter_shortlang in *. 
  destruct H_in_longer; split; try assumption.
  omega.
Qed. 


(* ************************* *)
(* **** Proving two-ish **** *)
(* ************************* *)

Definition is_cancellable (L : language) (w : word) :=
  fun i j => L (firstn i w ++ skipn j w). 

Lemma twoish_two : forall k : block_pumping_constant, 
    exists rk : block_pumping_constant,
      forall L1 L2 : language, 
        block_cancellable_matching_with k L1 ->
        block_cancellable_matching_with k L2 ->
        (forall w, length w <= rk ->
              L1 w <-> L2 w) ->
        forall w, L1 w <-> L2 w.
Proof.
  intros k. 
  assert (H_ramsey := Theorem_of_Ramsey_duo_prop k). 
  destruct H_ramsey as [rk [H_lt H_ramsey]]. 
  exists rk. 
  intros L1 L2 H_L H_L' H_length w. 
  (** Setting the strong induction on word length **)
  remember (length w) as n.  
  assert (H_move := Nat.eq_refl (length w)).
  rewrite <- Heqn in H_move at 2. clear Heqn. 
  generalize dependent w. 
  induction n as [|n IHn] using strong_induction; intros w H_w_length.
  - (* In the trivial base case *)
    spec H_length w.
    assert (0 <= rk) by omega.
    rewrite H_w_length in H_length; spec H_length H; assumption.
  - (* In the inductive case, with all shorter words satisfying P *)
    assert (n < rk \/ n >= rk) by omega.
    destruct H as [H_short | H_long].
    + (* In the case that the words are shorter than rk, trivial *)
      assert (length w <= rk) by omega.
      spec H_length w H; assumption. 
    + (* In the case that the words are longer than rk, but all shorter words satisfy *)
      (** Constructing a (breakpoint_set rk w d) which enumerates all the slots *)
      remember (iota 1 rk) as bp_list.
      assert (bp_list_pred : breakpoint_set_predicate bp_list w rk).
      rewrite Heqbp_list.
      { unfold breakpoint_set_predicate; split.
        rewrite length_iota; reflexivity.
        split.
        apply (iota_increasing 1 rk definitions.d).
        assert (H_useful := last_indep (iota 1 rk)).
        destruct H_useful as [H_absurd | H_useful]. 
        destruct H_absurd as [H_absurd _].
        subst bp_list.
        assert (rk >= 1).
        { destruct k as [k about_k]; unfold p_predicate in about_k.
          simpl in H_lt; omega. }
        assert (length (iota 1 rk) = rk) by apply length_iota.
        rewrite H_absurd in H0.
        unfold length in H0; omega.
        destruct H_useful as [H_non_nil H_useful].
        spec H_useful definitions.d 0.
        rewrite H_useful.
        rewrite iota_last. omega. } 
      (* Explicitly tell Coq the sigma-type here - must remember! *)
      spec H_ramsey w (exist _ bp_list bp_list_pred : breakpoint_set rk w). 
      (** Trying Ramsey's Theorem with two colors **)
      spec H_ramsey (is_cancellable L1 w). 
      (* Setting up the context variables for the case analysis *)
      destruct H_ramsey as [bps' H_ramsey].
      simpl in * (* Bookkeeping to refold the sigma-types *).
      assert (IHn' := IHn).
      spec H_L w bps'; spec H_L' w bps';
      destruct H_L as [bp1 [bp2 [H_bp_lt H_L]]];
      assert (H_bc1 : length (firstn bp1 w ++ skipn bp2 w) < length w).
      apply about_pump_length; assumption.
      spec IHn (length (firstn bp1 w ++ skipn bp2 w));
      rewrite <- H_w_length in IHn; spec IHn H_bc1;
      spec IHn (firstn bp1 w ++ skipn bp2 w)
           (eq_refl (length (firstn bp1 w ++ skipn bp2 w))).
      destruct H_L' as [bp1' [bp2' [H_bp'_lt H_L']]];
      assert (H_bc2 : length (firstn bp1' w ++ skipn bp2' w) < length w).
      apply about_pump_length; assumption.
      spec IHn' (length (firstn bp1' w ++ skipn bp2' w));
      rewrite <- H_w_length in IHn'; spec IHn' H_bc2;
      spec IHn' (firstn bp1' w ++ skipn bp2' w)
           (eq_refl (length (firstn bp1' w ++ skipn bp2' w))).
      clear -H_ramsey H_bp_lt H_bp'_lt H_L H_L' IHn IHn' H_bp_lt. 
      (* Case analysis on additional information about breakpoints *) 
      destruct H_ramsey as [H_sublist [case1 | case0]].  
      ++ (* Ramsey cancels word into L1 *)
        (* L2's breakpoints also work for L1 *)
        split; intro H.
        spec case1 bp1' bp2' H_bp'_lt;
          unfold is_cancellable in case1; tauto.
        spec case1 bp1 bp2 H_bp_lt;
          unfold is_cancellable in case1; tauto. 
      ++ (* Ramsey cancels word into L2 *)
        (* L1's breakpoints work for itself *)
        split; intro H.
         spec case0 bp1 bp2 H_bp_lt;
          unfold is_cancellable in case0; tauto.
        spec case0 bp1' bp2' H_bp'_lt;
          unfold is_cancellable in case0; tauto.
Qed.

(* ***************** *)
(* **** Lemma 2 **** *)
(* ***************** *)

(* inj_finite
     : forall (P : X -> Prop) (Q : Y -> Prop)
         (f : {x : X | P x} -> {y : Y | Q y}),
       inhabited {x : X | P x} ->
       injective P Q f ->
       is_finite_dep Q -> 
       is_finite_dep P *)

(* We require the following building blocks for our grand finale: 
   X : {l | BC(k,l)} 
   Y : {l | short_lang l} 
   P : BC(k)
   Q : short 
   f : dependent length shearing function 
   injective f 
   is_finite Q
   inhabited X 
 *)

(*****)
(* P *)
(*****)

(* This line causes Coq universe inconsistency! 
Coercion bc_language_proj1 : bc_language >-> language. *) 

(***************)
(* inhabited X *)
(***************)
Lemma inhabited_bc : forall k : block_pumping_constant, inhabited (bc_language k).
Proof.
  intros k.
  (* Constructing an absurd language that can still have breakpoints *) 
  remember ((fun w => False) : language) as absurd. 
  assert (bc_sigma k absurd).
  { unfold bc_sigma. intros w bps.
    exists (get_bp1_from_bps bps).
    exists (get_bp2_from_bps bps).
    split.
    unfold get_bp1_from_bps, get_bp2_from_bps.
    simpl.
    destruct bps as [x about_bps]. 
    (* Destruction/inversion until I reveal two elements *)
    destruct x as [_ | x].
    { unfold breakpoint_set_predicate in about_bps.
      destruct k as [k about_k]; unfold p_predicate in about_k.
      destruct about_bps as [H_length H_incr H_last].
      simpl in H_length. omega. }
    destruct x0 as [_ | x0].
    { unfold breakpoint_set_predicate in about_bps.
      destruct k as [k about_k]; unfold p_predicate in about_k.
      destruct about_bps as [H_length H_incr H_last].
      simpl in H_length. omega. }
    simpl.
    unfold breakpoint_set_predicate in about_bps.
    destruct about_bps as [H_length [H_incr H_last]].
    unfold increasing in H_incr.
    spec H_incr 0 1.
    assert (0 < 1 < length (x::x0::x1)). simpl; omega.
    spec H_incr H.
    unfold nth in H_incr. assumption.
    split; intro H_absurd_mem;
      subst absurd; contradiction. } 
  (* Finally we have our witness *)
  constructor. exists absurd. assumption.
Qed.

(*****) (*****)
(* Y *) (* Q *)
(*****) (*****)
Definition is_short_lang (n : nat) (L: language) : Prop :=
  forall w : word, L w -> length w <= n.

Definition short_lang (n : nat) : Type :=
  { l | is_short_lang n l}. 

Definition short_lang_proj1 {n : nat} (sl : short_lang n) :=
  match sl with
  | exist _ b _ => b
  end.

(*****)
(* f *)
(*****)
Program Definition filter_shortbclang (k : block_pumping_constant) (rk : block_pumping_constant) :=
  fun bcl : {l | bc_sigma k l} => exist (is_short_lang rk)
                                     (filter_shortlang rk (bc_language_proj1 bcl))
                                     _.
Next Obligation.  
  unfold is_short_lang, filter_shortlang;
    intros; unfold bc_language_proj1;
      destruct H0; assumption. 
Defined.
(* filter_shortbclang
     : forall k rk : nat,
       {l : language | bc_sigma k l} -> {x : language | short_lang rk x} *)

(***************)
(* injective f *)
(***************)
(** This is the real statement of injectivity we want! **)
(** Significantly, the precise way rk is dependent is super important **)
Lemma twoish_sigma : forall k : block_pumping_constant, 
    exists rk : block_pumping_constant,
      forall BCL1 BCL2 : bc_language k, 
        block_cancellable_matching_with k (proj1_sig BCL1) ->
        block_cancellable_matching_with k (proj1_sig BCL2) ->
        (forall w, length w <= rk ->
              (proj1_sig BCL1 w <-> proj1_sig BCL2 w)) ->
        forall w, proj1_sig BCL1 w <-> proj1_sig BCL2 w.
Proof.
  intro k.
  assert (H_useful := twoish_two k).
  destruct H_useful as [rk H_useful].
  exists rk.
  intros BCL1 BCL2.
  destruct BCL1 as [L1 about_L1];
    destruct BCL2 as [L2 about_L2].
  spec H_useful L1 L2.
  spec H_useful about_L1 about_L2.
  simpl in *.
  intros _ _ H w. 
  spec H_useful H.
  exact (H_useful w). 
Qed.

Theorem real_injectivity :
  forall (k : block_pumping_constant),
  exists rk : block_pumping_constant,
    injective (block_cancellable_matching_with k)
              (is_short_lang rk)
              (filter_shortbclang k rk). 
Proof.
  intros k. 
  assert (H_twoish := twoish_sigma k).
  (* Using the sigma version doesn't prevent us from being destructive *) 
  destruct H_twoish as [rk H_twoish].
  exists rk.
  unfold injective, Injective. 
  intros bcx bcy H_length.
  spec H_twoish bcx bcy.  
  (* However, in order to use our equality lemma we must destruct *)
  destruct bcx as [l1 about_l1];
    destruct bcy as [l2 about_l2].
  spec H_twoish about_l1 about_l2. 
  (* Two dependent languages are equal iff the languages are equal *) 
  apply language_equality_sigma. 
  simpl in *.
  (* Two languages are equal iff forall words, they agree *) 
  apply language_equality.
  (* Now we have the exact conclusion of H_twoish *) 
  assert (H_next : forall w : word, length w <= rk -> l1 w <-> l2 w).
  { (* This needs to be proven using H_length *)
    (* What does it mean for languages to be equal? *)
    intros w w_length.
    apply language_equality_sigma in H_length.
    unfold bc_language_proj1 in H_length.
    rewrite (language_equality (filter_shortlang rk l1)
                               (filter_shortlang rk l2)) in H_length.
    unfold filter_shortlang in H_length.
    spec H_length w.
    destruct H_length.
    split; intros.
    assert (H_away : l1 w /\ length w <= rk). split; assumption. 
    spec H H_away; destruct H; assumption.
    assert (H_away : l2 w /\ length w <= rk). split; assumption.
    spec H0 H_away; destruct H0; assumption. }
  apply (H_twoish H_next).
Qed.

(************)
(* finite Q *)
(************)
Lemma is_finite_sheared : forall n : nat,
    is_finite (is_short_lang n). 
Proof.
  intro n.
  destruct (wordlength_finite n) as [ws about_ws].
  destruct (shortlang_finite ws) as [ls about_ls].
  exists ls.
  intro l; split.
  intros H_l_mem w H_mem.
  apply (about_ws w).
  spec about_ls l.
  destruct about_ls.
  apply (H H_l_mem w); assumption.
  intro H.
  spec about_ls l. destruct about_ls.
  apply H1. intros w H_l_mem.
  spec H w. spec H H_l_mem.
  spec about_ws w. destruct about_ws.
  apply H3; assumption.  
Qed.

(* Enter magical finite library! *)
Lemma is_finite_sheared_dep : forall n : nat,
    is_finite_dep (is_short_lang n).  
Proof.
  intro n.
  assert (H_useful := is_finite_sheared n).
  apply list_to_dep_list in H_useful. 
  assumption. 
Qed.

(*****************)
(* Grand finale! *)
(*****************)
Theorem bc_k_is_finite_dep :
  forall k : block_pumping_constant, is_finite_dep (bc_sigma k).
Proof.
  intro k.
  assert (H_real := real_injectivity k).
  destruct H_real as [rk H_real].
  generalize (is_finite_sheared_dep rk).
  eapply (inj_finite 
            (bc_sigma k) (is_short_lang rk) (filter_shortbclang k rk)).
  apply inhabited_bc.
  exact H_real. 
Qed.

Theorem bc_k_is_finite :
  forall k : block_pumping_constant, is_finite (bc_sigma k).
Proof. 
  intro k.
  apply (is_finite_equiv (bc_sigma k)).
  exact (bc_k_is_finite_dep k). 
Qed.

Print Assumptions bc_k_is_finite. 
  