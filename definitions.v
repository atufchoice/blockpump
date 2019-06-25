Require Import List Logic Nat Omega Classical Decidable.
Import ListNotations.
From Block
Require Import lib finite.

Definition d : nat := 2337.

(* ********************* *)
(* **** Definitions **** *)
(* ********************* *)

Inductive T : Type :=
| aa : T
| bb : T
| cc : T.

(* Alphabet equality *) 
Definition T_eq (s1 s2 : T) : bool :=
  match s1, s2 with
  | aa, aa => true
  | bb, bb => true
  | cc, cc => true
  | _, _ => false
  end.

Theorem T_eq_refl :
  forall (s1 s2 : T),
    T_eq s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2; destruct s1, s2; split; intro H; try reflexivity;
    try unfold T_eq in H; inversion H.
Qed.

Definition word := list T.

(* Word equality *) 
Fixpoint word_eq (w1 w2 : word) : bool :=
  match w1, w2 with
  | [], [] => true
  | hd1 :: tl1, hd2 :: tl2 => if T_eq hd1 hd2
                             then word_eq tl1 tl2
                             else false
  | _, _ => false
  end.

Theorem word_eq_dec : forall (w1 w2 : word),
    decidable (word_eq w1 w2 = true).  
Proof.
  intros w1 w2.
  case word_eq. left. reflexivity.
  right. intro Hc. discriminate.
Qed.

Lemma word_eq_id : forall (w : word),
    word_eq w w = true.
Proof.
  intros w.
  induction w as [|hd tl IHtl].
  - unfold word_eq; reflexivity.
  - simpl.
    assert (T_eq hd hd = true).
    apply T_eq_refl; reflexivity.
    rewrite H. exact IHtl.
Qed.

Theorem word_eq_refl : forall (w1 w2 : word),
    word_eq w1 w2 = true <-> w1 = w2. 
Proof.
  induction w1 as [|hd1 tl1 IHtl1];
    induction w2 as [|hd2 tl2 IHtl2];
    split; intro H; try reflexivity; try inversion H.
  case_eq (T_eq hd1 hd2); [intro H_true | intro H_false]. 
  simpl in H. rewrite H_true in H. spec IHtl1 tl2.
  rewrite IHtl1 in H. rewrite H.
  rewrite T_eq_refl in H_true. rewrite H_true. reflexivity.
  rewrite H_false in H1.
  inversion H1. apply word_eq_id.
Qed.

Theorem word_eq_refl' : forall (w1 w2 : word),
    word_eq w1 w2 = false <-> w1 <> w2. 
Proof.
  intros.
  apply mirror_reflect. 
  apply word_eq_refl.
Qed. 

Theorem word_eq_dec' : forall x y : word, {x = y} + {x <> y}.
Proof.
  intros x y.
  case_eq (word_eq x y).
  intros H_true. left.
  rewrite word_eq_refl in H_true. 
  assumption.
  intros H_false. right.
  rewrite word_eq_refl' in H_false.
  assumption.
Qed.

Definition language : Type := word -> Prop. 

Definition language_decidability (l : language) := forall w, decidable (l w).

Lemma language_equality : forall l1 l2 : language,
    l1 = l2 <-> forall w : word, l1 w <-> l2 w.
Proof.
  intros l1 l2; split.
  intros H_leq w; split; intro H_mem. 
  rewrite H_leq in H_mem; assumption.
  rewrite <- H_leq in H_mem; assumption.
  intros.
  apply functional_extensionality. 
  intro w. spec H w.
  apply prop_ext. assumption.
Qed.

Lemma language_equality_sigma :
    forall (P : language -> Prop)
      (l1 : language) (H1 : P l1) (l2 : language) (H2 : P l2),
      (exist P l1 H1) = (exist P l2 H2) <-> l1 = l2. 
Proof.
  intros P l1 H1 l2 H2; split.
  - intro H_eq_dep.
    apply eq_sig_fst in H_eq_dep; assumption.
  - intro H_eq.
    subst. assert (H1 = H2) by eapply proof_irrelevance.
    rewrite H. reflexivity.
Qed.

(* Two versions of the derivative predicate *)
Definition is_deriv (L L_x : language) : Prop :=
  exists (x : word), forall (w : word), L_x w <-> L (x ++ w).

Definition is_derivative (L L' : language) : word -> Prop :=
  fun (x : word) => forall (w : word), L' w <-> L (x ++ w).

Definition derivative_of (L : language) (t : word) : language :=
  fun w => L (t ++ w). 

(* Defining equivalence classes for some language *) 
Definition equiv_classes_pred (ls : list language) :=
  forall L, In L ls -> forall w, In (derivative_of L w) ls. 
Definition equiv_classes : Type :=
  {ls : list language | equiv_classes_pred ls}.
Definition equiv_classes_proj1 (LS : equiv_classes) := proj1_sig LS. 
Coercion equiv_classes_proj1 : equiv_classes >-> list.

(* Library for language derivatives *)
Lemma chomp_deriv : forall (w : word) (L : language),
    L w = (derivative_of L w) []. 
Proof. 
  intros w L. unfold derivative_of;  
    rewrite app_nil_r; reflexivity.
Qed.

Lemma cat_deriv : forall (x y w : word) (L : language),
    (derivative_of (derivative_of L x) y) w = (derivative_of L (x ++ y)) w.
Proof.
  intros x y w L; unfold derivative_of; rewrite <- app_assoc; reflexivity.
Qed.

Lemma cat_cat_deriv : forall (x y z w : word) (L : language),
    (derivative_of (derivative_of L x) (y ++ z)) w =
    (derivative_of (derivative_of L (x ++ y)) z) w.
Proof.
  intros x y z w L.
  unfold derivative_of; rewrite <- app_assoc. 
  rewrite app_assoc. 
  reflexivity. 
Qed.

Lemma extend_deriv : forall (x y a : word) (L : language),
    (forall (w : word), 
        (derivative_of L x) w = (derivative_of L y) w) ->
    (forall (w : word), 
    (derivative_of L (x ++ a)) w = (derivative_of L (y ++ a)) w). 
Proof.
  intros x y a L H_eq w.
  do 2 rewrite <- cat_deriv. 
  unfold derivative_of in *.
  spec H_eq (a ++ w).
  assumption. 
Qed.

Lemma cat_deriv_proper :
  forall (x y : word) (L : language),
    derivative_of (derivative_of L x) y = derivative_of L (x ++ y). 
Proof.
  intros.
  apply language_equality. intro w. 
  assert (H_useful := cat_deriv x y w L).
  apply prop_ext_equiv. assumption.
Qed.

Lemma extend_deriv_proper : 
  forall (L : language) (x1 x2 : word),
    derivative_of L x1 = derivative_of L x2 ->
    forall (a : word),
      derivative_of L (x1 ++ a) = derivative_of L (x2 ++ a). 
Proof.
  intros L x1 x2 H_eq a.
  rewrite <- (cat_deriv_proper x1 a L). 
  rewrite <- (cat_deriv_proper x2 a L).
  rewrite H_eq; reflexivity.
Qed. 

(* ************************************************* *)
(* **** Myhill-Nerode formulation of regularity **** *)
(* ************************************************* *)
Definition regular (L : language) : Prop :=
  is_finite (is_deriv L).

(* ***************************** *)
(* **** Combining languages **** *)
(* ***************************** *)
Definition intersection_lang (l1 l2 : language) : language :=
  fun w : word => l1 w /\ l2 w.

Definition union_lang (l1 l2 : language) : language :=
  fun w : word => l1 w \/ l2 w.

Definition concat_lang (l1 l2 : language) : language :=
  fun w : word => exists w1 w2 : word, w = w1 ++ w2 /\ l1 w1 /\ l2 w2.

(* *********************************** *)
(* **** Block pumping definitions **** *)
(* *********************************** *)

(* Pumping a word n times *)
Fixpoint napp (n : nat) (w : word) : word :=
  match n with
  | 0 => []
  | S n' => w ++ napp n' w
  end.

Definition sublist {X} (w1 w2 : list X) :=
  forall x : X, In x w1 -> In x w2.

Definition cancelled_word (w : word) (i j : nat) : word :=
  firstn i w ++ skipn j w. 

Definition pumpable_block (i : nat) (j : nat) (w : word) :=
  firstn (j-i) (skipn i w).

Definition is_pump (l : language) (w : word) :=
  fun i j => forall m, l (firstn i w ++ napp m (pumpable_block i j w) ++ skipn j w).

Definition increasing (l : list nat) := 
  forall n m : nat, 
  n < m < (length l) -> 
  nth n l d < nth m l d.

(* Subset-types for pumping constants *)
Definition p_predicate (p : nat) := 
  p >= 2. 
	
Definition block_pumping_constant : Type :=
  { p : nat | p_predicate p}.

Definition p_proj1 (p : block_pumping_constant) : nat :=
  match p with
  | exist _ b _ => b
  end.

Coercion p_proj1 : block_pumping_constant >-> nat.

(* Subset-types for breakpoints *)
Definition breakpoint_set_predicate (bl : list nat) (w : word) (p : block_pumping_constant) := 
(* Size of breakpoints is pumping constant *)
length bl = p /\
(* Breakpoints have to be increasing *) 
increasing bl /\
(* The last breakpoint has to occur within the word *)
last bl d <= length w.

Definition breakpoint_set (p : block_pumping_constant) (w : word) : Type := 
  {bl : list nat | breakpoint_set_predicate bl w p}.
 
Definition bl_proj1 {p : block_pumping_constant} {w : word} (bl : breakpoint_set p w) : list nat :=
  match bl with 
  | exist _ b _  => b 
  end.  

Coercion bl_proj1 : breakpoint_set >-> list.

(* Subset-types for breakpoints *)
Definition breakpoint_predicate
           (i : nat) (p : block_pumping_constant) (w : word)
           (bl : breakpoint_set p w) := 
  In i (bl_proj1 bl).

Definition breakpoint {p : block_pumping_constant} {word : list T}
	   (bl : breakpoint_set p word) : Type :=
  {i : nat | breakpoint_predicate i p word bl}.

Definition bp_proj1 {p : block_pumping_constant} {w : word}
           {bl : breakpoint_set p w} (i : breakpoint bl) : nat :=
  match i with
| exist _ b _  => b 
 end.

Coercion bp_proj1 : breakpoint >-> nat.

Tactic Notation "destruct_bps" ident(bps) ident(about_name) :=
  destruct bps as [bps about_name];
  unfold breakpoint_set_predicate in about_name; simpl in *.

Tactic Notation "destruct_bp" ident(bp) ident(about_name) :=
  destruct bp as [bp about_name]; simpl in *. 

Definition bc_sigma_dec (k : block_pumping_constant) : language -> Prop :=
  fun L : language =>
    (forall (w : word), L w \/ ~ L w) /\
    forall (s : word),
    forall (bl : breakpoint_set k s),
    exists (i j : breakpoint bl),
      i < j /\ (L (firstn i s ++ skipn j s) <-> (L s)).

Definition bc_sigma (k : block_pumping_constant) : language -> Prop :=
  fun L : language =>
    forall (s : word),
    forall (bl : breakpoint_set k s),
    exists (i j : breakpoint bl),
      i < j /\ (L (firstn i s ++ skipn j s) <-> (L s)).

Definition bc_language_dec (k : block_pumping_constant) : Type :=
  { l | bc_sigma_dec k l}.

Definition bc_language_dec_proj1 {k : block_pumping_constant} (bcl : bc_language_dec k) :=
  match bcl with
  | exist _ b _ => b
  end.

Definition bc_language (k : block_pumping_constant) : Type :=
  { l | bc_sigma k l}.

Definition bc_language_proj1 {k : block_pumping_constant} (bcl : bc_language k) :=
  match bcl with
  | exist _ b _ => b
  end.

(* Library for breakpoints and breakpoint sets *)
(* Breakpoint sets are never empty *)
Lemma about_bps_nonempty :
  forall (k : block_pumping_constant) (w : word) (bps : breakpoint_set k w),
    bl_proj1 bps <> [].
Proof.
  intros k w bps absurd.
  destruct k as [k about_k].
  unfold p_predicate in about_k.
  destruct_bps bps about_bps.
  destruct about_bps as [H_length [H_incr H_last]].
  apply length_zero_iff_nil in absurd.
  rewrite absurd in H_length; omega. 
Qed.

(* Breakpoints never spill over their word *)
Lemma about_bp_length :
  forall (k : block_pumping_constant) w (bps : breakpoint_set k w) (bp : breakpoint bps), bp <= length w.
Proof. 
  intros k w bps bp.
  destruct bp as [bp H_in].
  destruct bps as [bps [H_length [H_incr H_last]]]. 
  simpl in *.
  apply (In_nth bps bp d) in H_in.
  destruct H_in as [i [H_lt H_pos]].
  rewrite <- H_pos.
  unfold increasing in H_incr.
  apply (Nat.le_trans (nth i bps d)
                      (last bps d)
                      (length w)). 
  apply about_incr_nth_last. exact H_incr.
  exact H_lt.
  assumption. 
Qed.

(* Distance between breakpoints is less than word length *) 
Lemma about_bp_distance :
  forall (k : block_pumping_constant) w (bps : breakpoint_set k w) (bp1 bp2 : breakpoint bps),
    bp1 < bp2 -> bp1 + (length w - bp2) < length w. 
Proof.
  intros k w bps bp1 bp2 H_lt.
  destruct bp1 as [bp1 H_in1].
  destruct bp2 as [bp2 H_in2].
  destruct bps as [bps [H_length [H_incr H_last]]]. 
  simpl in *.
  assert (bp1 <> bp2) by omega.
  rewrite Nat.add_sub_assoc.
  rewrite plus_comm.
  replace (length w + bp1 - bp2) with (length w - (bp2 - bp1)) by omega. 
  apply inane_helper.
  apply (In_nth bps bp2 d) in H_in2.
  destruct H_in2 as [i H_in2].
  assert (H_useful := about_incr_nth_last d bps H_incr i).
  destruct H_in2. spec H_useful H0.
  assert (bp2 <= length w) by omega.
  split; omega.
  apply (In_nth bps bp2 d) in H_in2.
  destruct H_in2 as [i H_in2].
  assert (H_useful := about_incr_nth_last d bps H_incr i).
  destruct H_in2. spec H_useful H0.
  omega.
Qed.

(* Pump between breakpoints is less than word length *) 
Lemma about_pump_length :
  forall (k : block_pumping_constant) w (bps : breakpoint_set k w) (bp1 bp2 : breakpoint bps),
    bp1 < bp2 -> length (firstn bp1 w ++ skipn bp2 w) < length w.
Proof.
  intros.
  rewrite app_length.
  rewrite firstn_length_le.
  rewrite about_length_skipn. 
  apply (about_bp_distance k w bps bp1 bp2).
  destruct bp1 as [bp1 H_in1].
  destruct bp2 as [bp2 H_in2].
  destruct bps as [bps [H_length [H_incr H_last]]]. 
  simpl in *.
  assumption. 
  apply about_bp_length.
Qed.

Lemma left_mid : forall (w : word) (a b : nat),
    a < b <= length w -> firstn a w ++ pumpable_block a b w = firstn b w. 
Proof.
  intros w a. revert w.
  induction a; simpl; intros.
  unfold pumpable_block. simpl. f_equal. omega.
  destruct w. exfalso. simpl in H. omega.
  destruct b. exfalso. omega.
  simpl. f_equal.
  spec IHa w b. spec IHa. simpl in H. omega.
  rewrite <- IHa. reflexivity.
Qed.

(* All breakpoints for some word 
   can be breakpoints for some longer word *)
Lemma bp_to_longer_word :
  forall (k : block_pumping_constant) (w w' : word)
    (bps : breakpoint_set k w)
    (bp1 bp2 : breakpoint bps),
    length w < length w' ->
    exists (bps' : breakpoint_set k w'),
      breakpoint_predicate bp1 k w' bps'
      /\ breakpoint_predicate bp2 k w' bps'.
Proof.
  intros k w w' bps bp1 bp2 H_length.
  assert (H_useful : breakpoint_set_predicate bps w' k).
  { unfold breakpoint_set_predicate.
    destruct_bps bps about_bps;
      destruct about_bps as [H_l [H_last H_incr]];
      simpl in *. 
    split. assumption. split. assumption.
    omega. }
  destruct_bps bps about_bps.
  exists (exist _ bps H_useful).
  destruct_bp bp1 about_bp1;
    destruct_bp bp2 about_bp2;
  unfold breakpoint_predicate in *; simpl in *.
  split; assumption.  
Qed.

(* All breakpoint sets for a shorter word 
   can be breakpoint sets for a longer word *) 
Lemma bps_to_longer_word :
  forall (k : block_pumping_constant) (w w' : word)
    (bps : breakpoint_set k w),
    length w <= length w' ->
    breakpoint_set_predicate (proj1_sig bps) w' k.
Proof.     
  intros k w w' bps H_le.
  apply le_lt_or_eq in H_le.
  destruct_bps bps about_bps;
      destruct about_bps as [H_length [H_incr H_last]]. 
  destruct H_le as [H_lt | H_eq]. 
  - split. assumption.
    split. assumption.
    simpl in *; omega.
  - split. assumption.
    split. assumption.
    rewrite <- H_eq; assumption.  
Qed.

(* If we have a shorter word w and a longer word w', 
   and a breakpoint set for longer word w', 
   and two breakpoints from this set for w', 
   then they are also breakpoints for shorter word w. *) 
Lemma bp_to_shorter_word :
  forall (k : block_pumping_constant) (w w' : word)
    (bps : breakpoint_set k w')
    (H2 : breakpoint_set_predicate (proj1_sig bps) w k)
    (bp1 bp2 : breakpoint bps),
    length w < length w' ->
    breakpoint_predicate bp1 k w (exist (fun bps => breakpoint_set_predicate bps w k) bps H2)
    /\ breakpoint_predicate bp2 k w (exist (fun bps => breakpoint_set_predicate bps w k) bps H2).
Proof.
  intros k w w' bps H bp1 bp2 H_length.
  destruct_bps bps about_bps. 
  destruct_bp bp1 about_bp1;
    destruct_bp bp2 about_bp2;
    unfold breakpoint_predicate in *;
    simpl in *.
  split; assumption.
Qed.

Definition behead {X : Type} (l : list X) (d : X) : X :=
  match l with 
  | h :: tl => h
  | [] => d
  end.

Program Definition get_bp1_from_bps {w : word} {k : block_pumping_constant}
        (bps : breakpoint_set k w) : {bp | breakpoint_predicate bp k w bps} :=
  exist (fun i => breakpoint_predicate i k w bps) (behead (bl_proj1 bps) 0) _.
Next Obligation.
  unfold breakpoint_predicate.
  destruct bps as [bps about_bps].
  unfold breakpoint_set_predicate in about_bps.
  destruct about_bps as [H_length [H_incr H_last]].
  simpl. destruct bps.
  destruct k as [k about_k].
  unfold p_predicate in about_k. simpl in H_length. omega.
  destruct bps.
  destruct k as [k about_k].
  unfold p_predicate in about_k. simpl in H_length. omega.
  unfold behead. simpl. left; reflexivity.
Defined.

Program Definition get_bp2_from_bps {w : word} {k : block_pumping_constant}
        (bps : breakpoint_set k w) : {bp | breakpoint_predicate bp k w bps} :=
  exist (fun i => breakpoint_predicate i k w bps) (behead (tl (bl_proj1 bps)) 0) _.
Next Obligation.
  unfold breakpoint_predicate.
  destruct bps as [bps about_bps].
  unfold breakpoint_set_predicate in about_bps.
  destruct about_bps as [H_length [H_incr H_last]].
  simpl. destruct bps.
  destruct k as [k about_k].
  unfold p_predicate in about_k. simpl in H_length. omega.
  destruct bps.
  destruct k as [k about_k].
  unfold p_predicate in about_k. simpl in H_length. omega.
  unfold behead. simpl. right; left; reflexivity. 
Defined.

(* Property only applies to L *) 
Definition block_pumpable_with (k : block_pumping_constant) (L : language) :=
  forall (w : word), L w ->
                  forall (bl : breakpoint_set k w),
                  exists (i j : breakpoint bl), i < j /\
                                           (forall m : nat, L (firstn i w ++ napp m (pumpable_block i j w) ++ skipn j w)).

Definition block_cancellable_with (k : block_pumping_constant) (L : language) :=
  forall (w : word), L w ->
                   forall (bl : breakpoint_set k w),
                   exists (i j : breakpoint bl), i < j /\
                                            L (firstn i w ++ skipn j w).

(* Property applies to both L and L complement *) 
Definition block_pumpable_matching_with (k : block_pumping_constant) (L : language) :=
  forall (w : word),
  forall (bl : breakpoint_set k w),
  exists (i j : breakpoint bl), i < j /\
                           (forall m : nat, L (firstn i w ++ napp m (pumpable_block i j w) ++ skipn j w) <-> L w).

Definition block_cancellable_matching_with (k : block_pumping_constant) (L : language) :=
  forall (w : word),
  forall (bl : breakpoint_set k w),
  exists (i j : breakpoint bl), i < j /\ (L (firstn i w ++ skipn j w) <-> L w).

(* *************************** *)
(* **** Combustion lemmas **** *)
(* *************************** *)

(* You can only insert n breakpoints into words of length n *)
(* If all the words are of length less than k - 1, then you cannot insert
   k breakpoints *)
Lemma block_cancellable_explosion : forall (k : block_pumping_constant) (L : language),
    (forall w : word, L w -> length w < k-1) ->
    block_cancellable_with k L.
Proof.
  intros k L H_length w H_mem absurd_bps.
  spec H_length w. 
  spec H_length H_mem.
  destruct_bps absurd_bps about_absurd_bps.
  destruct about_absurd_bps as [H_absurd_length [H_incr H_last]].
  assert (H_useful := Nat.le_lt_trans (last absurd_bps d) (length w) (k-1)).
  spec H_useful H_last H_length.
  assert (H_obv : absurd_bps <> []).
  { destruct k as [k about_k]; unfold p_predicate in about_k.
    simpl in H_absurd_length. intro absurd. apply length_zero_iff_nil in absurd.
    omega. }  
  assert (H_contradiction := about_incr_length_last k d absurd_bps H_obv H_absurd_length H_incr).
  omega (* Contradiction *).
Qed.

Lemma breakpoint_explosion_two : forall (k : block_pumping_constant) (w : word),
    length w <= k-2 ->
    forall (l : list nat), 
    breakpoint_set_predicate l w k -> False.
Proof.
  intros k w H_word absurd H_bps.
  assert (H_non_empty :=  about_bps_nonempty k w (exist (fun l => breakpoint_set_predicate l w k) absurd H_bps));
  simpl in H_non_empty. 
  unfold breakpoint_set_predicate in H_bps.
  destruct H_bps as [H_length [H_incr H_last]].
  assert (H_useful := about_incr_length_last k d absurd H_non_empty H_length H_incr).
  assert (H_useful' := Nat.le_trans (last absurd d)
                                    (length w)
                                    (k-2)
                                    H_last H_word). 
  clear -H_useful H_useful'.
  destruct k as [k about_k];
    unfold p_predicate in about_k; simpl in *; omega  (* Contradiction! *). 
Qed.

Lemma breakpoint_explosion_one : forall (k : block_pumping_constant) (w : word),
    length w < k-1 ->
    forall (l : list nat), 
      breakpoint_set_predicate l w k -> False.
Proof.
  intros k w H_word absurd H_bps.
  assert (H_non_empty :=  about_bps_nonempty k w (exist (fun l => breakpoint_set_predicate l w k) absurd H_bps));
  simpl in H_non_empty. 
  unfold breakpoint_set_predicate in H_bps.
  destruct H_bps as [H_length [H_incr H_last]].
  assert (H_useful := about_incr_length_last k d absurd H_non_empty H_length H_incr).
  assert (H_useful' := Nat.le_lt_trans (last absurd d)
                                       (length w)
                                       (k-1)
                                       H_last H_word). 
  clear -H_useful H_useful'.
  destruct k as [k about_k];
    unfold p_predicate in about_k; simpl in *; omega  (* Contradiction! *). 
Qed.