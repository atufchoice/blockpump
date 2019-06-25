Require Import List Nat Omega ExtensionalityFacts.
Import ListNotations.
From Coq
Require Import ssreflect. 

Tactic Notation "spec" hyp(H) := 
  match type of H with ?a -> _ => 
  let H1 := fresh in (assert (H1: a); 
  [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) := 
  (generalize (H a); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) := 
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) := 
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) := 
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) := 
  (generalize (H a b c d e); clear H; intro H).

(* **************** *)
(* **** Axioms **** *)
(* **************** *)

Axiom functional_extensionality : forall X Y (f g : X -> Y),
    (forall x : X, f x = g x) ->
    f = g.

Axiom prop_ext: forall P Q : Prop, P <-> Q -> P = Q.

(* ************************ *)
(* **** Library lemmas **** *)
(* ************************ *)

(* **** Logic **** *)
Lemma mirror_reflect: forall X (f : X -> bool) (P : X -> Prop),
  (forall x : X, f x = true <-> P x) ->
  (forall x : X, f x = false <-> ~P x).
Proof.
  split; repeat intro.
  + rewrite <- H in H1. rewrite H0 in H1. discriminate.
  + specialize (H x). destruct (f x). 
    exfalso. apply H0. rewrite <- H. reflexivity.
    reflexivity.
Qed.

Theorem prop_ext_equiv :
  forall (P Q : Prop),
    (P = Q) <-> (P <-> Q). 
Proof.
  intros P Q; split; intro H.
  split; intros; subst; tauto.
  apply prop_ext. assumption.
Qed.

(* **** Natural numbers **** *)
Lemma le_S_disj :
  forall n m : nat,
    n <= S m -> n <= m \/ n = S m.
Proof.
  intros.
  inversion H.
  right; reflexivity.
  left; exact H1.  
Qed.

Theorem helper :
  forall P : nat -> Prop,
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
    forall n, (forall m, ((m <= n) -> P m)).
Proof.
  induction n as [ | n' IHn' ]. 
  - intros m H1.
    inversion H1.
    exact H.
  - intros m H1.
    assert (H_le_S := le_S_disj m n'); apply H_le_S in H1; clear H_le_S.
    destruct H1. 
      * spec IHn' m. apply IHn'; exact H1. 
      * spec H0 n'. rewrite H1; apply H0; exact IHn'. 
Qed.

Lemma strong_induction' : 
  forall P : nat -> Prop,  
    P 0 ->
      (forall n : nat, 
      (forall m, 
      (m <= n -> P m)) -> P (S n)) ->
          (forall n : nat, P n).
Proof. 
  intros.
  induction n.
  - exact H.
  - apply (H0 n). apply helper.
    * exact H.
    * exact H0.
Qed.

Lemma strong_induction : 
  forall P : nat -> Prop,  
    P 0 ->
      (forall n : nat, 
      (forall m, 
      (m < n -> P m)) -> P n) ->
          (forall n : nat, P n).
Proof. 
  intros.
  induction n using strong_induction'.
  - exact H.
  - spec H0 (S n). apply H0.
    intros.
    apply lt_n_Sm_le in H2.
    spec H1 m H2. assumption. 
Qed.

Fixpoint iota m n :=
  match n with
  | S n' => m :: iota (S m) n'
  | 0 => []
  end.

Lemma unfold_iota_S m n :
  iota m (S n) = m :: iota (S m) n.
Proof.
  unfold iota; reflexivity. 
Qed.

Lemma length_iota m n : length (iota m n) = n.
Proof. by elim: n m => //= n IHn m; rewrite IHn. Qed.   

Lemma iota_add m n1 n2 : iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof.
by elim: n1 m => //= [|n1 IHn1] m; rewrite ?Nat.add_0_r // -Nat.add_succ_comm -IHn1.
Qed.

Lemma iota_addl m1 m2 n : iota (m1 + m2) n = map (add m1) (iota m2 n).
Proof. by elim: n m2 => //= n IHn m2; rewrite -Nat.add_succ_r IHn. Qed.

Lemma subnKC m n : m <= n -> m + (n - m) = n.
Proof.
  intro H.
  apply eq_sym.
  apply le_plus_minus.
  assumption.
Qed.

Lemma ltnn n : ltb n n = false.
Proof. apply Nat.ltb_irrefl. Qed.

Lemma min_plus : forall (n m : nat),
    Nat.min n (n+m) = n.
Proof.
  intros n m.
  induction n.
  - rewrite Nat.min_0_l. reflexivity.
  - rewrite plus_Sn_m.
    rewrite <- Nat.succ_min_distr.
    rewrite IHn.
    reflexivity.
Qed.

Lemma pred_le_succ : forall (n : nat),
    Nat.pred n < S n.
Proof.
  destruct n.
  - exact Nat.lt_0_1.
  - rewrite Nat.pred_succ.
    omega (* Used to prove n < S (S n) *).
Qed.

Lemma le_pred : forall (n m : nat),
    n <> 0 /\ m <> 0 -> n < m -> Nat.pred n < Nat.pred m.
Proof.
  intros n m H_not_zero H_lt.
  induction H_lt. 
  - rewrite Nat.pred_succ.
    apply lt_pred_n_n.
    destruct H_not_zero as [H_absurd _].
    apply neq_0_lt. apply not_eq_sym. exact H_absurd.
  - inversion H_lt.
    destruct H_not_zero as [useful _].
    assert (m <> 0). rewrite <- H. omega (* Used to prove S n <> 0 *).
    rewrite Nat.pred_succ.
    apply pred_le_succ.
    rewrite Nat.pred_succ.
    omega.
Qed.

Lemma le_minus_n : forall (n m x : nat),
    x < n /\ x < m -> n < m -> n - x < m - x.
Proof.
  intros n m x H_safe H.
  induction x.
  - do 2 rewrite Nat.sub_0_r. exact H.
  - do 2 rewrite Nat.sub_succ_r.
    apply le_pred.
    split; omega.
    apply IHx.  split; omega.
Qed.

Lemma lt_minus_n : forall n m x : nat, n < m -> n >= x -> n - x < m - x.
Proof.
  intros n m x H_lt H_gt.
  assert (n > x \/ n = x) by omega.
  destruct H as [left | right]. 
  - assert (H_useful := le_minus_n n m x).
    apply H_useful. split; omega.
    exact H_lt.
  - rewrite right. omega. 
Qed.

Lemma leq_addl : forall m n,  n <= m + n.
Proof. intros m n. omega. Qed. 

Lemma subn_eq0 : forall m n, m - n = 0 -> m <= n.
Proof. intros m n H. omega. Qed.

Lemma leq_subLR : forall m n p, (m - n <= p) -> (m <= n + p).
Proof. intros m n p H1. omega. Qed.

Lemma leq_subr : forall m n,  n - m <= n.
Proof. intros m n. omega. Qed.

Lemma inane_helper : forall m n, m <> 0 /\ m <= n -> n - m < n. 
Proof.
  induction m.
  intros. destruct H; contradiction.
  intros n H.
  destruct H.
  rewrite Nat.sub_succ_r.
  destruct n.
  inversion H0.
  spec IHm n.
  apply Peano.le_S_n in H0.
  destruct m.
  inversion H0. omega.
  omega. omega.
Qed.

Lemma ge_le_eq : forall m n : nat,
    m <= n -> m >= n -> m = n.
Proof.
  intros m n H1 H2; omega.
Qed.


(* **** Polymorphic lists **** *) 
Lemma nth_cat s1 s2 n (d : nat) :
  nth n (s1 ++ s2) d = if ltb n (length s1) then nth n s1 d else nth (n - length s1) s2 d.
Proof. by elim: s1 n => [|x s1 IHs] []. Qed.
(* Magically, specifying the type of d does wonders! *)

(* Unfold lemmas *) 
Lemma unfold_last_single {S} : forall (random a : S),
  last [a] random = a. 
Proof. 
  intros random a. 
  unfold last. reflexivity.
Qed.

Lemma unfold_last_hd {S} : forall (random a b : S) (l : list S),
  last (a :: (b :: l)) random = last (b :: l) random.
Proof.
  intros random h1 h2 tl. 
  unfold last. reflexivity.
Qed.

Lemma unfold_length_S {A} : forall (a : A) (l : list A), 
  length (a :: l) = S (length l).
Proof.
  intros hd tl.
  unfold length. reflexivity.
Qed.

Lemma skipn_zero {A} : forall (l : list A), 
    skipn 0 l = l.
Proof.
  intro l. unfold skipn. reflexivity.
Qed.

Lemma skipn_nil {A} : forall (n : nat),
    skipn n ([] : list A) = [].
Proof.
  induction n; simpl; reflexivity.
Qed.

Lemma unfold_skipn_Sn_tl {A}: forall (n : nat) (hd : A) (tl : list A),
    skipn (S n) (hd :: tl) = skipn n tl. 
Proof. 
  intros n hd tl.
  unfold skipn.
  reflexivity.
Qed.

(* Taking care to make the nth unfold lemmas polymorphic *)
Lemma nth_zero {A} : forall (a d: A) (l : list A),
    nth 0 (a :: l) d = a. 
Proof. unfold nth; reflexivity. Qed. 

Lemma nth_nil {A} : forall (n : nat) (d : A), 
    nth n [] d = d.
Proof. unfold nth. destruct n; reflexivity. Qed. 

Lemma unfold_nth_Sn_tl {A} : forall (n : nat) (a d : A) (tl : list A),
    nth (S n) (a :: tl) d = nth n tl d. 
Proof. unfold nth; reflexivity. Qed. 

(* Lemmas about last and nth and length *) 
Lemma about_last_nth {S} : forall (random : S) (l : list S), 
  last l random = nth (length l - 1) l random.
Proof.
  intro random.
  induction l.
  - simpl. reflexivity.
  - destruct l. 
    + rewrite unfold_last_single.
      simpl. reflexivity.
    + rewrite unfold_last_hd.
      rewrite IHl.
      replace (a::s::l) with ([a]++(s::l)).
      2: reflexivity.
      rewrite app_nth2.
      replace (length ([a]++s::l) - 1 - length [a]) with
              (length (s::l) - 1).
      simpl. omega. 
      simpl. reflexivity.
      simpl. reflexivity. 
Qed. 

(* Lemmas about firstn *)
Lemma about_firstn_app {S} : forall (n : nat) (l1 l2 : list S),
    n <= length l1 -> firstn n l1 = firstn n (l1++l2).
Proof. 
  intros n l1 l2 H_length.
  rewrite firstn_app.
  assert (firstn (n - length l1) l2 = []).
  assert (n - length l1 = 0).
  inversion H_length; omega.
  rewrite H. reflexivity.
  rewrite H. rewrite app_nil_r.
  reflexivity.
Qed.

Lemma about_firstn_length {A} : forall (l : list A), 
    firstn (length l) l = l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

(* Lemmas about skipn *)
(* Behead lemmas *)
Definition behead {A} (l : list A) := 
  match l with
  | [] => []
  | h::t => t
  end. 

Lemma skipn_one_behead {A} : forall (l : list A),
    skipn 1 l = behead l.
Proof.
  destruct l.
  - rewrite skipn_nil; reflexivity.
  - rewrite unfold_skipn_Sn_tl. unfold behead.
    rewrite skipn_zero. reflexivity. 
Qed.

Lemma skipn_succ_behead {A} : forall (n : nat) (l : list A),
    skipn (S n) l = behead (skipn n l).
Proof.
  induction n, l; try reflexivity. 
  do 2 rewrite unfold_skipn_Sn_tl.
  rewrite (IHn l).
  reflexivity. 
Qed.

Lemma skipn_hd_behead {A} : forall (n : nat) (a : A) (l : list A),
    skipn n l = behead (skipn n (a :: l)).
Proof.
  induction l, n; try reflexivity.
  - rewrite skipn_nil. rewrite unfold_skipn_Sn_tl.
    rewrite skipn_nil. reflexivity.
  - rewrite skipn_succ_behead.
    rewrite unfold_skipn_Sn_tl. reflexivity. 
Qed.

(* Length lemmas *) 
Lemma skipn_exceed {A} : forall (n : nat) (l : list A),
    length l <= n -> skipn n l = []. 
Proof.
  induction n, l.
  - intro H. rewrite skipn_nil; reflexivity.
  - intro H. inversion H.
  - intro H. rewrite skipn_nil; reflexivity.
  - intro H. rewrite unfold_length_S in H.
    apply le_S_n in H.
    spec IHn l.
    rewrite unfold_skipn_Sn_tl.
    apply IHn in H; exact H.
Qed.

Lemma about_skipn_length {A} : forall (n : nat) (l : list A), 
    length l <= n -> length (skipn n l) = 0.
Proof.
  intros n l H_length.
  induction H_length as [| n H_lt].
  induction l as [|a l IHl].
  - unfold length; rewrite skipn_zero; reflexivity. 
  - rewrite unfold_length_S; rewrite unfold_skipn_Sn_tl.
    exact IHl.
  - assert (length l <= S n) by omega.
    apply skipn_exceed in H.
    rewrite H. reflexivity. 
Qed.

(*
Lemma behead_behead {T} : forall (w : list T) (hd : T),
    w <> [] -> w = behead w hd :: behead w.
Proof.
  intros w hd Hneq.
  destruct w. contradiction.
  unfold behead, lib.behead.
  reflexivity. 
Qed.

Lemma about_skipn_succ {T} : forall (i : nat) (w : word) (t : T),
    (skipn i (t :: w)) <> [] -> exists t0 : T, skipn i (t :: w) = t0 :: skipn i w.
Proof.
  intros i w t Hneq.
  exists (behead (skipn i (t :: w)) t). 
  assert (H_useful := skipn_hd_behead i t w).
  rewrite H_useful.
  apply (behead_behead (skipn i (t :: w)) t); assumption.  
Qed.
*)

Lemma skipn_length {A} : forall (l : list A),
    skipn (length l) l = []. 
Proof.
  intros l.
  rewrite skipn_exceed; reflexivity.
Qed.

Lemma about_length_skipn {A} : forall (n : nat) (l : list A),
    length (skipn n l) = length l - n.
Proof.
  induction n, l.
  - rewrite skipn_nil; reflexivity.
  - rewrite skipn_zero; reflexivity.
  - rewrite skipn_nil.
    rewrite length_zero_iff_nil; reflexivity.
  - rewrite unfold_skipn_Sn_tl.
    rewrite (IHn l).
    rewrite unfold_length_S.
    reflexivity. 
Qed.

(* Append offset lemmas *)
Lemma skipn_app_first {A} : forall (n : nat) (l1 l2 : list A),
    length l1 = n -> skipn n (l1 ++ l2) = l2. 
Proof.
  intros n l1 l2 H_length. 
  induction H_length.
  induction l1.
  - unfold length; rewrite skipn_zero; reflexivity.
  - rewrite <- app_comm_cons.
    rewrite unfold_length_S.
    rewrite unfold_skipn_Sn_tl.
    rewrite IHl1; reflexivity.
Qed.

Lemma about_skipn_app {A} : forall (l1 l2 : list A) (n : nat),
    (n < length l1 /\ skipn n (l1 ++ l2) = skipn n l1 ++ l2)
    \/ (length l1 <= n /\ skipn n (l1 ++ l2) = skipn (n - length l1) l2).
Proof.
  induction l1, n.
  - right; split.
    unfold length; reflexivity.
    rewrite skipn_zero.
    reflexivity.
  - right; split.
    unfold length. omega (* Used to prove 0 <= S n *).
    unfold length; reflexivity. 
  - left; split.
    rewrite unfold_length_S; omega.
    do 2 rewrite skipn_zero.
    reflexivity.
  - spec IHl1 l2 n.
    destruct IHl1 as [[H_left1 H_left2] | [H_right1 H_right2]].
    left; split.
    rewrite unfold_length_S; omega.
    rewrite <- app_comm_cons.
    do 2 rewrite unfold_skipn_Sn_tl.
    exact H_left2.
    right; split. 
    rewrite unfold_length_S; omega.
    rewrite <- app_comm_cons.
    rewrite unfold_length_S; rewrite Nat.sub_succ. 
    rewrite unfold_skipn_Sn_tl; exact H_right2. 
Qed.

(* Breaking this down into more usable pieces *)
Lemma skipn_app_in {A} : forall (l1 l2 : list A) (n : nat),
    n < length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros l1 l2 n H_length.
  assert (H_useful := about_skipn_app l1 l2 n).
  destruct H_useful as [H_truth | H_lies].
  destruct H_truth as [H_truth  H_good]; exact H_good.
  destruct H_lies as [H_lies _]; omega.
Qed.

Lemma skipn_app_out {A} : forall (l1 l2 : list A) (n : nat),
    length l1 <= n -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof.
  intros l1 l2 n H_length.
  assert (H_useful := about_skipn_app l1 l2 n).
  destruct H_useful as [H_lies | H_truth].
  destruct H_lies as [H_lies _]; omega.
  destruct H_truth as [H_truth  H_good]; exact H_good.
Qed.

(* This has been proven above but illustrates an interesting technique
on using disjunctive cases to ease induction with unwieldy hypotheses *)
Lemma about_length_skipn_yet_again {A} : forall (n : nat) (l : list A),
    length (skipn n l) = length l - n.
Proof.
  intros n l.
  assert (n < (length l) /\ Nat.min n (length l) = n \/
          length l <= n /\ Nat.min n (length l) = (length l)).
  apply Nat.min_spec. 
  destruct H as [H_left | H_right].
  - (* In the non-exceeding case *)
    destruct H_left as [H_lt H_min].
    assert (length l = length (firstn n l) + length (skipn n l)).
    assert (l = firstn n l ++ skipn n l).
    rewrite firstn_skipn; reflexivity.
    rewrite {1} H.
    rewrite <- app_length. reflexivity.
    rewrite H.
    rewrite firstn_length.
    rewrite H_min.
    omega (* Used to prove a = b + a - b *).
  - destruct H_right as [H_le H_min].
    rewrite about_skipn_length.
    exact H_le. omega.
Qed.

(* Learning lessons from the skipn length proof - disjunction is key *) 
Lemma about_length_nth {S} : forall (l1 l2 : list S) (n : nat) (default : S),
    (n < length l1 /\ nth n (l1 ++ l2) default = nth n l1 default) \/
    length l1 <= n /\ nth n (l1 ++ l2) default = nth (n - length l1) l2 default.
Proof.
  induction l1, n; intros d. 
  - right; split.
    unfold length; omega.
    reflexivity.
  - right; split.
    unfold length; omega.
    unfold length; reflexivity.
  - left; split.
    unfold length; omega.
    rewrite <- app_comm_cons.
    do 2 rewrite nth_zero; reflexivity.
  - spec IHl1 l2 n.
    destruct (IHl1 d) as [[H_left1 H_left2] | [H_right1 H_right2]].
    left; split.
    rewrite unfold_length_S; omega.
    rewrite <- app_comm_cons.
    do 2 rewrite unfold_nth_Sn_tl.
    exact H_left2.
    right; split.
    rewrite unfold_length_S; omega.
    rewrite <- app_comm_cons. 
    rewrite unfold_nth_Sn_tl.
    rewrite unfold_length_S; rewrite Nat.sub_succ.
    exact H_right2.
Qed.

Lemma length_nth_in {S} : forall (l1 l2 : list S) (n : nat) (default : S),
    n < length l1 -> nth n (l1 ++ l2) default = nth n l1 default.
Proof.
  intros l1 l2 n d H_length.
  assert (H_useful := about_length_nth l1 l2 n).
  destruct (H_useful d) as [H_truth | H_lies].
  destruct H_truth as [H_truth H_good]; exact H_good. 
  destruct H_lies as [H_lies _]; omega.
Qed.

Lemma length_nth_out {S} : forall (l1 l2 : list S) (n : nat) (default : S),
    length l1 <= n -> nth n (l1 ++ l2) default = nth (n - length l1) l2 default.
Proof.
  intros l1 l2 n d H_length.
  assert (H_useful := about_length_nth l1 l2 n).
  destruct (H_useful d) as [H_lies | H_truth].
  destruct H_lies as [H_lies _]; omega.
  destruct H_truth as [H_truth  H_good]; exact H_good.
Qed.            

Lemma nth_app_offset {A} : forall (l1 l2 : list A) (n : nat) (default : A),
    nth n l2 default = nth (n + length l1) (l1 ++ l2) default.
Proof.
  induction l1, n; intros. 
  - reflexivity.
  - unfold length.
    rewrite app_nil_l; rewrite Nat.add_0_r; reflexivity. 
  - rewrite Nat.add_0_l.
    rewrite unfold_length_S; rewrite <- app_comm_cons.
    rewrite unfold_nth_Sn_tl.
    rewrite <- (Nat.add_0_l (length l1)). 
    rewrite <- (IHl1 l2 0). reflexivity.
  - rewrite plus_Sn_m; rewrite <- app_comm_cons.
    rewrite unfold_nth_Sn_tl.
    rewrite (IHl1 l2 (S n)).
    rewrite unfold_length_S.
    rewrite Nat.add_succ_r.
    rewrite plus_Sn_m.
    reflexivity. 
Qed. 

Lemma about_split_length {A} : forall (hd1 tl1 hd2 tl2 : list A),
    hd1 ++ tl1 = hd2 ++ tl2 -> length hd1 = length hd2 ->
    hd1 = hd2 /\ tl1 = tl2.
Proof.
  intros hd1 tl1 hd2 tl2 H_app H_length.
  assert (hd1 = firstn (length hd1) (hd1 ++ tl1)).
  rewrite (firstn_app (length hd1) hd1 tl1);
  rewrite about_firstn_length;
  rewrite Nat.sub_diag;
  rewrite firstn_O;
  rewrite app_nil_r; reflexivity. 
  assert (hd2 = firstn (length hd2) (hd2 ++ tl2)).
  rewrite (firstn_app (length hd2) hd2 tl2);
  rewrite about_firstn_length;
  rewrite Nat.sub_diag;
  rewrite firstn_O;
  rewrite app_nil_r;
  reflexivity.
  rewrite <- H_app in H0. rewrite <- H_length in H0.
  rewrite <- H0 in H.
  split. 
  exact H.
  rewrite H in H_app.
  apply app_inv_head in H_app.
  exact H_app.
Qed.

Lemma about_pivot_length {A} : forall (part1 part2 l1 l2 : list A) (p : A),
    part1 ++ p::part2 = l1 ++ p::l2 -> length part1 = length l1 ->
    part1 = l1 /\ part2 = l2.
Proof.
  intros part1 part2 l1 l2 p H_eq H_length.
  assert (H_useful := (about_split_length part1 (p::part2) l1 (p::l2))).
  apply H_useful in H_eq; clear H_useful.
  destruct H_eq as [H_now H_later]; split. exact H_now.
  apply (f_equal behead) in H_later.
  unfold behead in H_later.
  exact H_later.
  exact H_length.
Qed.

Lemma front_app_inj {A} : forall (head tl1 tl2 : list A),
    tl1 = tl2 -> head ++ tl1 = head ++ tl2.
Proof.
  intros h t1 t2 Heq; rewrite Heq; reflexivity. 
Qed.

(* Using the meta-induction pattern again *) 
Lemma last_indep {X} : forall l : list X,
    (l = [] /\ forall d : X, last l d = d) \/
    (l <> [] /\ forall d1 d2 : X, last l d1 = last l d2). 
Proof. 
  intros l. 
  induction l as [|hd tl IHl].
  - left; split. reflexivity.
    unfold last. intros; reflexivity.
  - destruct IHl as [[? ?] | [? ?]].    
    right; split.
    rewrite H. unfold not; intro H_absurd; inversion H_absurd.
    intros d1 d2.
    destruct tl.
    + reflexivity.
    + inversion H.   
    + right. split.
      unfold not; intro H_absurd; inversion H_absurd.
      intros d1 d2.
      destruct tl.
      do 2 rewrite unfold_last_single; reflexivity.
      do 2 rewrite unfold_last_hd.
      exact (H0 d1 d2).
Qed.

Lemma about_deriv_eq {X} :
  forall bp1 bp2 (x w : list X),
    bp1 >= length x -> bp2 >= length x -> 
    x ++ firstn (bp1 - length x) w ++ skipn (bp2 - length x) w = 
    firstn bp1 (x ++ w) ++ skipn bp2 (x ++ w).
Proof.
  intros bp1 bp2 x w H_lt1 H_lt2. 
  assert (Heq : bp1 = (length x + (bp1 - length x))) by omega.
  rewrite {2} Heq. 
  rewrite firstn_app_2.
  apply (skipn_app_out x w) in H_lt2.
  rewrite Heq; rewrite app_assoc_reverse; rewrite H_lt2.
  reflexivity.
Qed.

(* **** Natural number lists **** *) 

Definition increasing (l : list nat) (default : nat) := 
  forall n m : nat, 
  n < m < (length l) -> 
  nth n l default < nth m l default.

Lemma nth_iota p m n i : i < n -> nth i (iota m n) p = m + i.
Proof.
    by move/subnKC <-;
           rewrite Nat.add_succ_comm iota_add nth_cat length_iota ltnn Nat.sub_diag.
Qed.

Lemma iota_increasing : forall n m d : nat,
    increasing (iota n m) d.
Proof.
  intros n m d; unfold increasing; intros i j H_lt.
  rewrite length_iota in H_lt.
  rewrite nth_iota. omega. 
  rewrite nth_iota;
  omega.
Qed.

Lemma sublist_preserves_increasing : forall (l l1 l2 : list nat) (d : nat),
    l = l1 ++ l2 -> increasing l d -> increasing l1 d /\ increasing l2 d. 
Proof.
  intros l part1 part2 d H_app H_incr.
  unfold increasing in *; split.
  - intros i j H_lt.
    assert (i < length part1) by omega.
    apply (app_nth1 part1 part2 d) in H.
    rewrite <- H.
    assert (j < length part1) by omega.
    apply (app_nth1 part1 part2 d) in H0.
    rewrite <- H0.
    rewrite <- H_app.
    apply (H_incr i j).
    rewrite H_app; rewrite app_length; omega.
  - intros i j H_lt.
    rewrite (nth_app_offset part1 part2 i).
    rewrite (nth_app_offset part1 part2 j).
    rewrite H_app in H_incr.
    spec H_incr (i + length part1) (j + length part1).
    apply H_incr.
    rewrite app_length. omega. 
Qed.


Definition reverse_arg_minus (n m : nat) :=
  minus m n.

Definition minus_map (n : nat) (l : list nat) :=
  map (reverse_arg_minus n) l.


Lemma about_minus_nth : forall (n a : nat) (l : list nat) (default : nat),
    nth n (minus_map a l) (reverse_arg_minus a default) = (nth n l default) - a. 
Proof. 
  intros n a l default.
  unfold minus_map.
  assert (H_useful := map_nth (reverse_arg_minus a) l default n).
  unfold reverse_arg_minus in H_useful at 3. 
  rewrite <- H_useful.
  reflexivity.
Qed.

Lemma about_plus_increasing : forall (offset : nat) (l : list nat) (d : nat),
    increasing l d -> increasing (map (plus offset) l) d.
Proof.
  intros c l d H_incr;
    unfold increasing in *.
  intros n m H_lt.
  rewrite map_length in H_lt.
  spec H_incr n m H_lt.
  assert (H_useful := @nth_indep nat (map (add c) l) n (add c d) d).
  assert (H_useful' := @nth_indep nat (map (add c) l) m (add c d) d). 
  rewrite map_length in H_useful, H_useful'.
  assert (H_obv : n < length l) by omega.
  assert (H_obv' : m < length l) by omega.
  spec H_useful H_obv; spec H_useful' H_obv'.
  rewrite <- H_useful; rewrite <- H_useful'.
  do 2 rewrite map_nth. omega.
Qed. 

Lemma about_minus_increasing : forall (offset : nat) (l : list nat) (default : nat),
    increasing l default -> offset < nth 0 l default -> increasing (minus_map offset l) default.
Proof.
  intros a part2 default H_incr H_lt.
  unfold increasing. intros n m.
  intros H_lt_nm.
  rewrite <- (nth_indep _ (reverse_arg_minus a default)).
  2 : omega.
  replace (nth m (minus_map a part2) default) with
      (nth m (minus_map a part2) (reverse_arg_minus a default)).
  2 : apply nth_indep; omega.
  do 2 rewrite about_minus_nth.
  destruct n.
  - (* When n = 0 *)
    + destruct part2 as [| hd tl].
      * (* When part2 = [] *)
        unfold minus_map in H_lt_nm;
          rewrite map_length in H_lt_nm.
        inversion H_lt_nm. inversion H0. 
      * (* When part2 = hd :: tl *)
        rewrite nth_zero.
        assert (hd = nth 0 (hd::tl) default).
        rewrite nth_zero; reflexivity.
        apply (le_minus_n hd (nth m (hd::tl) default) a).
        split.
        rewrite <- H in H_lt; exact H_lt.
        Check Nat.lt_trans.
        apply (Nat.lt_trans a
                            (nth 0 (hd :: tl) default)
                            (nth m (hd :: tl) default)).
        exact H_lt.
        destruct m.
        ** (* When m = 0 *)
          inversion H_lt_nm. inversion H0. 
        ** (* When m = S m' *)
          unfold increasing in H_incr.
          spec H_incr 0 (S m).
          apply H_incr.
          split. omega.
          unfold minus_map in H_lt_nm;
            rewrite map_length in H_lt_nm.
          omega.
        ** rewrite {1} H.
           destruct m.
           *** inversion H_lt_nm. 
               inversion H0.
           ***  unfold increasing in H_incr.
                spec H_incr 0 (S m).
                apply H_incr.
                split. omega.
                unfold minus_map in H_lt_nm;
                  rewrite map_length in H_lt_nm.
                omega.
  - (* When n = S n *)
    apply (le_minus_n (nth (S n) part2 default)
                      (nth m part2 default)
                      a). 
    split.
    apply (Nat.lt_trans a
                        (nth 0 part2 default)
                        (nth (S n) part2 default)). 
    exact H_lt.
    unfold increasing in H_incr.
    spec H_incr 0 (S n).
    apply H_incr.
    split. omega.
    unfold minus_map in H_lt_nm;
      rewrite map_length in H_lt_nm.
    omega.
    destruct m.
    + (* When m = 0 *)
      inversion H_lt_nm.
      inversion H. 
    + apply (Nat.lt_trans a
                          (nth 0 part2 default)
                          (nth (S m) part2 default)).
      exact H_lt.
      unfold increasing in H_incr.
      spec H_incr 0 (S m).
      apply H_incr.
      split. omega.
      unfold minus_map in H_lt_nm;
        rewrite map_length in H_lt_nm.
      omega.
    + unfold increasing in H_incr.
      spec H_incr (S n) m.
      apply H_incr.
      unfold minus_map in H_lt_nm;
        rewrite map_length in H_lt_nm; exact H_lt_nm.
Qed.

Lemma about_increasing_min : forall (l : list nat) (default : nat),
    l <> [] -> increasing l default ->
    forall e : nat, In e l -> nth 0 l default <= e.
Proof.
  intros l default H_non_nil H_incr e H_in.
  apply (In_nth _ _ default) in H_in.
  destruct H_in as [index [H_length H_id]].
  rewrite <- H_id.
  destruct index.
  - reflexivity.
  - unfold increasing in H_incr.
    spec H_incr 0 (S index).
    apply Nat.lt_le_incl.
    apply H_incr.
    omega.
Qed.

Lemma iota_last : forall n : nat,
    last (iota 1 n) 0 = n. 
Proof. 
  intro n.
  destruct n.
  reflexivity.  
  rewrite about_last_nth.
  rewrite length_iota.
  rewrite nth_iota.
  omega. omega.
Qed.

Lemma about_incr_last_max : forall (d : nat) (l : list nat),
    increasing l d -> (forall n : nat, In n l -> n <= last l d).
Proof.
  intros d l H_incr n H_in.
  apply (In_nth l n d) in H_in.
  destruct H_in as [n_index [n_length n_pos]].
  rewrite <- n_pos. clear n_pos. 
  rewrite about_last_nth.
  unfold increasing in H_incr.
  assert (n_index = length l - 1 \/ n_index < length l - 1) by omega. 
  destruct H as [Heq | H_lt].
  rewrite Heq. reflexivity.
  clear n_length.
  spec H_incr n_index (length l - 1).
  apply Nat.lt_le_incl.
  apply H_incr.
  omega. 
Qed.

Lemma about_incr_nth_last : forall (d : nat) (l : list nat),
    increasing l d -> forall n : nat, n < length l -> nth n l d <= last l d. 
Proof.
  intros d l H_incr n H_length.
  rewrite about_last_nth.
  unfold increasing in H_incr.
  assert (n = length l - 1 \/ n < length l - 1) by omega.
  destruct H as [H_eq | H_lt].
  rewrite H_eq. 
  reflexivity. 
  apply Nat.lt_le_incl.
  spec H_incr n (length l - 1).
  apply H_incr. omega. 
Qed.

Lemma about_incr_index : forall (l : list nat) (d : nat),
    increasing l d -> forall (i : nat), i < length l -> nth i l d >= i.
Proof.
  intros l d H_incr i H_lt.
  induction i as [|i IHi].
  - omega.
  - assert (i < length l) by omega.
    spec IHi H.
    spec H_incr i (S i).
    assert (i < S i < length l) by omega.
    spec H_incr H0. omega.
Qed.

Lemma about_incr_length_last : forall (k d : nat) (l : list nat),
    l <> [] -> length l = k -> increasing l d -> last l d >= k - 1.
Proof.
  intros k d l H_nil H_eq H_incr.
  destruct k. 
  - apply length_zero_iff_nil in H_eq. contradiction.
  - rewrite about_last_nth.
    rewrite H_eq. apply about_incr_index. 
    exact H_incr. rewrite H_eq.
    omega.
Qed.

Lemma map_plus_minus : forall (l : list nat) (n : nat),
    map (fun x0 : nat => n + x0 - n) l = l. 
Proof.
  intros l n.
  assert (H_useful := map_ext  (fun x0 => n + x0 - n) (fun x => x)). 
  assert (H_pre : (forall a : nat, (fun x0 : nat => n + x0 - n) a = (fun x : nat => x) a)).
  intro a. omega. spec H_useful H_pre.
  clear H_pre.
  spec H_useful l. rewrite H_useful.
  now apply map_id.  
Qed.

Lemma map_minus_plus : forall (l : list nat) (offset : nat),
    (forall x : nat, In x l -> x >= offset) ->
    map (fun x => x - offset + offset) l = l. 
Proof.
  intros l c H_ge.
  induction l as [|hd tl IHl].
  - reflexivity.
  - rewrite map_cons. 
    assert (forall x : nat, In x tl -> x >= c).
    { intro x. spec H_ge x.
      intro. apply H_ge.
      now apply in_cons. }
    spec IHl H.
    rewrite IHl.
    spec H_ge hd.
    assert (In hd (hd :: tl)) by apply in_eq.
    spec H_ge H0.
    replace (hd - c + c) with hd by omega.
    reflexivity. 
Qed.
        
Lemma shifted_gt : forall (l : list nat) (n : nat),
    forall m : nat, In m (map (plus n) l) -> m >= n.
Proof.
  intros n l m H_in.
  apply in_map_iff in H_in.
  destruct H_in as [x [H_eq H_in]].
  omega. 
Qed.

(* From functional correctness proofs, bleurgh.v *)

Lemma iota_last_nonzero : forall m n d : nat,
    n <> 0 -> 
    last (iota m n) d = m + n - 1.  
Proof. 
  intros m n d.
  destruct n. 
  - intro absurd. unfold not in absurd. exfalso.
    apply absurd; reflexivity. 
  - intros.
    rewrite about_last_nth.
    rewrite length_iota.
    rewrite nth_iota.
    omega. rewrite Nat.add_sub_assoc. omega.
    omega. 
Qed.


(* A cacophany of helper lemmas *) 
Lemma incr_head :
  forall (l : list nat) (hd d : nat),
    increasing l d ->
    hd < nth 0 l d ->
    increasing (hd :: l) d.
Proof. 
  intros l hd d H_incr H_lt.
  unfold increasing. intros n m H_order.
  destruct n.
  - rewrite nth_zero.
    assert (m = 1 \/ m > 1) by omega.
    destruct H as [m_one | m_gt_one].
    subst m. simpl.
    exact H_lt. 
    assert (H_rewrite :=  nth_app_offset [hd] l (pred m) d).
    replace (pred m + length [hd]) with m in H_rewrite.
    2 : { unfold length; omega. }
    replace ([hd] ++ l) with (hd :: l) in H_rewrite by easy.
    rewrite <- H_rewrite; clear H_rewrite.
    apply (Nat.lt_trans hd (nth 0 l d) (nth (pred m) l d)).
    exact H_lt.
    spec H_incr 0 (pred m).
    apply H_incr.
    split. omega. destruct H_order.
    destruct m. omega.
    unfold pred.
    rewrite unfold_length_S in H0. omega.
  - destruct m.
    inversion H_order. 
    inversion H.
    do 2 rewrite unfold_nth_Sn_tl.
    spec H_incr n m.
    assert (n < m < length l).
    { destruct H_order. rewrite unfold_length_S in H0. split; omega. }
    spec H_incr H. exact H_incr.
Qed.

Lemma incr_unhead :
  forall (l : list nat) (hd d : nat),
    increasing (hd :: l) d ->
    increasing l d.
Proof.
  intros l hd d H_incr. 
  assert (H_useful' := sublist_preserves_increasing).
  assert (Heq : hd :: l = [hd] ++ l) by easy.
  spec H_useful' (hd :: l) [hd] l.
  spec H_useful' d Heq H_incr.
  destruct H_useful' as [_ H_useful'].
  exact H_useful'.
Qed.   

Lemma about_increasing_hd :
  forall (l : list nat) (h d : nat),
    increasing (h :: l) d ->
    h < hd (S h) l. 
Proof.
  intros l h d H_incr.
  destruct l. 
  simpl. omega.
  simpl. spec H_incr 0 1.
  simpl in H_incr. apply H_incr.
  omega. 
Qed.


Lemma about_hd_tl_incr :
  forall (hd : nat) (tl : list nat) (i d : nat),
    increasing (hd :: tl) d -> In i tl -> hd < i.
Proof.
  intros hd tl i d H_incr H_in.
  assert (H_incr_copy := H_incr). 
  destruct tl. inversion H_in.
  destruct H_in. subst i.
  spec H_incr 0 1.
  assert (H_lt : 0 < 1 < length (hd :: n :: tl)).
  { unfold length; omega. } 
  spec H_incr H_lt; clear H_lt.
  unfold nth in H_incr. exact H_incr.
  apply (In_nth _ _ d) in H.
  destruct H as [i_pos [about_pos pos_eq]].
  spec H_incr 0 (i_pos + 2).
  assert (H_obv : 0 < i_pos + 2 < length (hd :: n :: tl)).
  { do 2 rewrite unfold_length_S. omega. }
  spec H_incr H_obv; clear H_obv. rewrite nth_zero in H_incr.
  replace (nth (i_pos + 2) (hd :: n :: tl) d)
    with (nth i_pos tl d) in H_incr.
  rewrite pos_eq in H_incr. exact H_incr.
  replace (hd :: n :: tl) with ([hd;n] ++ tl) by easy.
  rewrite (nth_app_offset [hd;n] tl i_pos d).
  unfold length. reflexivity.
Qed.

Theorem not_in_app {X : Type} :
  forall (l1 l2 : list X) (x : X),
    ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros; split; intros.
  split; intro not; apply H.
  apply in_or_app.
  left; assumption. 
  apply in_or_app.
  right; assumption.
  destruct H.
  intro not.
  apply in_app_or in not.
  destruct not;
  contradiction. 
Qed.

Unset SsrRewrite. 

Lemma about_length_one :
  forall (l : list nat),
    length l = 1 ->
    exists (w : nat), l = [w].
Proof.
  intros l H_length.
  destruct l; inversion H_length.
  exists n. rewrite length_zero_iff_nil in H0.
  rewrite H0. reflexivity.
Qed.

Theorem increasing_NoDup :
  forall (l : list nat) (d : nat),
    increasing l d ->
    NoDup l.
Proof.
  intros l d H_incr.
  induction l as [|hd tl IHl].
  - constructor.
  - constructor.
    2 : { apply incr_unhead in H_incr. spec IHl H_incr.
          assumption. }
    intro absurd.
    assert (H_useful := about_hd_tl_incr hd tl hd d).
    spec H_useful H_incr absurd. omega.
Qed.

Theorem increasing_nth_injective :
  forall (l : list nat) (d : nat),
    increasing l d ->
    forall (x1 x2 : nat),
      x1 < length l ->
      x2 < length l -> 
      nth x1 l d = nth x2 l d ->
      x1 = x2.
Proof.
  intros l d H_incr x1 x2 H_x1 H_x2 H_nth.
  assert (x1 < x2 \/ x1 = x2 \/ x1 > x2) by omega.
  destruct H as [H_lt | [H_eq | H_gt]].
  - spec H_incr x1 x2.
    assert (x1 < x2 < length l) by omega. 
    spec H_incr H. omega.
  - exact H_eq.
  - spec H_incr x2 x1.
    assert (x2 < x1 < length l) by omega.
    spec H_incr H. omega.
Qed.

Theorem increasing_nth_lt :
  forall (l : list nat) (d : nat),
    increasing l d ->
    forall (x1 x2 : nat),
      x1 < length l ->
      x2 < length l -> 
      nth x1 l d < nth x2 l d ->
      x1 < x2.
Proof.
  intros l d H_incr x1 x2 H_x1 H_x2 H_nth.
  assert (x1 < x2 \/ x1 = x2 \/ x1 > x2) by omega.
  destruct H as [H_lt | [H_eq | H_gt]].
  - assumption.
  - rewrite H_eq in H_nth.
    omega.
  - spec H_incr x2 x1.
    assert (x2 < x1 < length l) by omega.
    spec H_incr H. omega.
Qed.

Section ListStuff.

Variable X : Type.

Inductive subseq : list X -> list X -> Prop :=
  | subseq_nil: forall l, subseq nil l
  | subseq_hm: forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2)
  | subseq_hn: forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2).

Lemma subseq_refl: forall (L : list X),
  subseq L L.
Proof.
  induction L; constructor; auto.
Qed.

Lemma subseq_trans: forall (L1 L2 L3 : list X),
  subseq L1 L2 ->
  subseq L2 L3 ->
  subseq L1 L3.
Proof.
  intros L1 L2 L3 H0 H1. revert L1 H0.
  induction H1. inversion 1. constructor.
  intros. inversion H0; subst. constructor.
  constructor. eauto.
  constructor 3. eauto.
  intros. constructor 3. eauto.
Qed.

Lemma subseq_length: forall L1 L2,
  subseq L1 L2 ->
  length L1 <= length L2.
Proof.
  induction 1; simpl; omega.
Qed.

Lemma subseq_antisym: forall L1 L2,
  subseq L1 L2 ->
  subseq L2 L1 ->
  L1 = L2.
Proof.
  induction L1; intros.
  inversion H0. trivial.
  inversion H0; subst. inversion H.
  inversion H; subst. f_equal. eauto.
  apply subseq_length in H.
  apply subseq_length in H4.
  apply subseq_length in H0.
  simpl in *. exfalso. omega.
  apply subseq_length in H.
  apply subseq_length in H3.
  apply subseq_length in H0.
  simpl in *. exfalso. omega.
Qed.

Lemma subseq_contra: forall (L1 L2 : list X),
  subseq L1 L2 ->
  length L1 > length L2 ->
  False.
Proof.
  intros. apply subseq_length in H. omega.
Qed.

Lemma subseq_whole: forall (L1 L2 : list X),
  subseq L1 L2 ->
  length L1 = length L2 ->
  L1 = L2.
Proof.
  induction 1; simpl.
  + destruct l; auto. inversion 1.
  + inversion 1. rewrite IHsubseq; auto.
  + intro. exfalso. eapply subseq_contra; eauto.
    omega.
Qed.

Lemma subseq_incl: forall (L1 L2 : list X),
  subseq L1 L2 ->
  incl L1 L2.
Proof.
  intros. induction H.
  inversion 1.
  intros x0 ?. destruct H0. subst; left; auto.
  right. apply IHsubseq; auto.
  intros x0 ?. right. apply IHsubseq; auto.
Qed.

Lemma subseq_NoDup: forall (L1 L2 : list X),
  NoDup L2 ->
  subseq L1 L2 ->
  NoDup L1.
Proof.
  intros. induction H0.
  + constructor.
  + inversion H; subst.
    constructor; auto.
    intro. apply H3. apply subseq_incl in H0.
    apply H0. trivial.
  + apply IHsubseq. inversion H; auto.
Qed.

Lemma subseq_app: forall (l1 l2 L1 L2 : list X),
  subseq l1 L1 ->
  subseq l2 L2 ->
  subseq (l1 ++ l2) (L1 ++ L2).
Proof.
  intros l1 l2 L1 L2 H. induction H; simpl; intros.
  * induction l. auto. constructor 3. apply IHl.
  * constructor. auto.
  * constructor 3. auto.
Qed.

Lemma NoDup_app: forall (L1 L2 : list X),
  NoDup (L1 ++ L2) -> NoDup L1 /\ NoDup L2.
Proof.
  induction L1; simpl; intros.
  split. constructor. auto.
  inversion H; subst.
  apply IHL1 in H3. destruct H3.
  split; auto. constructor; auto.
  intro. apply H2.
  rewrite in_app_iff. auto.
Qed.

Variable Heq : forall x y : X, x = y \/ x <> y.

Lemma incl_strip: forall (x : X) (l L : list X),
  incl l (x :: L) ->
  exists l',
    incl l (x :: l') /\ 
    incl l' l /\ 
    ~In x l'.
Proof.
  induction l; intros.
  exists nil. split. inversion 1. split; inversion 1.
  assert (incl l (x :: L)). { do 2 intro. apply H. right. trivial. }
  destruct (IHl _ H0) as [l' [? [? ?]]].
  destruct (Heq x a).
  subst. exists l'. split. do 2 intro. destruct H4. left; trivial. apply H1. trivial.
  split; trivial. do 2 intro. right. apply H2, H4.
  exists (a :: l'). split. do 2 intro. destruct H5.  right. left. trivial. apply H1 in H5. destruct H5. left. trivial. right. right. trivial.
  split. do 2 intro. destruct H5. left; trivial. right. apply H2. trivial.
  intro. destruct H5. subst; contradiction. contradiction.
Qed.

Lemma In_or_not_In: forall (x : X) (L : list X),
  In x L \/ ~ In x L.
Proof.
  induction L.
  * right. inversion 1.
  * destruct (Heq a x).
    left. left. trivial.
    destruct IHL. left. right. trivial.
    right. intro. destruct H1; contradiction.
Qed.

Lemma incl_subseq: forall (l L : list X),
  incl l L ->
  exists l', 
    subseq l' L /\
    incl l l' /\
    incl l' l.
Proof. 
  intros l L.
  remember (length L) as k. assert (length L <= k) by omega. clear Heqk.
  revert L H l. induction k; intros.
  + exists nil. destruct L.
    split. constructor. split; auto; inversion 1.
    inversion H.
  + destruct L.
    exists nil. split. constructor. split; auto. inversion 1.
    simpl in H.
    assert (length L <= k) by omega. clear H.
    specialize (IHk _ H1).
    destruct (In_or_not_In x l).
    * destruct (incl_strip _ _ _ H0) as [l' [? [? ?]]].
      assert (incl l' L). { do 2 intro. generalize (H3 _ H5); intro. apply H0 in H6. destruct H6. subst. contradiction. trivial. }
      destruct (IHk _ H5) as [l'' [? [? ?]]].
      exists (x :: l''). split. constructor. trivial.
      split. do 2 intro. apply H2 in H9. destruct H9. left; trivial. right. apply H7, H9.
      do 2 intro. destruct H9. subst. trivial. apply H3, H8, H9.
    * assert (incl l L). { do 2 intro. generalize (H0 _ H2); intro. destruct H3. subst. contradiction. trivial. }
      destruct (IHk _ H2) as [l' [? [? ?]]].
      exists l'. split. constructor. trivial.
      split; trivial.
Qed.

End ListStuff.

Arguments subseq {X}.

Fixpoint choose {X : Type} (L : list X) (k : nat) {struct L} : list (list X) :=
  match k with
  | 0 => nil :: nil
  | S k' => 
    match L with
    | nil => nil
    | h :: L' => 
      (map (fun l => h :: l) (choose L' k')) ++
      (choose L' k)
    end
  end.

Lemma choose_none: forall X (L : list X),
  forall k, k  > length L ->
  choose L k = nil.
Proof.
  induction L; simpl; intros. destruct k; trivial. inversion H.
  destruct k. inversion H.
  rewrite IHL. 2 : omega. simpl.
  apply IHL. omega. 
Qed.

Lemma choose_all: forall X (L : list X), 
  choose L (length L) = L :: nil.
Proof.
  induction L; simpl; intros. reflexivity.
  rewrite IHL. simpl. rewrite choose_none. trivial.
  omega. 
Qed.

Lemma choose_spec: forall X
  (L : list X),
  forall k, length L >= k ->
    (forall l, 
      In l (choose L k) <-> 
      (length l = k /\ subseq l L)).
Proof.
  induction L; simpl; intros; destruct k; simpl.
  * destruct l; simpl; intuition;
    try constructor; discriminate.
  * exfalso. omega.
  * destruct l; simpl; intuition;
    try constructor; discriminate.
  * rewrite in_app_iff; rewrite in_map_iff.
    assert (length L >= S k \/ length L = k) by omega.
    clear H. destruct H0.
    + split; intros.
      - destruct H0 as [[x [? ?]] | ?].
        ** subst l. simpl.
           rewrite IHL in H1.
           destruct H1 as [? ?].
           split. f_equal. trivial.
           constructor. trivial.
           omega.
        ** rewrite IHL in H0.
           destruct H0. split; trivial.
           constructor. trivial.
           omega.
      - destruct H0.
        inversion H1; subst.
        ** discriminate.
        ** left. exists l1. split; trivial.
           rewrite IHL. split; trivial.
           simpl in H0. inversion H0. trivial.
           omega.
        ** right.
           rewrite IHL. split; trivial.
           omega.
    + subst k. clear IHL.
      rewrite (choose_none _ _ (S _)). 2: omega.
      rewrite choose_all.
      simpl.
      split; intros.
      - destruct H as [[x [? [? | []]]] | []].
        subst. simpl. split; auto.
        apply subseq_refl.
      - left. destruct H.
        apply subseq_whole in H0. 2: auto.
        subst. exists L. auto.
Qed.

Lemma choose_incl1: forall X
  (L : list X), NoDup L ->
  forall k, length L >= k ->
    forall l, 
      In l (choose L k) -> 
        length l = k /\ incl l L /\ NoDup l.
Proof.
  intros. apply choose_spec in H1; trivial.
  destruct H1. split; trivial.
  split. apply subseq_incl. trivial.
  apply subseq_NoDup in H2; auto.
Qed.

Lemma choose_incl2: forall X (Heq: forall x y : X, x = y \/ x <> y)
  (L : list X), NoDup L ->
  forall k, length L >= k ->
    forall l, 
      length l = k /\ incl l L /\ NoDup l ->
      exists l', incl l l' /\ incl l' l /\
        In l' (choose L k).
Proof.
  intros.
  destruct H1 as [? [? ?]].
  destruct (incl_subseq _ Heq _ _ H2) as [l' [? [? ?]]].
  exists l'.
  split; trivial. split; trivial.
  rewrite choose_spec; trivial.
  split; trivial.
  assert (NoDup l'). { eapply subseq_NoDup. apply H. trivial. }
  generalize (NoDup_incl_length H3 H5).
  generalize (NoDup_incl_length H7 H6).
  omega.
Qed.

Require Import Classical.

Lemma choose_incl2': forall X
  (L : list X), NoDup L ->
  forall k, length L >= k ->
    forall l, 
      length l = k /\ incl l L /\ NoDup l ->
      exists l', incl l l' /\ incl l' l /\
        In l' (choose L k).
Proof.
  intros. eapply choose_incl2; eauto.
  intros. apply classic.
Qed.

Theorem subseq_nil_inversion {X : Type} :
  forall (h : X) (l : list X),
    subseq (h :: l) [] -> False. 
Proof.
  intros. induction l.
  inversion H. 
  inversion H.
Qed.

Theorem subseq_nil_nil {X : Type} :
  forall (l : list X),
    subseq l [] -> l = []. 
Proof.
  intros.
  induction l.
  reflexivity. 
  apply subseq_nil_inversion in H. inversion H.
Qed.

Lemma annoying :
  forall (l1 l2 : list nat) (h x d : nat),
    increasing (h :: l2) d ->
    subseq l1 (h :: l2) ->
    x < hd (S x) (h :: l2) ->
    x < hd (S x) l1.
Proof.
  intros l1 l2 h x d H_incr H_subseq H_lt.
  induction H_subseq.
  unfold hd. omega.
  unfold hd. unfold hd in H_lt. exact H_lt.
  apply IHH_subseq.
  apply (incr_unhead l0 x0) in H_incr.
  spec IHH_subseq H_incr. exact H_incr.
  simpl in H_lt.
  spec H_incr 0 1.
  destruct l0. unfold hd. omega.
  simpl.
  assert (0 < 1 < length (x0 :: n :: l0)).
  split. omega. do 2 rewrite unfold_length_S. omega.
  spec H_incr H. clear H.
  unfold nth in H_incr.
  now apply (Nat.lt_trans x x0 n).
Qed.

Lemma subseq_incr :
  forall (l : list nat) (d : nat),
    increasing l d ->
    forall (sl : list nat),
      subseq sl l ->
      increasing sl d. 
Proof.
  intros l d H_incr sl H_subseq.
  induction H_subseq. 
  - (* This case is easy *)
    unfold increasing. intros. unfold length in H; inversion H.
    inversion H1.
  - (* This case is annoying *)
    assert (l1 = [] \/ l1 <> []).
    { destruct l1. left; reflexivity.
      right; easy. }
    destruct H as [H_nil | H_nonnil].
    subst l1. unfold increasing.
    intros. unfold length in H.
    inversion H. inversion H1.
    subst m; inversion H0. inversion H3.
    (* Finally! *) 
    apply incr_head. 
    apply IHH_subseq.
    apply (incr_unhead l2 x) in H_incr. 
    assumption.
    destruct l1. unfold not in H_nonnil.
    exfalso; apply H_nonnil; reflexivity.
    assert (H_useful := about_increasing_hd l2 x d). 
    spec H_useful H_incr.
    destruct l2. inversion H_subseq.
    apply (incr_unhead (n0::l2) x) in H_incr. 
    assert (H_useful' := annoying (n :: l1) l2 n0 x).
    spec H_useful' d H_incr .
    spec H_useful' H_subseq H_useful.
    simpl in H_useful'. simpl. exact H_useful'.
  - (* This case is also easy *)
    apply IHH_subseq.
    assert (H_useful' := sublist_preserves_increasing).
    assert (Heq : x :: l2 = [x] ++ l2) by easy.
    spec H_useful' (x :: l2) [x] l2.
    spec H_useful' d Heq H_incr.
    destruct H_useful' as [_ H_useful'].
    exact H_useful'.
Qed.     

Lemma about_subseq_last :
  forall (l1 l2 : list nat) (d : nat),
    length l1 >= 2 -> length l2 >= 2 -> 
    increasing l2 d -> 
    subseq l1 l2 ->
    last l1 d <= last l2 d.
Proof.
  intros l1 l2 d H_length1 H_length2 H_incr H_subseq.
  assert (H_subseq_copy := H_subseq).
  apply (subseq_incl) in H_subseq.
  assert (H_in1 : In (nth (length l1 - 1) l1 d) l1).
  { apply nth_In; omega. }
  assert (H_in2 : In (nth (length l2 - 1) l2 d) l2).
  { apply nth_In; omega. }
  spec H_subseq (nth (length l1 - 1) l1 d) H_in1.
  clear H_in1.
  apply (In_nth _ _ d) in H_subseq.
  destruct H_subseq as [last_pos [last_pos_length last_pos_nth]].
  assert (last_pos = length l2 - 1 \/ last_pos < length l2 - 1) by omega.
  do 2 rewrite about_last_nth.
  destruct H as [H_eq | H_lt].    
  subst last_pos.
  rewrite last_pos_nth. reflexivity.
  rewrite <- last_pos_nth.
  apply Nat.lt_le_incl.
  apply H_incr. omega.
Qed.

(** Filter library **)
Theorem filter_nodup {X : Type} :
  forall (l : list X),
    NoDup l ->
    forall (f : X -> bool),
      NoDup (filter f l).
Proof.
  intros l H_nodup f.
  induction l as [|hd tl IHtl].
  - compute. constructor.
  - apply NoDup_cons_iff in H_nodup.
    destruct H_nodup. 
    spec IHtl H0. simpl.
    case_eq (f hd). intros.
    apply NoDup_cons_iff. split.
    intro not. apply filter_In in not.
    destruct not. contradiction. assumption.
    intro; assumption.
Qed.

Theorem filter_subseq_correct {X : Type} :
  forall (l : list X) (f : X -> bool),
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

Theorem filter_subseq_correct_nat :
  forall (l : list nat) (f : nat -> bool),
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

Theorem filter_incl {X : Type} :
  forall (l : list X) (f : X -> bool),
    incl (filter f l) l.
Proof.
  intros l f.
  intros w H_in.
  apply filter_In in H_in.
  destruct H_in; assumption. 
Qed.

(* Symphony of breakpoint_set_predicate obligations *) 
Theorem filter_increasing :
  forall (l : list nat) (d : nat),
    increasing l d ->
    forall (f : nat -> bool),
      increasing (filter f l) d.
Proof.
  intros.
  assert (H_rewrite := filter_subseq_correct_nat l f). 
  now apply subseq_incr with l.
Qed.

Theorem split_list {X : Type} :
  forall (l : list X) (n : nat),
    length l = n ->
    forall (m : nat), m <= n -> 
               exists l1 l2 : list X,
                 length l1 = m /\
                 length l2 = n - m. 
Proof.
  intros l n H_l m H_le. 
  destruct m. 
  - exists [], l. repeat split.
    omega.
  - exists (firstn (S m) l).
    exists (skipn (S m) l). split.
    rewrite firstn_length_le. reflexivity.
    omega. rewrite about_length_skipn.
    omega.
Qed.

Theorem get_subseq {X : Type} :
  forall (l : list X),
    forall (m : nat), m <= length l -> 
               exists l' : list X,
                 length l' = m /\
                 subseq l' l.
Proof.
  intros l m H_le.
  induction l as [|hd tl IHl].
  - simpl in H_le. subst. inversion H_le; subst.
    exists []. split; constructor.
  - apply le_lt_or_eq in H_le.
    destruct H_le as [H_lt | H_eq].
    + simpl in H_lt. spec IHl. omega.
      destruct IHl as [l' [l'_length l'_subseq]].
      exists l'. split. assumption. apply subseq_hn.
      assumption.
    + exists (hd :: tl).  split. symmetry; assumption.
      apply subseq_refl.
Qed.

(* Decidability is guaranteed by bool *) 
Theorem filter_length {X : Type} :
  forall (f : X -> bool) (l : list X),
    length (filter f l) + length (filter (fun n => negb (f n)) l) = length l.
Proof.
  intro f; induction l as [|hd tl IHl].
  - compute; reflexivity.
  - simpl. case_eq (f hd); intro.
    + simpl. rewrite IHl. reflexivity.
    + simpl. rewrite <- IHl. omega.
Qed. 

Theorem filter_subseq_correct' {X : Type} :
  forall (l : list X) (f : X -> bool),
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

Theorem short_subseq_inversion {X : Type} :
  forall (l1 l2 : list X),
    length l1 > length l2 ->
    subseq l1 l2 -> False.
Proof.
  intros l1 l2 H_length H_subseq.
  induction H_subseq; subst.
  simpl in H_length; inversion H_length.
  apply IHH_subseq. 
  simpl in H_length. omega.
  apply IHH_subseq. simpl in H_length. omega.
Qed.

Lemma firstn_skipn_shortens {X : Type} :
  forall (l : list X) (i j : nat),
    i < j < length l ->
    length (firstn i l ++ skipn j l) < length l.
Proof.
  intros l i j H_lt.
  rewrite app_length. 
  rewrite firstn_length.
  rewrite about_length_skipn.
  assert (min i (length l) = i).
  assert (i <= length l) by omega. 
  apply min_l in H. rewrite H. reflexivity.
  rewrite H. omega.
Qed.

Theorem subseq_grow :
  forall (n m : nat),
    m > n ->
    subseq (iota 0 n) (iota 0 m).
Proof.
  intros n m H_gt.
  induction m as [|m IHn].
  - inversion H_gt. 
  - assert (m > n \/ m = n) by omega.
    destruct H as [H_strict | H_eq].
    + spec IHn H_strict.
      replace (S m) with (m + 1) by omega.
      rewrite iota_add.
      assert (subseq [] (iota (0 + m) 1)) by constructor.
      replace (iota 0 n) with (iota 0 n ++ []) by (rewrite app_nil_r; reflexivity).
      apply subseq_app; assumption.
    + rewrite H_eq.
      replace (S n) with (n + 1) by omega.
      rewrite iota_add.
      replace (iota 0 n) with (iota 0 n ++ []) by (rewrite app_nil_r; reflexivity).
      apply subseq_app. rewrite app_nil_r.
      apply subseq_refl.
      constructor.
Qed.

Theorem subseq_cons {X : Type} :
  forall (l : list X) (hd : X) (tl : list X),
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

Theorem subseq_cons_or {X : Type} :
  forall (hd : X) (tl lw : list X),
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

Theorem firstn_nil_inversion {X : Type} :
  forall (l : list X) (n : nat),
    firstn n l = [] -> n = 0 \/ n > length l. 
Proof.
  intros.
  induction n.
  - left; reflexivity.
  - right; destruct l.
    simpl; omega.
    simpl in H. inversion H.
Qed.
