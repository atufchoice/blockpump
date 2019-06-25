Require Import List Classical FunctionalExtensionality ExtensionalityFacts ChoiceFacts Wellfounded FinFun Fin.
Import ListNotations. 

Tactic Notation "spec" hyp(H) :=
  match type of H with
    ?a -> _ => let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H])
  end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

(* **************** *)
(* **** Axioms **** *)
(* **************** *)

Axiom choice : FunctionalChoice.

Axiom choice' : FunctionalRelReification.

(* ************************************************* *)
(* **** Dependent finite injectivity playground **** *)
(* ************************************************* *)

Definition is_finite {X : Type} (P : X -> Prop) : Prop :=
  exists L : list X, forall (x : X), In x L <-> P x.

Definition is_finite_dep {X : Type} (P : X -> Prop) : Prop :=
  exists L : list {x | P x}, forall (dep_x : {x | P x}), In dep_x L. 

Definition injective {X Y : Type} (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x}  -> {y | Q y})
  := @Injective {x | P x} {y | Q y} f.

Theorem inj_finite {X Y : Type} :
  forall (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x}  -> {y | Q y}),
    inhabited {x | P x} -> 
    injective P Q f ->
    is_finite_dep Q ->
    is_finite_dep P.
Proof. 
  intros P Q f H_witness H_inj H_Q_fin.
  unfold injective, Injective in H_inj.
  (* Every y either is reachable by some x or not reachable by any x *)
  (* This is the preamble to choice *) 
  assert (H_frel : forall y, exists x, f x = y \/ forall x', f x' <> y). 
  { intro y. destruct (classic (exists x, f x = y)). 
    destruct H as [x H]. 
    exists x; left; assumption.
    destruct H_witness as [x0].
    exists x0. right. intros x_absurd H_absurd.
    apply H. exists x_absurd. assumption. } 
  (* Using choice to get the actual function from Y -> X *)
  apply choice in H_frel. 
  destruct H_frel as [g Hfrel].
  destruct H_Q_fin as [L H_Q_fin]. 
  exists (map g L).
  intro sig_x. 
  spec H_Q_fin (f sig_x).
  apply (in_map g L (f sig_x)) in H_Q_fin.
  replace (g (f sig_x)) with sig_x in H_Q_fin.
  assumption.
  assert (forall x, exists y, f x = y).
  { intro x. exists (f x). reflexivity. }
  spec H sig_x.
  destruct H as [y H].
  rewrite H.
  spec Hfrel y.
  destruct Hfrel as [Hyes | Habsurd].
  unfold injective, Injective in H_inj.
  spec H_inj sig_x (g y).
  assert (f sig_x = f (g y)).
  { rewrite H; rewrite Hyes; reflexivity. }
  spec H_inj H0; assumption.
  spec Habsurd sig_x.
  contradiction. 
Qed. 

(* This relies on law of excluded middle *) 
Lemma all_reachable {X Y : Type} :
  forall (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x}  -> {y | Q y}),
    inhabited {x | P x} ->
    forall y : {y | Q y},
    exists x : {x | P x},
      f x = y \/
      forall x' : {x | P x},
        f x' <> y.
Proof. 
  intros P Q f H_witness y.
  destruct (classic (exists x, f x = y)). 
  destruct H as [x H]. 
  exists x; left; assumption.
  destruct H_witness as [x0].
  exists x0. right. intros x_absurd H_absurd.
  apply H. exists x_absurd. assumption.
Qed.

Lemma about_non_unique {X Y : Type} :
  forall (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x} -> {y | Q y}),
  forall y : {y | Q y},
    injective P Q f ->
    ~ (exists! x : {x | P x},
      f x = y)
  <-> ((exists x1 x2 : {x | P x},
         f x1 = y /\ f x2 = y /\ x1 <> x2)
     \/ (forall x : {x | P x}, f x <> y)). 
Proof.
  intros P Q f y H_inj.
  split; intro H.
  - destruct (classic (exists x, f x = y)).
    + destruct H0 as [x H0].
      exfalso. destruct H. exists x. split. 
      exact H0. intros. spec H_inj x x'. apply H_inj.
      subst y. symmetry; assumption.
    + right. intros x. intro not.
      apply H0. exists x. assumption.
  - destruct H.
    + destruct H as [x1 [x2 [H1 [H2 Hneq]]]].
      intro not. unfold unique in not.
      destruct not. 
      destruct H.
      spec H0 x1 H1.
      spec H_inj x2 x. subst y.
      rewrite <- H2 in H.
      symmetry in H. spec H_inj H.
      subst x. symmetry in H_inj. contradiction.
    + intro not. destruct not. spec H x.
      destruct H0. contradiction.
Qed.

Definition reachable {X Y : Type} (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x} -> {y | Q y}) :=
  fun (dep_x : {x | P x}) (dep_y : {y | Q y}) => f dep_x = dep_y.

Definition surjective {X Y : Type} (P : X -> Prop) (Q : Y -> Prop)  (f : {x | P x}  -> {y | Q y}) :=
  forall (y : {y | Q y}), exists x : {x | P x}, f x = y. 

Lemma all_reachable_uniqlo {X Y : Type} :
  forall (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x}  -> {y | Q y}),
    injective P Q f ->
    surjective P Q f ->
    forall y : {y | Q y},
    exists! x : {x | P x},
      f x = y.
Proof. 
  intros P Q f H_inj H_surj y.
  spec H_surj y. destruct H_surj as [x ?].
  exists x. split. assumption.
  intros. eapply H_inj; eauto. congruence.
Qed.

Theorem inj_surj_finite {X Y : Type} :
  forall (P : X -> Prop) (Q : Y -> Prop) (f : {x | P x}  -> {y | Q y}),
    injective P Q f ->
    surjective P Q f ->
    is_finite_dep Q ->
    is_finite_dep P.
Proof.
  intros P Q f H_inj H_surj H_Q_fin. 
  (* Using definite description to get the actual function from Y -> X *)
  assert (H_choice := choice' _ _ _ (all_reachable_uniqlo P Q f H_inj H_surj)). 
  destruct H_choice as [g H_choice].
  (* Either g is the inverse or there is something wrong with our input *)
  destruct H_Q_fin as [L H_Q_fin] (* L contains all elements of dependent y *).
  (* The witness P list we need is constructed using choice-given g *) 
  exists (map g L).
  intro sig_x.
  spec H_choice (f sig_x). 
  spec H_inj (g (f sig_x)) sig_x.
  spec H_inj H_choice.
  rewrite <- H_inj.
  apply in_map.
  spec H_Q_fin (f sig_x). assumption.
Qed.

Definition get_hd {X : Type} :
  forall (P: X -> Prop) (L: list X) (hd : X) (tl : list X)
    (Hfin: forall x, In x L -> P x) (Heq : hd :: tl = L),
    {x | P x}.
Proof.
  intros P L hd tl Hfin Heq;
    rewrite <- Heq in Hfin.
  exists hd. spec Hfin hd (in_eq hd tl); apply Hfin; assumption.
Defined. 

Definition rest_fin {X : Type} :
  forall (P: X -> Prop) (L: list X) (hd : X) (tl : list X)
    (Hfin: forall x, In x L -> P x) (Heq : hd :: tl  = L),
  forall x, In x tl -> P x.
Proof.
  intros P L hd tl Hfin Heq x H.
  rewrite <- Heq in Hfin.
  apply (in_cons hd x tl) in H.
  spec Hfin x H; apply Hfin; assumption.
Defined.

(* Aha! I fully understand how this piece of magic works now *) 
Fixpoint build_dep_impl_list
         {X : Type}
         (P : X -> Prop)
         (L : list X)
         (Hfin : forall x, In x L -> P x) : list {x | P x} :=
  match L as l return ((l = L) -> list {x | P x}) with
  | nil =>
    fun _ => nil
  | a :: al =>
    fun h => cons (get_hd P L a al Hfin h)
               (build_dep_impl_list P al (rest_fin P L a al Hfin h))
  end (eq_refl L).
Print exist.

Fixpoint build_dep_impl_list' {X: Type} (P: X -> Prop) (L: list X)
         (Hfin: forall x, In x L -> P x): list {x | P x} :=
  match L as l return (l = L -> list {x | P x}) with
  | nil => fun _ => nil
  | hd :: tl =>
    fun h => cons (eq_rect (hd :: tl) _
                        (fun Hfin0 : forall x, In x (hd :: tl) -> P x =>
                           exist _ hd (Hfin0 hd (in_eq hd tl))) L h Hfin)
               (build_dep_impl_list' P tl (rest_fin P L hd tl Hfin h))
  end (eq_refl L).

Lemma build_dep_preserves_elements {X : Type} : forall (P : X -> Prop) (L : list X) (Hfin : forall x, In x L -> P x),
    map (fun dep_x => proj1_sig dep_x) (build_dep_impl_list P L Hfin) = L. 
Proof. 
  intros P l Hfin.
  induction l as [|hd tl IHl].
  - reflexivity.
  - simpl. 
    assert (map (fun dep_x : {x : X | P x} => proj1_sig dep_x)
                (build_dep_impl_list P tl (rest_fin P (hd :: tl) hd tl Hfin eq_refl))
            = tl) by intuition.
    rewrite IHl; reflexivity.
Qed.

Lemma in_map_inv {A B : Type} :
  forall (f : A -> B) (l : list A) (x : A),
    Injective f -> In (f x) (map f l) -> In x l.
Proof.
  intros f l x' H_inj H_map.
  unfold Injective in H_inj.
  apply (in_map_iff f l (f x')) in H_map.
  destruct H_map as [x [Heq H_in]].
  spec H_inj x x'.
  spec H_inj Heq; rewrite <- H_inj; assumption. 
Qed.

Lemma proj1_sig_injective {X : Type} :
    forall (P : X -> Prop)
      (x1 x2 : X) (H1 : P x1) (H2 : P x2),
      (exist P x1 H1) = (exist P x2 H2) <-> x1 = x2. 
Proof.
  intros P x1 x2 H1 H2; split.  
  - intro H_eq_dep.
    apply eq_sig_fst in H_eq_dep; assumption.
  - intro H_eq.
    subst. assert (H1 = H2) by eapply proof_irrelevance.
    rewrite H. reflexivity.
Qed.

Lemma proj1_sig_inj {X : Type} :
  forall (P : X -> Prop),
    Injective (fun (x : {x | P x}) => proj1_sig x). 
Proof.
  intro P; unfold Injective.
  intros x1 x2 H_eq.
  destruct x1 as [x1 about_x1];
    destruct x2 as [x2 about_x2]. 
  assert (H_useful := proj1_sig_injective P x1 x2 about_x1 about_x2).
  apply H_useful.
  assumption. 
Qed.

Lemma inj_in_map_iff :
  forall {X : Type} (P : X -> Prop) (f : {x | P x} -> X) (L : list {x | P x})
  (x : {x | P x}),
    In (proj1_sig x) (map (fun x => proj1_sig x) L) <-> In x L. 
Proof.
  intros X P f L x; split; intro H.
  - assert (H_useful := in_map_inv (fun x => proj1_sig x) L x).
    spec H_useful (proj1_sig_inj P).
    apply H_useful; exact H. 
  - assert (H_useful := in_map (fun x => proj1_sig x) L x). 
    spec H_useful H.
    exact H_useful.
Qed.

(** The key results! **)
Theorem list_to_dep_list : forall {X : Type} (P : X -> Prop),
    is_finite P -> is_finite_dep P. 
Proof.
  intros X P H_fin.
  destruct H_fin as [L H_fin].
  assert (forall x, In x L -> P x) by (intros; now apply H_fin).
  exists (build_dep_impl_list P L H).
  intros dep_x.
  destruct dep_x as [x about_x].
  spec H_fin x.
  destruct H_fin.
  spec H1 about_x.
  assert (H_useful := build_dep_preserves_elements P L H).
  assert (H_useful' := in_map_inv (fun x => proj1_sig x) (build_dep_impl_list P L H)).
  spec H_useful' (exist (fun x0 : X => P x0) x about_x).
  apply H_useful'.
  intros x0 x1 H_eq.
  destruct x0, x1. simpl in H_eq.
  apply proj1_sig_inj. exact H_eq.
  rewrite H_useful.
  simpl; exact H1.
Qed.   

Theorem dep_list_to_list : forall {X : Type} (P : X -> Prop),
    is_finite_dep P -> is_finite P.
Proof.
  intros X P H_fin_dep.
  destruct H_fin_dep as [L H_fin_dep].
  exists (map (fun x => proj1_sig x) L). 
  intro x; split; intro H.
  - rewrite in_map_iff in H.
    destruct H as [dep_x [H_eq H_in]].
    spec H_fin_dep dep_x. 
    rewrite <- H_eq.
    destruct dep_x as [dep_x about_dep_x]. 
    unfold proj1_sig; exact about_dep_x.
  - spec H_fin_dep (exist P x H).
    assert (H_useful := inj_in_map_iff P (fun x => proj1_sig x) L).
    spec H_useful (exist P x H). destruct H_useful as [_ right]; spec right H_fin_dep.
    assumption.
Qed.

Theorem is_finite_equiv : forall {X : Type} (P : X -> Prop),
    is_finite_dep P <-> is_finite P. 
Proof.
  intros X P; split.
  exact (dep_list_to_list P).
  exact (list_to_dep_list P).
Qed.

(* The subset of list L which satisfies P is finite *)
Lemma p_in_list_finite {X : Type} : forall (P : X -> Prop) (L : list X),
    is_finite (fun l => P l /\ In l L).
Proof.  
  intros P LS. 
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
    destruct (classic (P new_x)).
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

Lemma finite_conj {X : Type} : forall (P : X -> Prop) (Q : X -> X -> Prop),
    is_finite (fun l => P l) ->
    (forall L, is_finite (fun l => P l /\ Q L l)). 
Proof.     
  intros P Q H_fin L.
  destruct H_fin as [ls H_fin]. 
  assert (H_useful := p_in_list_finite (Q L) ls).
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

Lemma finite_conj_dep {X : Type} : forall (P : X -> Prop) (Q : X -> X -> Prop),
    is_finite (fun l => P l) ->
    (forall (x : X), P x -> forall x', Q x x' -> P x') -> 
    (forall (L : {l | P l}), is_finite (fun l => Q (proj1_sig L) l)).
Proof.
  intros P Q H_fin H_deriv L_dep.
  assert (H_useful := finite_conj P Q H_fin).
  destruct L_dep as [L_dep about_L_dep].
  spec H_useful L_dep.
  destruct H_useful as [LS H_useful].
  exists LS.
  intro x; split; intro H.
  spec H_useful x.
  apply H_useful. assumption.
  apply H_useful. split. simpl in *.
  spec H_deriv L_dep about_L_dep.
  spec H_deriv x H. assumption.
  simpl; assumption. 
Qed.

Lemma finite_conj_undep {X : Type} : forall (P : X -> Prop) (Q : X -> X -> Prop),
    is_finite (fun l => P l) ->
    (forall (x : X), P x -> forall x', Q x x' -> P x') -> 
    (forall (x : X), P x -> is_finite (fun l => Q x l)).
Proof.
  intros P Q H_fin H_deriv x H_P.
  assert (H_useful := finite_conj_dep P Q H_fin H_deriv).
  spec H_useful (exist P x H_P).
  destruct H_useful as [LS H_useful].
  exists LS.
  assumption. 
Qed.
