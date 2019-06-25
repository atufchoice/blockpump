Require Import Arith Bool List Nat Omega Classical.  
Import ListNotations. 
From Block
Require Import lib. 

(* Our pigeons need to be languages *) 
Inductive repeats {X : Type} : list X -> Prop :=
  | repeats_intro : forall l1 l2, (exists x, In x l1 /\ In x l2) -> repeats (l1 ++ l2).

Lemma repeats_cons {X : Type} : forall (l : list X),
    repeats l -> forall (x : X), repeats (x :: l). 
Proof.
  intros l H_repeats x. 
  inversion H_repeats. 
  destruct H as [x' [H_in1 H_in2]].
  replace (x :: l1 ++ l2) with ((x::l1) ++ l2).
  apply repeats_intro.
  exists x'. split. right; assumption. assumption.
  easy.
Qed.

Theorem pigeonhole_principle {X : Type} : forall (l1 l2 : list X),
    incl l1 l2 -> 
    length l2 < length l1 ->
    repeats l1.
Proof.
  intros l1.
  induction l1 as [|x tl1 IHtl1]; intros l2 H_incl H_length.
  - unfold length in H_length; inversion H_length. 
  - assert (H_x_l2 : In x l2).
    { apply H_incl. left; reflexivity. }   
    destruct (classic (In x tl1)) as [H_in | H_notin]. 
    + (* In the case that x is in the rest of l1 *)
      (* The repeated element is just x itself *)
      replace (x :: tl1) with ([x] ++ tl1).
      2 : simpl; reflexivity.
      apply repeats_intro.
      exists x. split. constructor; reflexivity.
      assumption.
    + (* In the case that x is not in the rest of l1 *)
      apply in_split in H_x_l2.
      destruct H_x_l2 as [l2_front [l2_back l2_split]].
      spec IHtl1 (l2_front ++ l2_back).
      spec IHtl1.
      { unfold incl; intros.
        assert (a <> x).
        intro not. subst. contradiction.
        spec H_incl a. spec H_incl.
        right; assumption.
        rewrite l2_split in H_incl.
        apply in_app_or in H_incl.
        destruct H_incl as [H_left | H_right].
        apply in_or_app. left; assumption.
        destruct H_right. symmetry in H1; contradiction.
        apply in_or_app. right; assumption. }
      spec IHtl1. 
      rewrite l2_split in H_length.
      rewrite app_length in H_length. 
      simpl in H_length.
      assert (length l2_front + length l2_back < length tl1) by omega.
      rewrite app_length in IHtl1.
      spec IHtl1 H; clear H.
      rewrite app_length; omega.
      simpl in H_length.
      now apply repeats_cons.
Qed.
