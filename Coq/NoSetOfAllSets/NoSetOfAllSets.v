Axiom SetT : Type.
Axiom elementOf : SetT -> SetT -> Prop.
Infix "∈" := elementOf (at level 70).

Axiom extensionality : forall a b, (a = b -> (forall x, x ∈ a <-> x ∈ b)).

Axiom empty_set : SetT.
Notation "∅" := empty_set.
Axiom empty_spec : forall x, ~ x ∈ ∅.

Axiom pairing : forall x y, exists z, x ∈ z /\ y ∈ z.

Definition subset : SetT -> SetT -> Prop := fun A B => forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70).

Axiom intersection : SetT -> SetT -> SetT.
Infix "∩" := intersection (at level 70).
Axiom intersection_spec : forall a b x, x ∈ (a ∩ b) <-> x = a /\ x = b.

Axiom powerset : SetT -> SetT.
Axiom powerset_spec : forall a x, x ⊆ a <-> x ∈ powerset a.

Theorem theorem1 : exists x : SetT, ∅ ∈ x /\ ~(∅ = x).
Proof.
  exists (powerset ∅).
  split.
  - (* Proof that empty_set ∈ powerset empty_set *)
    apply powerset_spec.  (* To show empty_set ∈ powerset empty_set, we need to show empty_set ⊆ empty_set *)
    unfold subset.        (* Unfold the definition of subset *)
    intros x Hx.          (* Assume x is an element of empty_set. We need to show x is an element of empty_set *)
    apply Hx.             (* This is trivially true by hypothesis Hx *)
  - (* Proof that ~(empty_set = powerset empty_set) *)
    intro H_eq.           (* Assume for contradiction that empty_set = powerset empty_set *)
    assert (∅ ∈ ∅). (* We know empty_set ∈ powerset empty_set from the first part of the proof.
                                     If powerset empty_set = empty_set, then empty_set must be an element of itself. *)
    {
      rewrite H_eq.        (* Use the assumption H_eq to rewrite empty_set with powerset empty_set *)
      apply powerset_spec. (* Apply powerset_spec to show empty_set ⊆ empty_set *)
      unfold subset.       (* Unfold subset *)
      intros y Hy.         (* Assume y ∈ empty_set *)
      rewrite <- H_eq in Hy.
      apply Hy.            (* Contradiction: if y ∈ empty_set, that's impossible by empty_spec *)
    }
    apply empty_spec in H. (* Now we have empty_set ∈ empty_set (from H) and ~empty_set ∈ empty_set (from empty_spec).
                             This is a contradiction. *)
    apply H.               (* Apply the contradiction *)
Qed.

Axiom regularity : forall x, ((x <> ∅) -> exists y, (y ∈ x /\ y ∩ x = ∅)).
Axiom union : forall f, exists a, forall y, forall x, ((x ∈ y /\ y ∈ f) -> x ∈ a).

Theorem no_set_is_its_own_member : ~(exists x, x ∈ x).
Proof.
  intro.
  destruct H.
  specialize regularity with (x := x).
  intros.
  assert (x <> ∅).
  {
    intro.
    specialize empty_spec with (x := x).
    intros.
    rewrite H1 in *.
    apply H2.
    apply H.
  }
  apply H0 in H1. clear H0.
  destruct H1.
  destruct H0.
  pose proof pairing.
  pose proof union.
Admitted.

Theorem no_set_of_all_sets : ~(exists x, forall y, y ∈ x).
Proof.
  intro.
  destruct H.
  specialize H with (y := x).
  pose proof no_set_is_its_own_member.
  apply H0. clear H0.
  exists x.
  apply H.
Qed.
