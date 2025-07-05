Axiom SetT : Type.
Axiom elementOf : SetT -> SetT -> Prop.
Infix "∈" := elementOf (at level 70).

Axiom extensionality : forall A B, (A = B <-> (forall x, x ∈ A <-> x ∈ B)).

Axiom empty_set : SetT.
Axiom empty_spec : forall x, ~ x ∈ empty_set.

Axiom union : SetT -> SetT -> SetT.
Axiom union_spec : forall x a b, elementOf x (union a b) <-> x = a \/ x = b.

Definition subset : SetT -> SetT -> Prop := fun A B => forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70).

Axiom powerset : SetT -> SetT.
Axiom powerset_spec : forall x a, x ⊆ a <-> x ∈ powerset a.

Theorem theorem1 : exists x : SetT, elementOf empty_set x /\ ~(empty_set = x).
Proof.
  exists (powerset empty_set).
  split.
  - (* Proof that empty_set ∈ powerset empty_set *)
    apply powerset_spec.  (* To show empty_set ∈ powerset empty_set, we need to show empty_set ⊆ empty_set *)
    unfold subset.        (* Unfold the definition of subset *)
    intros x Hx.          (* Assume x is an element of empty_set. We need to show x is an element of empty_set *)
    apply Hx.             (* This is trivially true by hypothesis Hx *)
  - (* Proof that ~(empty_set = powerset empty_set) *)
    intro H_eq.           (* Assume for contradiction that empty_set = powerset empty_set *)
    assert (empty_set ∈ empty_set). (* We know empty_set ∈ powerset empty_set from the first part of the proof.
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
