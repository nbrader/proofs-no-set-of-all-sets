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

Axiom specification_0 : forall (P : SetT -> SetT -> Prop),         forall z   , exists y, forall x, x ∈ y <-> ((x ∈ z) /\ P x    z).
Axiom specification_1 : forall (P : SetT -> SetT -> SetT -> Prop), forall z w1, exists y, forall x, x ∈ y <-> ((x ∈ z) /\ P x w1 z).

Theorem no_set_of_all_sets : ~(exists x, forall y, y ∈ x).
Proof.
  intro H.
  destruct H as [U HU].
  (* U is supposed to be the set of all sets *)
  
  (* Apply specification to construct Russell's set: {x ∈ U | x ∉ x} *)
  pose proof (specification_0 (fun x _ => ~(x ∈ x)) U) as H_spec.
  destruct H_spec as [R HR].
  
  (* R is the Russell set: x ∈ R iff x ∈ U and x ∉ x *)
  (* Since U contains all sets, R ∈ U *)
  assert (R ∈ U) as H_R_in_U.
  { apply HU. }
  
  (* Now we derive a direct contradiction *)
  (* Consider the statement "R ∈ R" *)
  assert (R ∈ R <-> (R ∈ U /\ ~(R ∈ R))) as H_equiv.
  { apply HR. }
  
  (* This gives us: R ∈ R iff (R ∈ U and ¬(R ∈ R)) *)
  (* Since we know R ∈ U, this simplifies to: R ∈ R iff ¬(R ∈ R) *)
  assert (R ∈ R <-> ~(R ∈ R)) as H_paradox.
  { 
    split.
    - intro H_in.
      apply H_equiv in H_in.
      destruct H_in as [_ H_not_in].
      exact H_not_in.
    - intro H_not_in.
      apply H_equiv.
      split.
      + exact H_R_in_U.
      + exact H_not_in.
  }
  
  (* Now we have R ∈ R iff ¬(R ∈ R), which is impossible *)
  (* This is equivalent to P iff ¬P, which implies ¬P *)
  assert (~(R ∈ R)) as H_not_R_in_R.
  {
    intro H_R_in_R.
    apply H_paradox in H_R_in_R as H_R_in_R'.
    apply H_R_in_R'.
    apply H_R_in_R.
  }
  
  (* But we can also derive R ∈ R *)
  assert (R ∈ R) as H_R_in_R.
  {
    apply H_paradox.
    exact H_not_R_in_R.
  }
  
  (* Final contradiction *)
  exact (H_not_R_in_R H_R_in_R).
Qed.

(* Alternative even more direct proof *)
Theorem no_set_of_all_sets_direct : ~(exists x, forall y, y ∈ x).
Proof.
  intro H.
  destruct H as [U HU].
  
  (* Construct Russell's set *)
  pose proof (specification_0 (fun x _ => ~(x ∈ x)) U) as H_spec.
  destruct H_spec as [R HR].
  
  (* R ∈ U since U contains all sets *)
  assert (R ∈ U) as H_R_in_U by apply HU.
  
  (* The key insight: we can derive both R ∈ R and ¬(R ∈ R) *)
  (* First, assume R ∈ R and derive contradiction *)
  assert (~(R ∈ R)) as H1.
  {
    intro H_R_in_R.
    (* If R ∈ R, then by definition of R, we have R ∈ U ∧ ¬(R ∈ R) *)
    apply HR in H_R_in_R as H.
    destruct H as [_ H_not_R_in_R].
    (* So ¬(R ∈ R), contradicting our assumption *)
    apply H_not_R_in_R.
    apply H_R_in_R.
  }
  
  (* Now derive R ∈ R *)
  assert (R ∈ R) as H2.
  {
    (* Since R ∈ U and ¬(R ∈ R), by definition of R we have R ∈ R *)
    apply HR.
    split.
    - exact H_R_in_U.
    - exact H1.
  }
  
  (* Final contradiction *)
  exact (H1 H2).
Qed.

Axiom law_of_excluded_middle : forall P : Prop, P \/ ~ P.

Theorem no_set_of_all_sets_lem : ~(exists x, forall y, y ∈ x).
Proof.
  intro.
  destruct H.
  pose proof (specification_0 (fun x _ => ~(x ∈ x)) x).
  destruct H0.
  specialize H0 with (x := x0) as H1.
  destruct H1.
  assert (x0 ∈ x0 \/ ~ (x0 ∈ x0)).
  {
    apply law_of_excluded_middle.
  }
  destruct H3.
  - apply H1.
    + apply H3.
    + apply H3.
  - assert (x0 ∈ x /\ x0 ∈ x0).
    {
      split.
      - apply H.
      - apply H0.
        split.
        + apply H.
        + apply H3.
    }
    destruct H4.
    apply H3.
    apply H5.
Qed.

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

Theorem no_set_of_all_sets_2 : ~(exists x, forall y, y ∈ x).
Proof.
  intro.
  destruct H.
  specialize H with (y := x).
  pose proof no_set_is_its_own_member.
  apply H0. clear H0.
  exists x.
  apply H.
Qed.
