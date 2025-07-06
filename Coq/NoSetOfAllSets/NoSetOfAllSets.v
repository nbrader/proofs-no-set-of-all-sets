Axiom SetT : Type.
Axiom elementOf : SetT -> SetT -> Prop.
Infix "∈" := elementOf (at level 70).

Axiom extensionality : forall a b, (a = b -> (forall x, x ∈ a <-> x ∈ b)).

Axiom pairing : forall x y, exists z, x ∈ z /\ y ∈ z.

Definition subset : SetT -> SetT -> Prop := fun A B => forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70).

Axiom intersection : SetT -> SetT -> SetT.
Infix "∩" := intersection (at level 70).
Axiom intersection_spec : forall a b x, x ∈ (a ∩ b) <-> x = a /\ x = b.

Axiom powerset : SetT -> SetT.
Axiom powerset_spec : forall a x, x ⊆ a <-> x ∈ powerset a.

Axiom specification : forall (P : SetT -> Prop), forall z, exists y, forall x, x ∈ y <-> ((x ∈ z) /\ P x).

(* Alternative even more direct proof *)
Theorem no_set_of_all_sets_direct : ~(exists x, forall y, y ∈ x).
Proof.
  intro H.
  destruct H as [U HU].
  
  (* Construct Russell's set *)
  pose proof (specification (fun x => ~(x ∈ x)) U) as H_spec.
  destruct H_spec as [R HR].
  
  (* R ∈ U since U contains all sets *)
  assert (R ∈ U) as H_R_in_U by apply HU.
  
  (* The key insight: we can derive both R ∈ R and ¬(R ∈ R) *)
  (* First, assume R ∈ R and derive contradiction *)
  assert (~(R ∈ R)) as H_not_R_in_R.
  {
    intro H_R_in_R.
    (* If R ∈ R, then by definition of R, we have R ∈ U ∧ ¬(R ∈ R) *)
    apply HR in H_R_in_R as H.
    destruct H as [_ H_not_R_in_R].
    (* So ¬(R ∈ R), contradicting our assumption *)
    exact (H_not_R_in_R H_R_in_R).
  }
  
  (* Now derive R ∈ R *)
  assert (R ∈ R) as H_R_in_R.
  {
    (* Since R ∈ U and ¬(R ∈ R), by definition of R we have R ∈ R *)
    apply HR.
    split.
    - exact H_R_in_U.
    - exact H_not_R_in_R.
  }
  
  (* Final contradiction *)
  exact (H_not_R_in_R H_R_in_R).
Qed.

Axiom union : forall f, exists a, forall y, forall x, ((x ∈ y /\ y ∈ f) -> x ∈ a).

(*
Axiom infinite_set_exists : exists X, (exists e, (forall z, ~(z ∈ e) /\ (e ∈ X) /\ forall y, y ∈ X -> (y ∪ singleton y) ∈ X)).

Theorem a_set_exists : exists x : SetT, x = x.
Proof.
  pose proof (specification (fun x => x = x)).
  
Qed.

Definition empty : SetT -> Prop := fun s => forall x, ~ x ∈ s.
Theorem empty_set_exists : exists x, empty x.
Proof.
  pose proof (specification empty).
  reflexivity.
Qed.

Axiom regularity : forall x e, empty e -> ((x <> e) -> exists y, (y ∈ x /\ y ∩ x = e)).
*)
