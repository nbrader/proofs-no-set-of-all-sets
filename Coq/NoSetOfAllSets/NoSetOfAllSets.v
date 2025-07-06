Axiom SetT : Type.
Axiom member : SetT -> SetT -> Prop.
Infix "∈" := member (at level 70).

Definition subset : SetT -> SetT -> Prop := fun A B => forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70).

(* Axiom Schema of Specification *)
Axiom specification_axiom : forall (P : SetT -> Prop), forall A, exists B, forall x, x ∈ B <-> ((x ∈ A) /\ P x).

Theorem no_set_of_all_sets : ~(exists U, forall X, X ∈ U).
Proof.
  intro H_univ_set_exists.
  destruct H_univ_set_exists as [U H_U_is_univ].

  (* Construct Russell's set 'R' *)
  (* The property P for Russell's set is 'x is not a member of x' *)
  pose proof (specification_axiom (fun x => ~(x ∈ x)) U) as H_russell_spec.
  destruct H_russell_spec as [R H_R_def].

  (* R ∈ U since U contains all sets *)
  assert (R ∈ U) as H_R_in_U by apply H_U_is_univ.

  (* The key insight: we can derive both R ∈ R and ¬(R ∈ R) *)
  (* First, assume R ∈ R and derive contradiction *)
  assert (~(R ∈ R)) as H_not_R_in_R.
  {
    intro H_R_in_R.
    (* If R ∈ R, then by definition of R, we have R ∈ U ∧ ¬(R ∈ R) *)
    apply H_R_def in H_R_in_R as H_R_def_expanded.
    destruct H_R_def_expanded as [_ H_R_not_in_R_from_def].
    (* So ¬(R ∈ R), contradicting our assumption *)
    exact (H_R_not_in_R_from_def H_R_in_R).
  }

  (* Now derive R ∈ R *)
  assert (R ∈ R) as H_R_in_R.
  {
    (* Since R ∈ U and ¬(R ∈ R), by definition of R we have R ∈ R *)
    apply H_R_def.
    split.
    - exact H_R_in_U.
    - exact H_not_R_in_R.
  }

  (* Final contradiction *)
  exact (H_not_R_in_R H_R_in_R).
Qed.

(* Axiom of Pairing *)
Axiom pairing_axiom : forall x y, exists pair_set, forall t, t ∈ pair_set <-> (t = x \/ t = y).

(* Axiom of Powerset *)
Axiom powerset_axiom : forall base_set, exists power_set, forall x, x ⊆ base_set <-> x ∈ power_set.

(* Axiom of Extensionality *)
Axiom extensionality_axiom : forall A B, (forall x, x ∈ A <-> x ∈ B) -> A = B.

(* Axiom of Union *)
Axiom union_axiom : forall family_of_sets, exists union_set, forall x, x ∈ union_set <-> (exists y, y ∈ family_of_sets /\ x ∈ y).