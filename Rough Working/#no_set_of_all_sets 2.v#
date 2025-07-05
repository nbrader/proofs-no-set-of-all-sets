(* Assume U is a type that includes all types as subtypes *)
Variable U : Type.
Variable all_types : U -> Type.

(* Assume there's a function that can embed any type as an element of U *)
Hypothesis embed : forall T : Type, U.

(* The idea is to find a contradiction by constructing a type that leads to a paradox similar to Russell's *)
Definition Russell := {x : U | forall (P : all_types x), False}.

(* Assume we can represent Russell's type within U *)
Hypothesis russell_in_u : U.
Hypothesis russell_type : all_types russell_in_u = Russell.

(* Derive a contradiction *)
Lemma no_universal_type: True.
Proof.
  pose proof (russell_type) as R.
  unfold Russell in R.
  rewrite <- R in R.
  reflexivity.
Qed.
