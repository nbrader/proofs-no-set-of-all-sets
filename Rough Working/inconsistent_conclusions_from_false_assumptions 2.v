Variable x : bool.
Variable x_val_1 : x = false.
Variable x_val_2 : x = true.

(* Derive a contradiction *)
Lemma paradox : False.
Proof.
  cut (true = false).
  - intro. inversion H.
  - pose proof x_val_1 as x_val_1.
    pose proof x_val_2 as x_val_2.
    rewrite x_val_2 in x_val_1.
    apply x_val_1.
Qed.