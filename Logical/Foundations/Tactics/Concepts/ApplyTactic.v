Require Export LF.Poly.Concepts.Polymorphism.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  rewrite -> eq.
  reflexivity.
Qed.

(* this proof is simpler than the above, by using the apply tactic we simplify
    the proof length. *)
Theorem silly1' : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Check [1;2].

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. 
Qed.

Theorem silly2' : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p H1 H2.
  rewrite H2. 
  - reflexivity.
  - rewrite H1. reflexivity.
Qed.


