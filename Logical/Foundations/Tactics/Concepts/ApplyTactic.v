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

(* Apply will try to find appropriate values for variables.  In the following
   theorem apply eq2 will match q to n and r to m *)
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. 
Qed.

 (* apply will not work if the conclusion of the fact being applied does not match
    the goal exactly; as in this example; *)
Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  (* this will fail because the goal contains m = n while the implication 
  contains n = m*)
  Fail apply H.
  (* we must first apply the symettry tactic*)
  symmetry. apply H.
Qed.

