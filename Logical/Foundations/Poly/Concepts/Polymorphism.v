Inductive list (X:Type) : Type :=
    | nil
    | cons (x:X) (l:list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
end.

Fixpoint rev {X:Type} (l:list X) : list X :=
    match l with
        | nil => nil
        | cons h t => app (rev t) (cons h nil)
    end.

Fixpoint length {X : Type} (l : list X) : nat :=
    match l with
        | nil => 0
        | cons _ l' => S (length l')
    end.

Fail Definition mynil := nil.
Definition mynil : list nat := nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
        (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
        (at level 60, right associativity).

Check [1;2;3].

Print LoadPath.