From LF Require Export Sample.
Export Core.

From Coq Require Import QArith Qcanon DecimalQ.
Open Scope Q_scope.

Definition result := (15 # 10) * (20 # 10).
Compute (85.0 * (2.0*2.0) * 30.0 * 3.1459).

Definition nega (a:assert) : assert :=
    if a then No else Yes.