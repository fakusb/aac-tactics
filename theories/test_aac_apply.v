Require Import AAC.
Require Instances.
Require Arith ZArith.


Goal forall x y c, x <= y -> x + c <= c + y.
Proof.
  intros.
  aac_apply Plus.plus_le_compat_r.
  exact H.
Qed.

