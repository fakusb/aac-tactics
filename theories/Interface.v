Require Import Relations.

Set Implicit Arguments.
Set Asymmetric Patterns.


(** * Classes for properties of operators *)

Class Associative (X:Type) (R:relation X) (dot: X -> X -> X) :=
  law_assoc : forall x y z, R (dot x (dot y z)) (dot (dot x y) z).
Class Commutative (X:Type) (R: relation X) (plus: X -> X -> X) :=
  law_comm: forall x y, R (plus x y) (plus y x).
Class Unit (X:Type) (R:relation X) (op : X -> X -> X) (unit:X) := {
  law_neutral_left: forall x, R (op unit x) x;
  law_neutral_right: forall x, R (op x unit) x
}.
