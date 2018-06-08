Require Import Relations.

(** * Classes for properties of operators *)

Class Associative {X:Type} (R:relation X) (dot: X -> X -> X) :=
  law_assoc : forall x y z, R (dot x (dot y z)) (dot (dot x y) z).
Class Commutative {X:Type} (R: relation X) (plus: X -> X -> X) :=
  law_comm: forall x y, R (plus x y) (plus y x).
Class Unit {X:Type} (R:relation X) (op : X -> X -> X) (unit:X) := {
  law_neutral_left: forall x, R (op unit x) x;
  law_neutral_right: forall x, R (op x unit) x
}.

(** * Classes for properties of homogeneous operators*)
Class HAssociative {Obj: Type} {Arr:Obj -> Obj -> Type} (R:forall A B, relation (Arr A B)) (comp: forall A B C, Arr B C -> Arr A B -> Arr A C) :=
  lawH_assoc : forall A B C D (x: Arr C D) (y: Arr B C) (z: Arr A B), R _ _ (comp _ _ _ x (comp _ _ _ y z)) (comp _ _ _ (comp _ _ _ x y) z).
Class HCommutative {Obj: Type} {Arr:Obj -> Obj -> Type} (R:forall A B, relation (Arr A B)) (comp: forall A B C, Arr B C -> Arr A B -> Arr A C) :=
  lawH_comm: forall A (x y: Arr A A), R _ _ (comp _ _ _ x y) (comp _ _ _ y x).
Class HUnit {Obj:Type} {Arr:Obj -> Obj -> Type} (R:forall A B, relation (Arr A B)) (comp: forall A B C, Arr B C -> Arr A B -> Arr A C) (unit:forall A, Arr A A) := {
  lawH_neutral_left: forall A B (x:Arr A B), R _ _ (comp _ _ _ (unit _) x) x;
  lawH_neutral_right: forall A B (x:Arr A B), R _ _ (comp _ _ _ x (unit _)) x
}.
