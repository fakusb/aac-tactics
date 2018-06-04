Require Import AAC AAC_hetero.
Require Instances.
Require Arith ZArith.


Section test.
  Import ReifH Utils. 
  Require Import Arith NArith.
  Import List.ListNotations.
  
  Goal (forall (x y :nat), x + 1 <= y -> x + 2 <= 1 + y).
  Proof. 
    intros x y H.
    pose (v_type := (Prop:::(nat:Type):::(@nilne Type Datatypes.unit))).
    pose (e_sym_def iTy def (i:idx) := ReifH.mkSym v_type iTy [] def). Print Scopes.
    pose (e_sym_prop := sigma_get (ReifH.mkSym v_type 0 [1;1] le) (sigma_add 1%positive (ReifH.mkSym v_type 0 [1;1] le) sigma_empty)).
    pose (e_sym_nat := sigma_get (ReifH.mkSym v_type 1 [] O)
                                 (sigma_add 4%positive (ReifH.mkSym v_type 1 [] y)
                                            (sigma_add 3%positive (ReifH.mkSym v_type 1 [] x)
                                                       (sigma_add 2%positive (ReifH.mkSym v_type 1 [] O)
                                                                  (sigma_add 1%positive (ReifH.mkSym v_type 1 [1] S) sigma_empty))))).
    pose (e_sym iTy :=
            match iTy return idx -> ReifH.Sym v_type iTy with
              0 => e_sym_prop
            | 1 => e_sym_nat
            | S (S iTy) => fun i => ReifH.mkSym v_type (S (S iTy)) [] tt
            end).

    (* TODO: - having no symbol or binOp is possible for any type, so this needs to be encorperated *)

    Lemma const_Assoc {X:Type} (x:X) :Associative eq (fun _ _ => x).
    Proof.
      cbv. intros. reflexivity.
    Qed.
    
    pose (e_bin iTy :=
            match iTy return idx -> ReifH.Bin v_type iTy with
            | 0 => fun _ => ReifH.mkBin v_type 0 (const_Assoc True) None
            | 1 => fun _ => ReifH.mkBin (bin_value := Nat.add) v_type 1 (Nat.add_assoc) None
            | S (S iTy) => fun _ => ReifH.mkBin v_type (S (S iTy)) (const_Assoc tt) None
            end).
    pose (e_unit iTy :=
            match iTy return idx -> unit_pack e_bin iTy with
            | 0 => fun _ => @mk_unit_pack v_type e_bin 0 True nil
            | 1 => fun _ => @mk_unit_pack v_type e_bin 1 0 nil
            | S (S iTy) => fun _ => @mk_unit_pack v_type e_bin (S (S iTy)) tt nil
            end).
    Compute (@ReifH.eval v_type e_sym e_bin e_unit 0 (sym 0 1 (vcons (sym 1 2 (@vnil v_type e_sym)) (vcons (sym 1 2 (@vnil v_type e_sym)) (@vnil _ _))))).

    Compute (@ReifH.eval v_type e_sym e_bin e_unit 0 (sym 0 1
                                                          (vcons (sum 1 (( sym 1 3 (@vnil v_type e_sym) ,1%positive)
                                                                           ::: @nilne _ ( sym 1 1 (vcons (sym 1 1 (vcons (sym 1 2 ((@vnil v_type e_sym))) (@vnil v_type e_sym))) (@vnil v_type e_sym)) ,1%positive)))
                                                                 (vcons ((sum 1 (( sym 1 1 ( (vcons (sym 1 2 ((@vnil v_type e_sym))) (@vnil v_type e_sym))) ,1%positive)
                                                                                   ::: @nilne _ ( sym 1 4 (@vnil v_type e_sym) ,1%positive) ))) (@vnil _ _))))).

    (* This example does not recognize the units*)
    change (@ReifH.eval v_type e_sym e_bin e_unit 0 (sym 0 1
                                                          (vcons (sum 1 (( sym 1 3 (@vnil v_type e_sym) ,1%positive)
                                                                           ::: @nilne _ ( sym 1 1 (vcons (sym 1 1 (vcons (sym 1 2 ((@vnil v_type e_sym))) (@vnil v_type e_sym))) (@vnil v_type e_sym)) ,1%positive)))
                                                                 (vcons ((sum 1 (( sym 1 1 ( (vcons (sym 1 2 ((@vnil v_type e_sym))) (@vnil v_type e_sym))) ,1%positive)
                                                                                   ::: @nilne _ ( sym 1 4 (@vnil v_type e_sym) ,1%positive) ))) (@vnil _ _))))).
    Abort.
End test. 
Goal forall x y c, x <= y -> x + c <= c + y.
Proof.
  intros.
  aac_apply Plus.plus_le_compat_r.
  exact H.
Qed.

