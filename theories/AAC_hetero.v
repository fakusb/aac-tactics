(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2018: Fabian Kunze.                                     *)
(***************************************************************************)

(** * Theory file for the aac_apply tactic

   
   We define several base classes to package associative and possibly
   commutative operators, and define a data-type for reified (or
   quoted) expressions.

   We then define a reflexive decision procedure to decide the
   equality of reified terms: first normalise reified terms, then
   compare them. This allows us to close transitivity steps
   automatically, in the [aac_rewrite] tactic.

   This currently just handles equality as relation.

   It handles assoc/commutaive functions over different types, but each function must be homogeneous (of shape X -> X -> X) *)

Require Import Utils.
Require Export Interface.

Set Implicit Arguments.
Set Asymmetric Patterns.


Module ReifH.
  Section ReifH.
    (* We use environments to store the various operators and the
     morphisms.*)

    Variable e_type:idx -> Type.

    (** ** free symbols  *)
    Section Sym.
      (** type of an arity  *)
      Fixpoint type_of_ar (ar: nelist idx) :=
        match ar with
        | nil i => e_type i
        | cons i ar => (e_type i) -> type_of_ar ar
        end.

      (** a symbol package contains an arity and a value of the corresponding type*)
      Record Sym  : Type :=
        mkSym {
            sym_ar : nelist idx;
            sym_value :> type_of_ar sym_ar;
          }.

    End Sym.

    (** ** binary operations *)

    Section Bin.
      Record Bin :=
        mkBin {
            bin_iTy : idx;
            bin_X := e_type bin_iTy;
            bin_value:> bin_X -> bin_X -> bin_X;
            bin_assoc: Associative (@eq bin_X) bin_value;
            bin_comm: option (Commutative eq bin_value)
          }.
    End Bin.

    Arguments bin_value : clear implicits.
    Arguments bin_iTy : clear implicits.

    Variable e_sym: idx -> Sym.
    Variable e_bin: idx -> Bin.

    (** packaging units (depends on e_bin) *)

    Record unit_of iTy (u:e_type iTy) :=
      mk_unit_for {
          uf_iBin: idx;
          uf_bin := e_bin uf_iBin;
          uf_eq : iTy = @bin_iTy uf_bin;
          uf_desc: Unit (@eq _) (@bin_value uf_bin) (cast _ uf_eq u)
        }.


    Record unit_pack :=
      mk_unit_pack {
          u_iTy : idx;
          u_value:> e_type u_iTy;
          u_desc: list (unit_of u_value)
        }.
    Variable e_unit: idx -> unit_pack.

    Inductive T: idx -> Type :=
    | sum (i : idx) : let iTy := bin_iTy (e_bin i)
                      in mset (T iTy) -> T iTy
    (*| prd: idx -> nelist T -> T*)
    | sym i: let ar := sym_ar (e_sym i) in
             vT ar -> T (lastne ar)
    | unit i: T (u_iTy (e_unit i))
    with vT: nelist idx -> Type :=
         | vnil X: vT (nil X)
         | vcons X ar: T X -> vT ar -> vT (X::ar).

    Arguments vnil {X}.

    (** lexicographic rpo over the normalised syntax *)
    Fixpoint compare {iTy jTy} (u: T iTy) (v: T jTy) :=
      match u,v with
      | sum i l, sum j vs => lex (idx_compare i j) (mset_compare compare l vs)
      (*| prd i l, prd j vs => lex (idx_compare i j) (list_compare compare l vs)*)
      | sym i l, sym j vs => lex (idx_compare i j) (vcompare l vs)
      | unit i , unit j => idx_compare i j
      | unit _ , _        => Lt
      | _      , unit _  => Gt
      | sum _ _, _        => Lt
      | _      , sum _ _  => Gt
      (*| prd _ _, _        => Lt
      | _      , prd _ _  => Gt*)

      end
    with vcompare {ar1 ar2} (us: vT ar1) (vs: vT ar2) :=
           match us,vs with
           | vnil _, vnil _ => Eq
           | vnil _, _    => Lt
           | _,    vnil _ => Gt
           | vcons _ _ u us, vcons _ _ v vs => lex (compare u v) (vcompare us vs)
           end.

    (** ** Evaluation from syntax to the abstract domain *)

    Fixpoint eval {iTy} (u : T iTy) : (e_type iTy) :=
      match u with
      | sum i l => let o := @bin_value (e_bin i) in
                  fold_map (fun un => let '(u,n):=un in @copy _ o n (eval u)) o l
      (*| prd i l => fold_map eval (Bin.value (e_bin i)) l*)
      | sym i v => eval_aux v (sym_value (e_sym i))
      | unit i  => e_unit i
      end
    with eval_aux {ar} (v: vT ar): type_of_ar ar -> e_type (lastne ar) :=
           match v with
           | vnil iTy => fun f => f
           | vcons X ar x v => fun f => eval_aux v (f (eval x))
           end.

  End ReifH.
