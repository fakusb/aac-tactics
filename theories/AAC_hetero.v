(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(*                      2018: Fabian Kunze.                                *)
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

   It is able to handle operations that are associative, but not homogeneous, as e.g. function composition or arrow composition in category theory.
   Therefore, every type involved is seen as an category: There are 'objects' and 'arrows'.
   For homogenous types, on can e.g. use Unit as object Type.

   It handles assoc/commutaive functions over different types, but each function must be homogeneous (of shape X -> X -> X) *)

Require Import Utils.
Require Import BinPos.
Require Export Interface.
Require Import List.
Require Import PeanoNat. 
Import List.ListNotations.
Local Open Scope list_scope.


Set Implicit Arguments.


Module ReifH.
  Section ReifH.
    (* We use environments to store the various operators and the
     morphisms.*)
    Local Notation idC := nat.
    Local Notation idT := ((idC * idx * idx)%type).
    
    Lemma idT_eq_dec (x y : idT): {x = y} + {x <> y}.
    Proof.
      repeat decide equality.
    Qed.

    Local Hint Resolve idT_eq_dec.
    
    Variable l_type : nelist {obj : idx -> Type & idx -> idx -> Type}. (* The different kinds of types supported on various levels*)

    Fixpoint nthne X n (l:nelist X) {struct l}: X :=
      match l,n with
        nilne x,_ => x
      | consne x _,0 => x
      | consne _ l,S n => nthne n l
      end. 
    
    Let e_type := (fun (i:idT) => let '(i,l,r):= i in (projT2 (nthne i l_type)) l r).

    (* TODO: e_rel for different relations?*)
    (*Variable e_rel : forall iTy, e_type iTy -> e_type iTy -> Prop.*)

    (** ** free symbols  *)
    Section Sym.
      (** type of an arity  *)
      Fixpoint type_of_ar (args: list idT) ret:=
        match args with
        | nil => e_type ret
        | i::args => (e_type i) -> type_of_ar args ret
        end.

      (** a symbol package contains an arity and a value of the corresponding type*)
      Record Sym iTy: Type :=
        mkSym {
            sym_args : list idT;
            sym_value :> type_of_ar sym_args iTy;
          }.

    End Sym.

    (** ** binary operations *)

    Section Bin.
      Record Bin iCat :=
        mkBin {
            (* order: as in fuction composition*)
            bin_value: forall iObj1 iObj2 iObj3, e_type (iCat,iObj2,iObj3)
                                -> e_type (iCat,iObj1,iObj2)
                                -> e_type (iCat,iObj1,iObj3);
            bin_assoc: HAssociative (fun _ _ => eq) (bin_value);
            bin_comm: option (HCommutative (fun _ _ => eq) bin_value)
          }.
    End Bin.
    
    Arguments bin_value : clear implicits.
    Arguments bin_value {iCat} _.

    Variable e_sym: forall iTy, idx -> Sym iTy.
    Variable e_bin: forall iCat, idx -> Bin iCat.

    (** packaging units (depends on e_bin) *)

    Record unit_of iCat (u:forall iObj, e_type (iCat,iObj,iObj)) :=
      mk_unit_for {
          uf_iBin: idx;
          uf_bin := e_bin iCat uf_iBin;
          uf_desc: HUnit (fun _ _ => @eq _) (bin_value uf_bin) u
        }.


    Record unit_pack iCat :=
      mk_unit_pack {
          u_value:> (forall iObj, e_type (iCat,iObj,iObj));
          u_desc: list (unit_of _ u_value)
        }.
    Variable e_unit: forall iCat, idx -> unit_pack iCat.

    Inductive T: idC -> idx -> idx -> Type :=
    | sum {Cat A} (i : idx): mset (T Cat A A) -> T Cat A A
    | prd {Cat A B}: idx -> vAT Cat A B -> T Cat A B
    | sym {Cat A B} (i : idx):
        vT (sym_args (e_sym (Cat,A,B) i)) -> T Cat A B
    | unit {Cat} {A} (j:idx): T Cat A A
    with vT: list idT -> Type :=
         | vnil: vT nil
         | vcons {Cat A B} ar: T Cat A B -> vT ar -> vT ((Cat,A,B)::ar)
    with vAT: idC -> idx -> idx -> Type := (* nonempty vector of arrows whose objects match at the border, for assoc *)
         | vAnil {Cat A B} : T Cat A B -> vAT Cat A B
         | vAcons {Cat A B C} : T Cat B C -> vAT Cat A B -> vAT Cat A C.

    Fixpoint vAapp {Cat A B C} (l: vAT Cat B C) : vAT Cat A B -> vAT Cat A C :=
      match l with
        vAnil x => fun A l' => vAcons x l'
      | vAcons t q => fun A l' => vAcons t (vAapp q l')
      end A.

    Section fold_map_vA.
      Variable F : idC -> idx -> idx -> Type.
      Variable ret : forall Cat A B, T Cat A B -> F Cat A B.
      Variable bind : forall Cat A B C, T Cat B C -> F Cat A B -> F Cat A C.
      Fixpoint fold_map_vA {Cat A B} (l : vAT Cat A B) : F Cat A B :=
        match l with
        | vAnil x => ret x
        | @vAcons Cat A B C u l =>  bind u (fold_map_vA l)
        end.
    End fold_map_vA.
    

    (** lexicographic rpo over the normalised syntax *) (* does implicitly assume that Cat A B = Cat' A' B', but that is not important for us *)
    Fixpoint compare {Cat A B Cat' A' B'} (u: T Cat A B) (v: T Cat' A' B') :=
      match u,v with
      | sum i l, sum j vs => lex (idx_compare i j) (mset_compare compare l vs)
      | prd i l, prd j vs => lex (idx_compare i j) (vAcompare l vs)
      | sym i l, sym j vs => lex (idx_compare i j) (vcompare l vs)
      | unit i , unit j => (idx_compare i j)
      | unit _ , _    => Lt
      | _      , unit _  => Gt
      | sum _ _, _        => Lt
      | _      , sum _ _  => Gt
      | prd _ _, _        => Lt
      | _      , prd _ _  => Gt

      end
    with vcompare {ar1 ar2} (us: vT ar1) (vs: vT ar2) :=
           match us,vs with
           | vnil, vnil => Eq
           | vnil, _  => Lt
           | _,   vnil => Gt
           | vcons  u us, vcons v vs => lex (compare u v) (vcompare us vs)
           end
    with vAcompare {Cat A B Cat' A' B'} (us: vAT Cat A B) (vs: vAT Cat' A' B') :=
           match us,vs with
           | vAnil u, vAnil v => compare u v
           | vAnil _, _  => Lt
           | _,  vAnil _ => Gt
           | @vAcons _ _ C _ u us, @vAcons _ _ C' _ v vs => lex (idx_compare C C') (lex (compare u v) (vAcompare us vs))
           end.

    (** ** Evaluation from syntax to the abstract domain *)

    Fixpoint eval {Cat A B} (u : T Cat A B) : (e_type (Cat,A,B)) :=
      match u with
      | @sum Cat A iBin l => let o := bin_value (e_bin _ iBin) A A A in
                  fold_map (fun un => let '(u,n):=un in @copy _ o n (eval u)) o l
      | prd iBin l => vaeval iBin l
      | @sym Cat A B i v => eval_aux v (sym_value (e_sym (Cat,A,B) i))
      | @unit Cat A i  => u_value (e_unit Cat i) A
      end
    with eval_aux {ar Cat A B} (v: vT ar): type_of_ar ar (Cat,A,B) -> e_type (Cat,A,B) :=
           match v with
           | vnil  => fun f => f
           | vcons x v => fun f => eval_aux v (f (eval x))
           end
    with vaeval {Cat A B} iBin (vs: vAT Cat A B): e_type (Cat,A,B) :=
           match vs with
           | vAnil u => eval u
           | @vAcons Cat _ _ _ u us => bin_value (e_bin Cat iBin) _ _ _ (eval u) (vaeval iBin us)
           end.

    (** we need to show that compare reflects equality (this is because
     we work with msets rather than lists with arities) *)
    Lemma tcompare_weak_spec: forall Cat A B (u v : T Cat A B), compare_weak_spec u v (compare u v)
    with vAtcompare_weak_spec: forall Cat A B (u v : vAT Cat A B), compare_weak_spec u v (vAcompare u v)
    with vcompare_reflect_eqdep: forall ar us ar' vs (H: ar=ar'), vcompare us vs = Eq -> cast vT H us = vs.
    Proof.
      -intros Cat A B [].
       +intros v. refine (match v as v' in T Cat' A' B' return forall H : Cat' A' B' = _,
                   compare_weak_spec _ (cast _ H v') (compare _ v') with
               | sum _ _ => _
               | _ => _
                          end eq_refl). all:intros H;try constructor.
        inversion H;subst. cbn. rewrite cast_eq. 2:trivial. 
        case (pos_compare_weak_spec i p0); intros; try constructor.
        case (mset_compare_weak_spec compare (tcompare_weak_spec _) m m0); intros; try constructor.
       +intros v0. refine (match v0 as v' in T Cat' A' B' return forall H : Cat' A' B' = _,
                   compare_weak_spec _ (cast _ H v') (compare _ v') with
               | sum _ _ => _
               | _ => _
                          end eq_refl). all:intros H;try constructor.
        inversion H;subst. cbn.  
        case (pos_compare_weak_spec p p1); intros; try constructor.
        case (vAtcompare_weak_spec _ v v1);intros;try constructor.  
       +intros v0. refine (match v0 as v' in T Cat' A' B' return forall H : Cat' A' B' = _,
                   compare_weak_spec _ (cast _ H v') (compare _ v') with
               | sum _ _ => _
               | _ => _
                          end eq_refl). all:intros H;try constructor.
        inversion H;subst. cbn.  
        destruct (pos_compare_weak_spec i p0); intros; try constructor.   
        case_eq (vcompare v v1); intro Hv; try constructor.
        rewrite <- (vcompare_reflect_eqdep _ _ _ _ eq_refl Hv). cbn. constructor.
       +intros v0. refine (match v0 as v' in T Cat' A' B' return forall H : Cat' A' B' = _,
                   compare_weak_spec _ (cast _ H v') (compare _ v') with
               | sum _ _ => _
               | _ => _
                          end eq_refl). all:intros H;try constructor.
        inversion H;subst. rewrite cast_eq. 2:trivial. cbn.
        case (pos_compare_weak_spec j p0); intros; try constructor. 
      -intros Cat A B [] v0.
       +destruct v0;intros;try constructor. cbn.
        case (tcompare_weak_spec _ t t0). all:intros;constructor.
       +refine (match v0 as v0 in vAT Cat' A' B' return forall H : Cat' A' B' = _,
                   compare_weak_spec _ (cast (fun Cat A B => vAT Cat A B) H v0) (vAcompare _ v0) with
               | vAnil _ => _
               | _ => _
                          end eq_refl). all:intros H;try constructor. 
        inversion H;subst. cbn. rewrite cast_eq. 2:trivial. revert v1.
        revert dependent B. intros B.
        revert dependent p0. intros p0. case_eq (pos_compare_weak_spec B p0);intros;try constructor. 
        case (tcompare_weak_spec _ t t0);intros;try constructor.
        case (vAtcompare_weak_spec _ v v1);intros;constructor. 
      -induction us; destruct vs; simpl; intros H Huv; try discriminate.
       +apply cast_eq, list_eq_dec, idT_eq_dec.
       +inversion H. subst.
        revert Huv. case (tcompare_weak_spec _ t t0). 2,3:easy.
        intro. intros H'. apply IHus with (H:=eq_refl) in H'. cbn in H'. subst.
        apply cast_eq,list_eq_dec,idT_eq_dec. 
    Qed.
    (*
    Instance eval_aux_compat i (l: vT i): Proper (sym.rel_of X R i ==> R) (eval_aux l).
    Proof.
      induction l; simpl; repeat intro.
      assumption.
      apply IHl, H. reflexivity.
    Qed.
     *)
    
  (* in type Cat, is i a unit for [j] ? *)
  Definition is_unit_of Cat j i :=
    List.existsb (fun p => eq_idx_bool j (uf_iBin p)) (u_desc (e_unit Cat i)).

  (* is [iTY i] commutative ? *)
  Definition is_commutative Cat i :=
    match bin_comm (e_bin Cat i) with Some _ => true | None => false end.


  (** ** Normalisation *)

  Inductive discr {A}: idT -> Type :=
  | Is_op Cat A B (m: A): discr Cat A B
  | Is_unit Cat A: idx -> discr (Cat,(A,A))
  | Is_nothing Cat A B: discr Cat A B.
 
  (* This is called sum in the std lib *)

  (* combine intro rhs *)
  Definition comp A B (merge : B -> B -> B) (l : B) (l' : A + B) : A + B :=
    match l' with
      | inl _ => inr l
      | inr l' => inr (merge l l')
    end.
 
  (** auxiliary functions, to clean up sums  *)

  Section sums.
    Variable i : idx. (* index of binary function to normalise *)
    Variable is_unit : idx -> bool.


    Definition sum' {Cat A} (u : mset (T (Cat,(A,A)))) : T (Cat,(A,A)) :=
      match u with
      | nilne (u,xH) => u
      | _ => sum i u
      end.

    Definition is_sum {Cat A B} (u: T Cat A B) : discr Cat A B :=
    match u in T Cat A B return discr Cat A B with
      | sum Cat A j l => if eq_idx_bool j i then Is_op _ l else Is_nothing _ 
      | unit Cat A j => if is_unit j then Is_unit Cat A j else Is_nothing _
      | u => Is_nothing _
    end.

    Definition copy_mset {Cat A B} n (l: mset (T Cat A B)): mset (T Cat A B) :=
      match n with
        | xH => l
        | _ => nelist_map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l
      end.
   
    Program Definition return_sum {Cat} {i1} u n : idx + mset (T (Cat,(i1,i1))):=
      match is_sum u with
        | Is_nothing _ => inr (nilne (u,n))
        | Is_op _ l' =>  inr (copy_mset n l')
        | Is_unit j => inl j
      end.
   
    Definition add_to_sum {Cat i1} u n (l : idx + (mset (T (Cat,(i1,i1)))))  :=
      match is_sum  u with
        | Is_nothing _ => comp (merge_msets compare) (nilne (u,n)) l
        | Is_op _ l' => comp (merge_msets compare) (copy_mset n l') l
        | Is_unit _ => l
    end.


    Definition norm_msets_ {Cat} {i1} norm (l: mset (T (Cat,(i1,i1)))) : idx + mset (T(Cat,(i1,i1))):=
    fold_map'
    (fun un => let '(u,n) := un in  return_sum  (norm u) n)
    (fun un l => let '(u,n) := un in  add_to_sum  (norm u) n l) l.


  End sums.
 
  (** similar functions for products *)

  Section prds.
    Variable i : idx.
    Variable is_unit : idx -> bool.
    
    Definition prd' {Cat A B} (u: vAT Cat A B): T Cat A B :=
    match u with
      | vAnil u => u
      | vAcons_ _ _ _ as u => prd i u
    end.

    Definition is_prd {Cat A B} (u: T Cat A B) : discr Cat A B :=
    match u in T Cat A B return discr Cat A B with
      | prd Cat A B j l => if eq_idx_bool j i then Is_op _ l else Is_nothing _
      | unit j => if is_unit j  then Is_unit j else Is_nothing _
      | u => Is_nothing _
    end.
 
   
    Program Definition return_prd {Cat} {i1 i2} (u:T (Cat,(i1,i2))) : (idx * (i1=i2)) + vAT (Cat,(i1,i2)):=
      match is_prd u in discr Cat A B return Cat A B = (Cat,(i1,i2)) -> (idx * (i1=i2)) + vAT (Cat,(i1,i2)) with
        | Is_nothing _ => fun H => inr (vAnil (u))
        | Is_op _ l' =>  fun H => inr (l')
        | Is_unit j => fun H => inl (j,_)
      end eq_refl.

    Definition comp' {arr} {i1 i2 i3 : idx} {C D} (merge : arr i2 i3 -> arr i1 i2 -> arr i1 i3) (l : arr i2 i3) (l' : (D * (i1 = i2)) + arr i1 i2) : C + arr i1 i3 :=
      match l' with
      | inl (_,H) => inr (cast (fun i => arr i i3) (eq_sym H) l)
      | inr l' => inr (merge l l')
      end.
   
    Program Definition add_to_prd {Cat A B C} (u: T Cat B C):=
      match is_prd u in @discr _ Cat A B return
            forall (H:Cat A B = Cat B C) A,
              (idx * (A = B)) + (vAT Cat A B) -> (idx * (A = C)) + (vAT Cat A C) with
        | Is_nothing _=> fun H A l => comp' (arr:= fun i1 i2 => vAT (Cat,(i1,i2))) vAapp (vAnil u) l
        | Is_op Cat A B''' l' => fun H A l => comp' (arr:= fun i1 i2 => vAT (Cat,(i1,i2))) vAapp l' l
        | Is_unit _  => fun H A l => (cast (fun i : idx => (_ + vAT (Cat,(A,i)))%type) _ l)
      end eq_refl A.

    
    
    Definition norm_lists_ {Cat i1 i2} (norm: forall Cat A B, T Cat A B -> T Cat A B) (l : vAT (Cat,(i1,i2))) :=
      fold_map_vA (fun Cat A B => match Cat A B with
                             (Cat,(i1,i2))  => _ + _ end)%type
                  (fun Cat' A' B' => match Cat' A' B' with
                             (jCat,(j1,j2)) => 
                             fun (u: T (jCat,(j1,j2))) => return_prd (norm _ u)
                           end)
                  (fun Cat i1 i2 i3 u l => add_to_prd (norm _ u) l) l.


  End prds.


  Definition run_list {Cat} {i1 i2} (x: _ + vAT (Cat,(i1,i2))) :=
    match x with
    | inl (n,H) => vAnil (cast (fun j => T (Cat,(i1,j))) H (unit Cat i1 n))
    | inr l => l
    end.
 
  Definition norm_lists {Cat} {i1 i2} (norm: forall Cat A B, T Cat A B -> T Cat A B ) i (l: vAT (Cat,(i1,i2))) :=
    let is_unit := is_unit_of Cat i in
      run_list (norm_lists_ i is_unit norm l).

(* TODO: does this make sens? *)
  
  Definition run_msets {Cat} {i1} (x : (idx) + _) := match x with
                        | inl (n,H) => nilne (cast (fun i => T (Cat,(i1,i))) H (unit Cat i1 n), xH)
                        | inr l => l
                      end.
 
  Definition norm_msets {Cat} {i1} (norm: T (Cat,(i1,i1)) -> T _) i l :=
    let is_unit := is_unit_of Cat i in
      run_msets (norm_msets_ i is_unit norm l).
 
  Fixpoint norm {Cat A B} (u:T Cat A B) {struct u} : T Cat A B:=
    match u with
      | sum Cat A B i l as u => if is_commutative Cat A B i then sum' i (norm_msets norm i l) else u
      | prd Cat A B i l => prd' i (norm_lists norm i l)
      | sym Cat A B i l => sym Cat A B i (vnorm l)
      | unit Cat A B i as u => u
    end
  with vnorm i (l: vT i): vT i :=
    match l with
      | vnil => vnil
      | vcons _ _ u l => vcons (norm u) (vnorm l)
    end.

  (** ** Correctness *)

  Lemma is_unit_of_Unit  : forall Cat A B (i j : idx),
   is_unit_of Cat A B i j = true -> Unit (@eq (e_type Cat A B)) (bin_value (e_bin Cat A B i)) (eval (unit Cat A B j)).
  Proof.
    intros. unfold is_unit_of in H.
    rewrite existsb_exists in H.
    destruct H as [x [H H']].
    revert H' ; case (eq_idx_spec); [intros H' _ ; subst| intros _ H'; discriminate].
    simpl. destruct x. simpl. auto.
  Qed.
 
  Instance Binvalue_Commutative Cat A B i (H : is_commutative Cat A B i = true) : Commutative eq (bin_value (e_bin Cat A B i) ).
  Proof.
    unfold is_commutative in H.
    destruct bin_comm; auto.
    discriminate.
  Qed.

  Instance Binvalue_Associative Cat A B i :Associative eq (bin_value (e_bin Cat A B i) ).
  Proof.
    destruct e_bin; auto.
  Qed.
 (*
  Instance Binvalue_Proper i : Proper (R ==> R ==> R) (@Bin.value _ _ (e_bin i) ).
  Proof.
    destruct ((e_bin i)); auto.
  Qed.
*)
  Hint Resolve (*Binvalue_Proper*) Binvalue_Associative Binvalue_Commutative.

  (** auxiliary lemmas about sums  *)

  Hint Resolve is_unit_of_Unit.
  Section sum_correctness.
    Variable Cat A B : idT.
    Variable i : idx. (* The binary operator of the sum*)
    Variable is_unit : idx -> bool.
    Hypothesis is_unit_sum_Unit : forall j, is_unit j = true -> @Unit _ eq (bin_value (e_bin Cat A B i)) (eval (unit Cat A B j)).

    Inductive is_sum_spec_ind Cat A B: T Cat A B -> @discr (mset (T Cat A B)) -> Prop :=
    | is_sum_spec_op : forall j l, j = i -> is_sum_spec_ind (sum j l) (Is_op l)
    | is_sum_spec_unit : forall j, is_unit j = true ->  is_sum_spec_ind (unit Cat A B j) (Is_unit j)
    | is_sum_spec_nothing : forall u, is_sum_spec_ind u (Is_nothing).
 
    Lemma is_sum_spec (u:T Cat A B) : is_sum_spec_ind u (is_sum i is_unit u).
    Proof.
      unfold is_sum; destruct u; intros; try constructor.
      -destruct eq_idx_bool eqn:eq1. 2: now constructor.
      revert eq1. case eq_idx_spec; try discriminate. intros. now  constructor.
      -case_eq (is_unit j); intros; try constructor. auto.
    Qed.

    Instance assoc :   @Associative _ eq (bin_value (e_bin Cat A B i)).
    Proof.
      destruct (e_bin Cat A B i). simpl. assumption.
    Qed.
    (*Instance proper :   Proper (R ==> R ==> R) (Bin.value (e_bin i)).
    Proof.
      destruct (e_bin i). simpl. assumption.
    Qed.*)
    Hypothesis comm : @Commutative _ eq (bin_value (e_bin Cat A B i)).

    Lemma sum'_sum : forall  (l: mset (T Cat A B)),  eval (sum' i l) = eval (sum i l) .
    Proof.
      intros [[a n] | [a n] l]; destruct n;  simpl; reflexivity.
    Qed.

    Lemma eval_sum_nil (x:T Cat A B):
      eval (sum i (nilne (x,xH))) = (eval x).
    Proof. rewrite <- sum'_sum. reflexivity.   Qed.
     
    Lemma eval_sum_cons : forall n a (l: mset (T Cat A B)),
      (eval (sum i ((a,n):::l))) = (bin_value (e_bin Cat A B i) (@copy _ (bin_value (e_bin Cat A B i)) n (eval a)) (eval (sum i l))).
    Proof.
      intros n a [[? ? ]|[b m] l]; simpl; reflexivity.
    Qed.
   
    Inductive compat_sum_unit : @m idx (mset (T Cat A B)) -> Prop :=
    | csu_left : forall x,  is_unit x = true->  compat_sum_unit  (left x)
    | csu_right : forall m, compat_sum_unit (right m).

    Lemma compat_sum_unit_return x n : compat_sum_unit  (return_sum i is_unit x n).
    Proof.
      unfold return_sum.
      case is_sum_spec; intros; try constructor; auto.
    Qed.
   
    Lemma compat_sum_unit_add : forall x n h,
        compat_sum_unit  h ->
        compat_sum_unit
          (add_to_sum i (is_unit_of Cat A B i) x n
                      h).
    Proof.
      unfold add_to_sum;intros; inversion H;
        case_eq  (is_sum i (is_unit_of Cat A B i) x);
        intros; simpl; try constructor || eauto. apply H0.
    Qed.

    (* Hint Resolve copy_plus. : this lags because of  the inference of the implicit arguments *)
    Hint Extern 5 (copy (?n + ?m) (eval ?a) = bin_value (copy ?n (eval ?a)) (copy ?m (eval ?a))) => apply copy_plus.
    Hint Extern 5 (?x = ?x) => reflexivity.
    Hint Extern 5 (bin_value ?x ?y = bin_value ?y ?x) => apply bin_comm.
   
    Lemma eval_merge_bin : forall (h k: mset (T Cat A B)),
      eval (sum i (merge_msets compare h k)) = bin_value (e_bin Cat A B i) (eval (sum i h)) (eval (sum i k)).
    Proof.
      induction h as [[a n]|[a n] h IHh]; intro k.
      -simpl.
       induction k as [[b m]|[b m] k IHk]; simpl.
       +destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl; auto. apply copy_plus; auto.  all: exact _. 
     
       +destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl; auto.
        rewrite copy_plus,law_assoc; auto. now cbv;congruence. 
        rewrite IHk;  clear IHk. rewrite 2 law_assoc. f_equal. apply law_comm.
        
      -induction k as [[b m]|[b m] k IHk]; simpl;  simpl in IHh.
      +destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl.
       *rewrite  (law_comm _ (copy m (eval a))), law_assoc, <- copy_plus,  Pplus_comm; auto. now cbv;congruence. 
       *rewrite <- law_assoc, IHh.  reflexivity.
       *rewrite law_comm. reflexivity.
      +simpl in IHk.
       destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl.
       *rewrite IHh; clear IHh. rewrite 2 law_assoc. rewrite (law_comm _ (copy m (eval a))). rewrite law_assoc, <- copy_plus,  Pplus_comm; auto. cbv;congruence. 
       *rewrite IHh; clear IHh. simpl.  rewrite law_assoc. reflexivity. 
       *rewrite 2 (law_comm  (copy m (eval b))). rewrite law_assoc.  
       rewrite <- IHk. reflexivity.
    Qed.

 
    Lemma copy_mset' n (l: mset (T Cat A B)):  copy_mset n l = nelist_map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l.
    Proof.
      unfold copy_mset.  destruct n; try reflexivity.
     
      simpl. induction l as [|[a l] IHl]; simpl; try congruence.  destruct a.  reflexivity.
    Qed.
   
   
    Lemma copy_mset_succ  n (l: mset (T Cat A B)):  eval (sum i (copy_mset (Pos.succ n) l)) = bin_value (e_bin Cat A B i) (eval (sum i l)) (eval (sum i (copy_mset n l))).
    Proof.
      rewrite 2 copy_mset'.
     
      induction l as [[a m]|[a m] l IHl].
      -simpl eval.   rewrite <- copy_plus; auto. rewrite Pmult_Sn_m. reflexivity. cbv. congruence. 
      -simpl nelist_map.  rewrite ! eval_sum_cons. rewrite IHl.  clear IHl.
       rewrite Pmult_Sn_m. rewrite copy_plus; auto. rewrite <- !law_assoc. 2:now cbv;congruence.
       f_equal. 
       rewrite law_comm . rewrite <- !law_assoc. f_equal. apply law_comm.
    Qed.

    Lemma copy_mset_copy : forall n  (m : mset (T Cat A B)), eval (sum i (copy_mset n m)) = @copy _ (bin_value (e_bin Cat A B i)) n (eval (sum i m)).
    Proof.
      induction n using Pind; intros.
     
      unfold copy_mset. rewrite copy_xH. reflexivity.
      rewrite copy_mset_succ. rewrite copy_Psucc. rewrite IHn. reflexivity.
    Qed.
   
    Instance compat_sum_unit_Unit : forall p, compat_sum_unit (left p) ->
      @Unit _ eq (bin_value (e_bin Cat A B i)) (eval (unit Cat A B p)).
    Proof.
      intros.
      inversion H. subst.  auto.
    Qed.
  
    Lemma copy_n_unit : forall j n, is_unit j = true ->
      eval (unit Cat A B j) = @copy _ (bin_value (e_bin Cat A B i)) n (eval (unit Cat A B j)).
    Proof.
      intros.
      induction n using Prect.
      rewrite copy_xH. reflexivity.
      rewrite copy_Psucc. rewrite <- IHn. apply is_unit_sum_Unit in H. rewrite law_neutral_left. reflexivity.
    Qed.

   
    Lemma z0  l r (H : compat_sum_unit  r):
      eval (sum i (run_msets (comp (merge_msets compare) l r))) = eval (sum i ((merge_msets compare) (l) (run_msets r))).
    Proof.
      unfold comp. unfold run_msets.
      case_eq r; intros; subst.
      rewrite eval_merge_bin; auto.
      rewrite eval_sum_nil.
      apply compat_sum_unit_Unit in H. rewrite law_neutral_right.  reflexivity.
      reflexivity.
    Qed.

    Lemma z1 : forall n x,
      eval (sum i (run_msets (return_sum i (is_unit) x n )))
      = @copy _ (bin_value (e_bin Cat A B i)) n (eval x).
    Proof.
      intros. unfold return_sum.  unfold run_msets.
      destruct (is_sum_spec x); intros; subst.
      -rewrite copy_mset_copy.
       reflexivity.
      -rewrite eval_sum_nil. apply copy_n_unit. auto.
      -reflexivity.
    Qed.
    Lemma z2 : forall  u n x, compat_sum_unit  x ->
      eval (sum i ( run_msets
        (add_to_sum i (is_unit) u n x)))
      = 
      bin_value (e_bin Cat A B i) (@copy _ (bin_value (e_bin Cat A B i))  n (eval u)) (eval (sum i (run_msets x))).
    Proof.
      intros u n x Hix .
      unfold add_to_sum.
      case is_sum_spec; intros; subst.
   
      rewrite z0 by auto.  rewrite eval_merge_bin.  rewrite copy_mset_copy. reflexivity.
      rewrite <- copy_n_unit by assumption.
      apply is_unit_sum_Unit in H.
      rewrite law_neutral_left. reflexivity.
     
     
      rewrite z0 by auto.  rewrite eval_merge_bin. reflexivity.
    Qed.
  End sum_correctness.
  
  Lemma eval_norm_msets Cat A B i norm
    (Comm : Commutative eq (bin_value (e_bin Cat A B i)))
    (Hnorm: forall (u : T Cat A B), eval (norm u) = eval u) : forall h, eval (sum i (norm_msets norm i h)) = eval (sum i h).
  Proof.
    unfold norm_msets.
    assert (H :
      forall h : mset (T Cat A B),
        eval (sum i (run_msets (norm_msets_ i (is_unit_of Cat A B i) norm h))) =  eval (sum i h) /\ compat_sum_unit (is_unit_of Cat A B i) (norm_msets_ i (is_unit_of Cat A B i) norm h)).
      
    -induction h as [[a n] | [a n] h [IHh IHh']]; simpl norm_msets_; split.
     +rewrite z1 by auto.  rewrite Hnorm . reflexivity.
     +apply compat_sum_unit_return. auto.      
     +rewrite z2 by auto. rewrite IHh. 
      rewrite eval_sum_cons.  rewrite Hnorm. reflexivity.
     +apply compat_sum_unit_add, IHh'.
     -apply H.
  Defined.
 
  (** auxiliary lemmas about products  *)

  Section prd_correctness.
    Variable Cat A B : idT. 
    Variable i : idx.
    Variable is_unit : idx -> bool.
    Hypothesis is_unit_prd_Unit : forall j, is_unit j = true->  @Unit _ eq (bin_value (e_bin Cat A B i)) (eval (unit Cat A B j)).

    Inductive is_prd_spec_ind Cat A B : T Cat A B ->  @discr (nelist (T Cat A B)) -> Prop :=
    | is_prd_spec_op :
      forall j l, j = i -> is_prd_spec_ind (prd j l) (Is_op l)
    | is_prd_spec_unit :
      forall j, is_unit j = true ->  is_prd_spec_ind (unit Cat A B j) (Is_unit j)
    | is_prd_spec_nothing :
      forall u, is_prd_spec_ind u (Is_nothing).
   
    Lemma is_prd_spec (u : T Cat A B ) : is_prd_spec_ind u (is_prd i is_unit u).
    Proof.
      unfold is_prd; destruct u; intros; try constructor.
      -case (eq_idx_spec); intros; subst;  try constructor; auto.
      -case_eq (is_unit j); intros; try constructor; auto.
    Qed.

    Lemma prd'_prd : forall (l: nelist (T Cat A B)), eval (prd' i l) = eval (prd i l).
    Proof.
      intros  [?|? [|? ?]]; simpl; reflexivity.
    Qed.
   
   
    Lemma eval_prd_nil (x: T Cat A B):  eval (prd i (nilne x)) = eval x.
    Proof.
      rewrite <- prd'_prd. simpl. reflexivity.
    Qed.
    Lemma eval_prd_cons a : forall (l: nelist (T Cat A B)), eval (prd i (a:::l)) = bin_value (e_bin Cat A B i) (eval a) (eval (prd i l)).
    Proof.
      intros  [|b l]; simpl; reflexivity.
    Qed.
    Lemma eval_prd_app : forall (h k: nelist (T Cat A B)), eval (prd i (appne h k)) = bin_value (e_bin Cat A B i) (eval (prd i h)) (eval (prd i k)).
    Proof.
      induction h; intro k. simpl; try reflexivity.
      simpl appne.  rewrite  2 eval_prd_cons, IHh, law_assoc. reflexivity.
    Qed.

    Inductive compat_prd_unit : @m idx (nelist (T Cat A B)) -> Prop :=
    | cpu_left : forall x,  is_unit  x = true -> compat_prd_unit  (left x)
    | cpu_right : forall m, compat_prd_unit (right m)
    .
 
    Lemma compat_prd_unit_return  x: compat_prd_unit (return_prd i is_unit x).
    Proof.
      unfold return_prd.
      case (is_prd_spec); intros; try constructor; auto.
    Qed.

    Lemma compat_prd_unit_add  : forall x  h,
      compat_prd_unit  h
      ->
      compat_prd_unit
      (add_to_prd i is_unit x
        h).
    Proof.
      intros.
      unfold add_to_prd.
      unfold comp.
      case (is_prd_spec); intros; try constructor; auto.
      unfold comp; case h; try constructor.
      unfold comp; case h; try constructor.
    Qed.

   
    Instance compat_prd_Unit : forall p, compat_prd_unit (left p) ->
      @Unit _ eq (bin_value (e_bin Cat A B i)) (eval (unit Cat A B p)).
    Proof.
      intros.
      inversion H; subst. apply is_unit_prd_Unit. assumption.
    Qed.

    Lemma z0' : forall l (r: @m idx (nelist (T Cat A B))), compat_prd_unit r ->
      eval (prd i (run_list (comp (@appne _) l r))) = eval (prd i ((appne (l) (run_list r)))).
    Proof.
      intros.
      unfold comp. unfold run_list. case_eq r; intros; auto; subst.
      rewrite eval_prd_app.
      rewrite eval_prd_nil.
      apply compat_prd_Unit in H. rewrite law_neutral_right. reflexivity.
    Qed.
 
    Lemma z1' (a:T Cat A B) :  eval (prd i (run_list (return_prd i is_unit a))) =  eval (prd i (nilne a)).
    Proof.
      intros. unfold return_prd.  unfold run_list.
      case (is_prd_spec); intros; subst; reflexivity.
    Qed.
    Lemma z2' : forall  u  x, compat_prd_unit  x ->
      eval (prd i ( run_list
        (add_to_prd i is_unit u x))) =  bin_value (e_bin Cat A B i) (eval u) (eval (prd i (run_list x))).
    Proof.
      intros u x Hix.
      unfold add_to_prd.
      case (is_prd_spec); intros; subst.
      rewrite z0' by auto.  rewrite eval_prd_app.  reflexivity.
      apply is_unit_prd_Unit in H. rewrite law_neutral_left. reflexivity.
      rewrite z0' by auto.  rewrite eval_prd_app. reflexivity.
    Qed.
 
  End prd_correctness.




  Lemma eval_norm_lists Cat A B i (Hnorm: forall (u : T Cat A B), eval (norm u) = eval u) : forall h : (nelist (T Cat A B)), eval (prd i (norm_lists norm i h)) = eval (prd i h).
  Proof.
    unfold norm_lists.
    assert (H :  forall h : nelist (T Cat A B),
      eval (prd i (run_list (norm_lists_ i (is_unit_of Cat A B i) norm h))) =
      eval (prd i h)
      /\ compat_prd_unit (is_unit_of Cat A B i) (norm_lists_ i (is_unit_of Cat A B i) norm h)).
    {
      induction h as [a | a h [IHh IHh']]; simpl norm_lists_; split.
      -rewrite z1'. 2:now eauto. simpl.  apply Hnorm.
      -apply compat_prd_unit_return. now eauto. 
      -rewrite z2'. 2,3:now eauto. rewrite IHh.  rewrite eval_prd_cons.  rewrite Hnorm. reflexivity.
      -apply compat_prd_unit_add. all:auto.
    }
    apply H.
    Defined.

  (** correctness of the normalisation function *)

  Theorem eval_norm: forall Cat A B (u: T Cat A B), eval (norm u) = eval u
    with eval_norm_aux: forall arTy ret (l: vT arTy) (f: type_of_ar arTy ret),
      eval_aux (vnorm l) f = eval_aux l f.
  Proof.
    induction u as [ Cat A B p m | iTY p l | Cat A B ? | Cat A B ?];  cbn [norm].
    -case_eq (is_commutative Cat A B p); intros.
     +rewrite sum'_sum.
      apply eval_norm_msets; auto.
     +reflexivity.
    -rewrite prd'_prd.
    apply eval_norm_lists; auto.
    -apply eval_norm_aux.
    -reflexivity.
    -induction l; cbn; intros f.
     +reflexivity.
     +rewrite eval_norm. apply IHl; reflexivity.
  Qed.


  (** corollaries, for goal normalisation or decision *)

  Lemma normalise : forall Cat A B (u v: T Cat A B), eval (norm u) = eval (norm v) -> eval u = eval v.
  Proof. intros ? u v. rewrite 2 eval_norm. trivial. Qed.
   
  Lemma compare_reflect_eq Cat A B (u v : T Cat A B) : compare u v = Eq -> eval u = eval v.
  Proof. case (tcompare_weak_spec u v); intros; try congruence. Qed.

  Lemma decide Cat A B (u v: T Cat A B): compare (norm u) (norm v) = Eq -> eval u = eval v.
  Proof. intros H. apply normalise. apply compare_reflect_eq. apply H. Qed.

  (* Lemma lift_normalise {S} {H : AAC_lift S R}: *)
  (*   forall (u v: T), (let x := norm u in let y := norm v in *)
  (*     S (eval x) (eval y)) -> S (eval u) (eval v). *)
  (* Proof. destruct H. intros u v; simpl; rewrite 2 eval_norm. trivial. Qed. *)


  End ReifH.
End ReifH.
