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
Require Import BinPos.
Require Export Interface.
Require Import List.
Require Import PeanoNat. 
Import List.ListNotations.
Local Open Scope list_scope.


Set Implicit Arguments.
Set Asymmetric Patterns.


Module ReifH.
  Section ReifH.
    (* We use environments to store the various operators and the
     morphisms.*)

    Local Notation idT := nat.
    Variable l_type : nelist Type.

    Fixpoint nthne X n (l:nelist X) {struct l}: X :=
      match l,n with
        nilne x,_ => x
      | consne x _,0 => x
      | consne _ l,S n => nthne n l
      end. 
    
    Let e_type := (fun i => nthne i l_type).

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
      Record Bin iTy :=
        mkBin {
            bin_value: e_type iTy -> e_type iTy -> e_type iTy;
            bin_assoc: Associative eq bin_value;
            bin_comm: option (Commutative eq bin_value)
          }.
    End Bin.
    
    Arguments bin_value : clear implicits.
    Arguments bin_value {iTy} _.

    Variable e_sym: forall iTy, idx -> Sym iTy.
    Variable e_bin: forall iTy, idx -> Bin iTy.

    (** packaging units (depends on e_bin) *)

    Record unit_of iTy (u:e_type iTy) :=
      mk_unit_for {
          uf_iBin: idx;
          uf_bin := e_bin iTy uf_iBin;
          uf_desc: Unit (@eq _) (bin_value uf_bin) u
        }.


    Record unit_pack iTy :=
      mk_unit_pack {
          u_value:> e_type iTy;
          u_desc: list (unit_of _ u_value)
        }.
    Variable e_unit: forall iTy, idx -> unit_pack iTy.

    Inductive T: idT -> Type :=
    | sum iTy (i : idx): mset (T iTy) -> T iTy
    (*| prd: idx -> nelist T -> T*)
    | sym iTy (i : idx):
             vT (sym_args (e_sym iTy i)) -> T iTy
    | unit iTy (j:idx): T iTy
    with vT: list idT -> Type :=
         | vnil: vT nil
         | vcons X ar: T X -> vT ar -> vT (X::ar).

    (** lexicographic rpo over the normalised syntax *)
    Fixpoint compare {iTy jTy} (u: T iTy) (v: T jTy) :=
      match u,v with
      | sum iTy i l, sum _ j vs => lex (idx_compare i j) (mset_compare compare l vs)
      (*| prd i l, prd j vs => lex (idx_compare i j) (list_compare compare l vs)*)
      | sym iTy i l, sym jTy j vs => lex (idx_compare i j) (vcompare l vs)
      | unit _ i , unit _ j => (idx_compare i j)
      | unit _ _ , _        => Lt
      | _      , unit _ _  => Gt
      | sum _ _ _, _        => Lt
      | _      , sum _ _ _  => Gt
      (*| prd _ _, _        => Lt
      | _      , prd _ _  => Gt*)

      end
    with vcompare {ar1 ar2} (us: vT ar1) (vs: vT ar2) :=
           match us,vs with
           | vnil, vnil => Eq
           | vnil, _  => Lt
           | _,   vnil => Gt
           | vcons _ _ u us, vcons _ _ v vs => lex (compare u v) (vcompare us vs)
           end.

    (** ** Evaluation from syntax to the abstract domain *)

    Fixpoint eval {iTy} (u : T iTy) : (e_type iTy) :=
      match u with
      | sum iTy i l => let o := bin_value (e_bin iTy i) in
                  fold_map (fun un => let '(u,n):=un in @copy _ o n (eval u)) o l
      (*| prd i l => fold_map eval (Bin.value (e_bin i)) l*)
      | sym iTy i v => eval_aux v (sym_value (e_sym iTy i))
      | unit iTy i  => e_unit iTy i
      end
    with eval_aux {ar iTy} (v: vT ar): type_of_ar ar iTy -> e_type iTy :=
           match v with
           | vnil  => fun f => f
           | vcons X ar x v => fun f => eval_aux v (f (eval x))
           end.


    (** we need to show that compare reflects equality (this is because
     we work with msets rather than lists with arities) *)
    Lemma tcompare_weak_spec: forall iTy (u v : T iTy), compare_weak_spec u v (compare u v)
    with vcompare_reflect_eqdep: forall ar us ar' vs (H: ar=ar'), vcompare us vs = Eq -> cast vT H us = vs.
    Proof.
      -destruct u. 
       +destruct v; simpl; try constructor.
        case (pos_compare_weak_spec i i0); intros; try constructor.
        case (mset_compare_weak_spec compare (tcompare_weak_spec iTy) m m0); intros; try constructor.
       +intros u. destruct u. 1,3:now constructor. cbn.
        destruct (pos_compare_weak_spec i i0); intros; try constructor.   
        case_eq (vcompare v v0); intro Hv; try constructor.
        rewrite <- (vcompare_reflect_eqdep _ _ _ _ eq_refl Hv). cbn. constructor.
       +intros []. 1,2:now constructor. cbn.
        case (pos_compare_weak_spec j j0); intros; try constructor. 
      -induction us; destruct vs; simpl; intros H Huv; try discriminate.
       +apply cast_eq, list_eq_dec, Nat.eq_dec.
       +inversion H. subst.
        revert Huv. case (tcompare_weak_spec _ t t0). 2,3:easy.
        intro. intros H'. apply IHus with (H:=eq_refl) in H'. cbn in H'. subst.
        apply cast_eq,list_eq_dec,Nat.eq_dec. 
    Qed.
    (*
    Instance eval_aux_compat i (l: vT i): Proper (sym.rel_of X R i ==> R) (eval_aux l).
    Proof.
      induction l; simpl; repeat intro.
      assumption.
      apply IHl, H. reflexivity.
    Qed.
     *)
    
  (* in type iTy, is i a unit for [j] ? *)
  Definition is_unit_of iTy j i :=
    List.existsb (fun p => eq_idx_bool j (uf_iBin p)) (u_desc (e_unit iTy i)).

  (* is [iTY i] commutative ? *)
  Definition is_commutative iTy i :=
    match bin_comm (e_bin iTy i) with Some _ => true | None => false end.


  (** ** Normalisation *)

  Inductive discr {A} : Type :=
  | Is_op : A -> discr
  | Is_unit : idx -> discr
  | Is_nothing : discr .
 
  (* This is called sum in the std lib *)
  Inductive m {A} {B} :=
  | left : A -> m
  | right : B -> m.

  (* combine intro rhs *)
  Definition comp A B (merge : B -> B -> B) (l : B) (l' : @m A B) : @m A B :=
    match l' with
      | left _ => right l
      | right l' => right (merge l l')
    end.
 
  (** auxiliary functions, to clean up sums  *)

  Section sums.
    Variable iTy : idT. (* index of the Type to look at *)
    Variable i : idx. (* index of binary function to normalise *)
    Variable is_unit : idx -> bool.


    Definition sum' (u: mset (T iTy)): T iTy :=
      match u with
        | nilne (u,xH) => u
        | _ => sum i u
      end.

    Definition is_sum  (u: T iTy) : @discr (mset (T iTy)) :=
    match u with
      | sum iTy j l => if eq_idx_bool j i then Is_op l else Is_nothing
      | unit iTy j => if is_unit j   then Is_unit j else Is_nothing
      | u => Is_nothing
    end.

    Definition copy_mset n (l: mset (T iTy)): mset (T iTy) :=
      match n with
        | xH => l
        | _ => nelist_map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l
      end.
   
    Definition return_sum  u n :=
      match is_sum  u with
        | Is_nothing => right (nilne (u,n))
        | Is_op l' =>  right (copy_mset n l')
        | Is_unit j => left j
      end.
   
    Definition add_to_sum u n (l : @m idx (mset (T iTy)))  :=
      match is_sum  u with
        | Is_nothing => comp (merge_msets compare) (nilne (u,n)) l
        | Is_op l' => comp (merge_msets compare) (copy_mset n l') l
        | Is_unit _ => l
    end.


    Definition norm_msets_ norm  (l: mset (T iTy)) :=
    fold_map'
    (fun un => let '(u,n) := un in  return_sum  (norm u) n)
    (fun un l => let '(u,n) := un in  add_to_sum  (norm u) n l) l.


  End sums.
 
  (** similar functions for products *)

  (* Section prds. *)

  (*   Variable i : idx. *)
  (*   Variable is_unit : idx -> bool. *)
  (*   Definition prd'  (u: nelist T): T := *)
  (*   match u with *)
  (*     | nil u => u *)
  (*     | _ => prd i u *)
  (*   end. *)

  (*   Definition is_prd (u: T) : @discr (nelist T) := *)
  (*   match u with *)
  (*     | prd j l => if eq_idx_bool j i then Is_op l else Is_nothing *)
  (*     | unit j => if is_unit j  then Is_unit j else Is_nothing *)
  (*     | u => Is_nothing *)
  (*   end. *)
 
   
  (*   Definition return_prd u := *)
  (*     match is_prd u with *)
  (*       | Is_nothing => right (nil (u)) *)
  (*       | Is_op l' =>  right (l') *)
  (*       | Is_unit j => left j *)
  (*     end. *)
   
  (*   Definition add_to_prd  u  (l : @m idx (nelist T))  := *)
  (*     match is_prd  u with *)
  (*       | Is_nothing => comp (@appne T) (nil (u)) l *)
  (*       | Is_op l' => comp (@appne T) (l') l *)
  (*       | Is_unit _ => l *)
  (*     end. *)

  (*   Definition norm_lists_ norm (l : nelist T) := *)
  (*   fold_map' *)
  (*   (fun u => return_prd  (norm u)) *)
  (*   (fun u l => add_to_prd (norm u) l) l. *)


  (* End prds. *)


  (* Definition run_list x := match x with *)
  (*                       | left n => nil (unit n) *)
  (*                       | right l => l *)
  (*                     end. *)
 
  (* Definition norm_lists norm i l := *)
  (*   let is_unit := is_unit_of i in *)
  (*     run_list (norm_lists_ i is_unit norm l). *)

  Definition run_msets {iTy} x := match x with
                        | left n => nilne (unit iTy n, xH)
                        | right l => l
                      end.
 
  Definition norm_msets {iTy} (norm: T iTy -> T iTy) i l :=
    let is_unit := is_unit_of iTy i in
      run_msets (norm_msets_ i is_unit norm l).
 
  Fixpoint norm {iTy} (u:T iTy) {struct u} : T iTy:=
    match u with
      | sum iTy i l as u => if is_commutative iTy i then sum' i (norm_msets norm i l) else u
      (* | prd i l => prd' i (norm_lists norm i l) *)
      | sym iTy i l => sym iTy i (vnorm l)
      | unit iTy i as u => u
    end
  with vnorm i (l: vT i): vT i :=
    match l with
      | vnil => vnil
      | vcons _ _ u l => vcons (norm u) (vnorm l)
    end.

  (** ** Correctness *)

  Lemma is_unit_of_Unit  : forall iTy (i j : idx),
   is_unit_of iTy i j = true -> Unit (@eq (e_type iTy)) (bin_value (e_bin iTy i)) (eval (unit iTy j)).
  Proof.
    intros. unfold is_unit_of in H.
    rewrite existsb_exists in H.
    destruct H as [x [H H']].
    revert H' ; case (eq_idx_spec); [intros H' _ ; subst| intros _ H'; discriminate].
    simpl. destruct x. simpl. auto.
  Qed.
 
  Instance Binvalue_Commutative iTy i (H : is_commutative iTy i = true) : Commutative eq (bin_value (e_bin iTy i) ).
  Proof.
    unfold is_commutative in H.
    destruct bin_comm; auto.
    discriminate.
  Qed.

  Instance Binvalue_Associative iTy i :Associative eq (bin_value (e_bin iTy i) ).
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
    Variable iTy : idT.
    Variable i : idx. (* The binary operator of the sum*)
    Variable is_unit : idx -> bool.
    Hypothesis is_unit_sum_Unit : forall j, is_unit j = true -> @Unit _ eq (bin_value (e_bin iTy i)) (eval (unit iTy j)).

    Inductive is_sum_spec_ind iTy: T iTy -> @discr (mset (T iTy)) -> Prop :=
    | is_sum_spec_op : forall j l, j = i -> is_sum_spec_ind (sum j l) (Is_op l)
    | is_sum_spec_unit : forall j, is_unit j = true ->  is_sum_spec_ind (unit iTy j) (Is_unit j)
    | is_sum_spec_nothing : forall u, is_sum_spec_ind u (Is_nothing).
 
    Lemma is_sum_spec (u:T iTy) : is_sum_spec_ind u (is_sum i is_unit u).
    Proof.
      unfold is_sum; destruct u; intros; try constructor.
      -destruct eq_idx_bool eqn:eq1. 2: now constructor.
      revert eq1. case eq_idx_spec; try discriminate. intros. now  constructor.
      -case_eq (is_unit j); intros; try constructor. auto.
    Qed.

    Instance assoc :   @Associative _ eq (bin_value (e_bin iTy i)).
    Proof.
      destruct (e_bin iTy i). simpl. assumption.
    Qed.
    (*Instance proper :   Proper (R ==> R ==> R) (Bin.value (e_bin i)).
    Proof.
      destruct (e_bin i). simpl. assumption.
    Qed.*)
    Hypothesis comm : @Commutative _ eq (bin_value (e_bin iTy i)).

    Lemma sum'_sum : forall  (l: mset (T iTy)),  eval (sum' i l) = eval (sum i l) .
    Proof.
      intros [[a n] | [a n] l]; destruct n;  simpl; reflexivity.
    Qed.

    Lemma eval_sum_nil (x:T iTy):
      eval (sum i (nilne (x,xH))) = (eval x).
    Proof. rewrite <- sum'_sum. reflexivity.   Qed.
     
    Lemma eval_sum_cons : forall n a (l: mset (T iTy)),
      (eval (sum i ((a,n):::l))) = (bin_value (e_bin iTy i) (@copy _ (bin_value (e_bin iTy i)) n (eval a)) (eval (sum i l))).
    Proof.
      intros n a [[? ? ]|[b m] l]; simpl; reflexivity.
    Qed.
   
    Inductive compat_sum_unit : @m idx (mset (T iTy)) -> Prop :=
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
          (add_to_sum i (is_unit_of iTy i) x n
                      h).
    Proof.
      unfold add_to_sum;intros; inversion H;
        case_eq  (is_sum i (is_unit_of iTy i) x);
        intros; simpl; try constructor || eauto. apply H0.
    Qed.

    (* Hint Resolve copy_plus. : this lags because of  the inference of the implicit arguments *)
    Hint Extern 5 (copy (?n + ?m) (eval ?a) = bin_value (copy ?n (eval ?a)) (copy ?m (eval ?a))) => apply copy_plus.
    Hint Extern 5 (?x = ?x) => reflexivity.
    Hint Extern 5 (bin_value ?x ?y = bin_value ?y ?x) => apply bin_comm.
   
    Lemma eval_merge_bin : forall (h k: mset (T iTy)),
      eval (sum i (merge_msets compare h k)) = bin_value (e_bin iTy i) (eval (sum i h)) (eval (sum i k)).
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

 
    Lemma copy_mset' n (l: mset (T iTy)):  copy_mset n l = nelist_map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l.
    Proof.
      unfold copy_mset.  destruct n; try reflexivity.
     
      simpl. induction l as [|[a l] IHl]; simpl; try congruence.  destruct a.  reflexivity.
    Qed.
   
   
    Lemma copy_mset_succ  n (l: mset (T iTy)):  eval (sum i (copy_mset (Pos.succ n) l)) = bin_value (e_bin iTy i) (eval (sum i l)) (eval (sum i (copy_mset n l))).
    Proof.
      rewrite 2 copy_mset'.
     
      induction l as [[a m]|[a m] l IHl].
      -simpl eval.   rewrite <- copy_plus; auto. rewrite Pmult_Sn_m. reflexivity. cbv. congruence. 
      -simpl nelist_map.  rewrite ! eval_sum_cons. rewrite IHl.  clear IHl.
       rewrite Pmult_Sn_m. rewrite copy_plus; auto. rewrite <- !law_assoc. 2:now cbv;congruence.
       f_equal. 
       rewrite law_comm . rewrite <- !law_assoc. f_equal. apply law_comm.
    Qed.

    Lemma copy_mset_copy : forall n  (m : mset (T iTy)), eval (sum i (copy_mset n m)) = @copy _ (bin_value (e_bin iTy i)) n (eval (sum i m)).
    Proof.
      induction n using Pind; intros.
     
      unfold copy_mset. rewrite copy_xH. reflexivity.
      rewrite copy_mset_succ. rewrite copy_Psucc. rewrite IHn. reflexivity.
    Qed.
   
    Instance compat_sum_unit_Unit : forall p, compat_sum_unit (left p) ->
      @Unit _ eq (bin_value (e_bin iTy i)) (eval (unit iTy p)).
    Proof.
      intros.
      inversion H. subst.  auto.
    Qed.
  
    Lemma copy_n_unit : forall j n, is_unit j = true ->
      eval (unit iTy j) = @copy _ (bin_value (e_bin iTy i)) n (eval (unit iTy j)).
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
      = @copy _ (bin_value (e_bin iTy i)) n (eval x).
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
      bin_value (e_bin iTy i) (@copy _ (bin_value (e_bin iTy i))  n (eval u)) (eval (sum i (run_msets x))).
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
  
  Lemma eval_norm_msets iTy i norm
    (Comm : Commutative eq (bin_value (e_bin iTy i)))
    (Hnorm: forall (u : T iTy), eval (norm u) = eval u) : forall h, eval (sum i (norm_msets norm i h)) = eval (sum i h).
  Proof.
    unfold norm_msets.
    assert (H :
      forall h : mset (T iTy),
        eval (sum i (run_msets (norm_msets_ i (is_unit_of iTy i) norm h))) =  eval (sum i h) /\ compat_sum_unit (is_unit_of iTy i) (norm_msets_ i (is_unit_of iTy i) norm h)).
      
    -induction h as [[a n] | [a n] h [IHh IHh']]; simpl norm_msets_; split.
     +rewrite z1 by auto.  rewrite Hnorm . reflexivity.
     +apply compat_sum_unit_return. auto.      
     +rewrite z2 by auto. rewrite IHh. 
      rewrite eval_sum_cons.  rewrite Hnorm. reflexivity.
     +apply compat_sum_unit_add, IHh'.
     -apply H.
  Defined.
 
  (** auxiliary lemmas about products  *)

  (* Section prd_correctness. *)
  (*   Variable iTy i : idx. *)
  (*   Variable is_unit : idx -> bool. *)
  (*   Hypothesis is_unit_prd_Unit : forall j, is_unit j = true->  @Unit _ eq (bin_value (e_bin iTy i)) (eval (unit j)). *)

  (*   Inductive is_prd_spec_ind  : T ->  @discr (nelist T) -> Prop := *)
  (*   | is_prd_spec_op : *)
  (*     forall j l, j = i -> is_prd_spec_ind (prd j l) (Is_op l) *)
  (*   | is_prd_spec_unit : *)
  (*     forall j, is_unit j = true ->  is_prd_spec_ind (unit j) (Is_unit j) *)
  (*   | is_prd_spec_nothing : *)
  (*     forall u, is_prd_spec_ind u (Is_nothing). *)
   
  (*   Lemma is_prd_spec u : is_prd_spec_ind u (is_prd i is_unit u). *)
  (*   Proof. *)
  (*     unfold is_prd; case u; intros; try constructor. *)
  (*     case (eq_idx_spec); intros; subst;  try constructor; auto. *)
  (*     case_eq (is_unit p); intros; try constructor; auto.   *)
  (*   Qed. *)

  (*   Lemma prd'_prd : forall (l: nelist T), eval (prd' i l) == eval (prd i l). *)
  (*   Proof. *)
  (*     intros  [?|? [|? ?]]; simpl; reflexivity. *)
  (*   Qed. *)
   
   
  (*   Lemma eval_prd_nil x:  eval (prd i (nil x)) == eval x.  *)
  (*   Proof. *)
  (*     rewrite <- prd'_prd. simpl. reflexivity. *)
  (*   Qed. *)
  (*   Lemma eval_prd_cons a : forall (l: nelist T), eval (prd i (a::l)) == @Bin.value _ _ (e_bin i) (eval a) (eval (prd i l)). *)
  (*   Proof. *)
  (*     intros  [|b l]; simpl; reflexivity. *)
  (*   Qed.        *)
  (*   Lemma eval_prd_app : forall (h k: nelist T), eval (prd i (h++k)) == @Bin.value _ _ (e_bin i) (eval (prd i h)) (eval (prd i k)). *)
  (*   Proof. *)
  (*     induction h; intro k. simpl; try reflexivity. *)
  (*     simpl appne.  rewrite  2 eval_prd_cons, IHh, law_assoc. reflexivity. *)
  (*   Qed.        *)

  (*   Inductive compat_prd_unit : @m idx (nelist T) -> Prop := *)
  (*   | cpu_left : forall x,  is_unit  x = true -> compat_prd_unit  (left x) *)
  (*   | cpu_right : forall m, compat_prd_unit (right m) *)
  (*   . *)
 
  (*   Lemma compat_prd_unit_return  x: compat_prd_unit (return_prd i is_unit x). *)
  (*   Proof. *)
  (*     unfold return_prd. *)
  (*     case (is_prd_spec); intros; try constructor; auto. *)
  (*   Qed. *)

  (*   Lemma compat_prd_unit_add  : forall x  h, *)
  (*     compat_prd_unit  h *)
  (*     -> *)
  (*     compat_prd_unit *)
  (*     (add_to_prd i is_unit x *)
  (*       h). *)
  (*   Proof. *)
  (*     intros. *)
  (*     unfold add_to_prd. *)
  (*     unfold comp. *)
  (*     case (is_prd_spec); intros; try constructor; auto. *)
  (*     unfold comp; case h; try constructor. *)
  (*     unfold comp; case h; try constructor. *)
  (*   Qed. *)

   
  (*   Instance compat_prd_Unit : forall p, compat_prd_unit (left p) -> *)
  (*     @Unit X R (Bin.value (e_bin i)) (eval (unit p)). *)
  (*   Proof. *)
  (*     intros. *)
  (*     inversion H; subst. apply is_unit_prd_Unit. assumption. *)
  (*   Qed. *)

  (*   Lemma z0' : forall l (r: @m idx (nelist T)), compat_prd_unit r -> *)
  (*     eval (prd i (run_list (comp (@appne T) l r))) == eval (prd i ((appne (l) (run_list r)))). *)
  (*   Proof. *)
  (*     intros. *)
  (*     unfold comp. unfold run_list. case_eq r; intros; auto; subst. *)
  (*     rewrite eval_prd_app. *)
  (*     rewrite eval_prd_nil. *)
  (*     apply compat_prd_Unit in H. rewrite law_neutral_right. reflexivity. *)
  (*     reflexivity. *)
  (*   Qed. *)
 
  (*   Lemma z1' a :  eval (prd i (run_list (return_prd i is_unit a))) ==  eval (prd i (nil a)). *)
  (*   Proof. *)
  (*     intros. unfold return_prd.  unfold run_list. *)
  (*     case (is_prd_spec); intros; subst; reflexivity. *)
  (*   Qed. *)
  (*   Lemma z2' : forall  u  x, compat_prd_unit  x ->  *)
  (*     eval (prd i ( run_list *)
  (*       (add_to_prd i is_unit u x))) ==  @Bin.value _ _ (e_bin i) (eval u) (eval (prd i (run_list x))). *)
  (*   Proof. *)
  (*     intros u x Hix. *)
  (*     unfold add_to_prd. *)
  (*     case (is_prd_spec); intros; subst. *)
  (*     rewrite z0' by auto.  rewrite eval_prd_app.  reflexivity. *)
  (*     apply is_unit_prd_Unit in H. rewrite law_neutral_left. reflexivity. *)
  (*     rewrite z0' by auto.  rewrite eval_prd_app. reflexivity. *)
  (*   Qed. *)
 
  (* End prd_correctness. *)




  (* Lemma eval_norm_lists i (Hnorm: forall u, eval (norm u) = eval u) : forall h, eval (prd i (norm_lists norm i h)) = eval (prd i h). *)
  (* Proof. *)
  (*   unfold norm_lists. *)
  (*   assert (H :  forall h : nelist T, *)
  (*     eval (prd i (run_list (norm_lists_ i (is_unit_of i) norm h))) == *)
  (*     eval (prd i h) *)
  (*     /\ compat_prd_unit (is_unit_of i) (norm_lists_ i (is_unit_of i) norm h)). *)
  
   
  (*     induction h as [a | a h [IHh IHh']]; simpl norm_lists_; split. *)
  (*     rewrite z1'. simpl.  apply Hnorm. *)
   
  (*     apply compat_prd_unit_return. *)
   
  (*     rewrite z2'. rewrite IHh.  rewrite eval_prd_cons.  rewrite Hnorm. reflexivity. apply is_unit_of_Unit. *)
  (*     auto. *)

  (*     apply compat_prd_unit_add. auto. *)
  (*     apply H. *)
  (*   Defined. *)

  (** correctness of the normalisation function *)

  Theorem eval_norm: forall iTy (u: T iTy), eval (norm u) = eval u
    with eval_norm_aux: forall arTy ret (l: vT arTy) (f: type_of_ar arTy ret),
      eval_aux (vnorm l) f = eval_aux l f.
  Proof.
    induction u as [ iTy p m (*| iTY p l*) | iTy ? | iTy ?];  cbn [norm].
    -case_eq (is_commutative iTy p); intros.
     +rewrite sum'_sum.
      apply eval_norm_msets; auto.
     +reflexivity.
    (*-rewrite prd'_prd.
    apply eval_norm_lists; auto.*)
    -apply eval_norm_aux.
    -reflexivity.
    -induction l; cbn; intros f.
     +reflexivity.
     +rewrite eval_norm. apply IHl; reflexivity.
  Qed.


  (** corollaries, for goal normalisation or decision *)

  Lemma normalise : forall iTy (u v: T iTy), eval (norm u) = eval (norm v) -> eval u = eval v.
  Proof. intros ? u v. rewrite 2 eval_norm. trivial. Qed.
   
  Lemma compare_reflect_eq iTy (u v : T iTy) : compare u v = Eq -> eval u = eval v.
  Proof. case (tcompare_weak_spec u v); intros; try congruence. Qed.

  Lemma decide iTy (u v: T iTy): compare (norm u) (norm v) = Eq -> eval u = eval v.
  Proof. intros H. apply normalise. apply compare_reflect_eq. apply H. Qed.

  (* Lemma lift_normalise {S} {H : AAC_lift S R}: *)
  (*   forall (u v: T), (let x := norm u in let y := norm v in *)
  (*     S (eval x) (eval y)) -> S (eval u) (eval v). *)
  (* Proof. destruct H. intros u v; simpl; rewrite 2 eval_norm. trivial. Qed. *)


  End ReifH.
End ReifH.
