(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2019: Fabian Kunze                                      *)
(***************************************************************************)

(** aac_apply -- rewriting modulo  *)

open Pcoq.Prim
open Pcoq.Constr
open Ltac_plugin
open Stdarg
open EConstr
open Names
open Proof_type

type hypinfo =
    {
      hyp : constr;		  (** the actual constr corresponding to the hypothese  *)
      hyptype : constr; 		(** the type of the hypothesis *)
      context : EConstr.rel_context;       	(** the quantifications of the hypothese *)
      body : constr; 		(** the body of the type of the hypothesis*)
    }

(** apply a lemma modulo AC *)
(* What do we want to support? *)
(* currently, it seems that just equality is supported *)
(* It would be nice to treat predicates up to equivalences *)
let aac_apply hyp  =
  Proofview.Goal.enter begin fun goal ->
    let env = Proofview.Goal.env goal in
    let sigma = Proofview.Goal.sigma goal in
    let hyp_type = Retyping.get_type_of env sigma hyp in
    
    (* TODO: check invariants like in get_hypinfo ? *)
    let (rel_context,body_type) = decompose_prod_assum sigma hyp_type in
    let _ = Feedback.msg_notice (Pp.(str "You passed: " ++ Printer.pr_econstr_env env sigma hyp)) in
    let _ = Feedback.msg_notice (Pp.(str "It has conclusion: " ++ Printer.pr_econstr_env (EConstr.push_rel_context rel_context env) sigma body_type)) in

    let _ = CErrors.user_err (Pp.(str "aac_apply is not implemented.")) in
    Proofview.tclUNIT()
    end
