open Names
open Libnames
open Proofview

val trans_translate : (reference * reference) -> reference -> Id.t list option -> unit

val trans_implement : (reference * reference) -> Id.t -> Constrexpr.constr_expr -> Id.t option -> unit
