open Globnames

type translator = global_reference Refmap.t

exception MissingGlobal of global_reference

val translate : Environ.env -> translator -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_type : Environ.env -> translator -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_ind : Environ.env -> translator -> Evd.evar_map -> Names.MutInd.t -> int -> Univ.universe_instance -> Term.constr array -> Constr.t * Evd.evar_map
