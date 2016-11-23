open Globnames

type trans_struct = {
  timesBool : global_reference;
  pairTrue  : global_reference;
}

type translator = global_reference Refmap.t

type translation_context = {
  trans : trans_struct;
  translator : translator;
}

exception MissingGlobal of global_reference

val translate : Environ.env -> translation_context -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_type : Environ.env -> translation_context -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_ind : Environ.env -> translation_context -> Evd.evar_map -> Names.MutInd.t -> int -> Univ.universe_instance -> Term.constr array -> Constr.t * Evd.evar_map

(* val translate_context : Environ.env -> translation_context -> Evd.evar_map -> Context.rel_context -> Context.rel_context * Evd.evar_map *)
