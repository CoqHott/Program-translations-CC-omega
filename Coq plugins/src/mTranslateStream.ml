open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

       
type trans_struct = {
  timesBool : global_reference;
  pairTrue  : global_reference;
}

type translator = global_reference Refmap.t
exception MissingGlobal of global_reference

type translation_context = {
  trans : trans_struct;
  translator : translator;
}
			     
let get_inductive fctx ind =
  let gr = IndRef ind in
  let gr_ =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  match gr_ with
  | IndRef ind_ -> ind_
  | _ -> assert false

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  match gr with
  | IndRef _ -> assert false
  | _ -> (c, sigma)

let fst_ t =
  let mp = ModPath.MPfile (DirPath.make (List.rev_map Id.of_string ["TranslationDemo"; "theories"; "BoolProd"])) in
  mkProj (Projection.make (Constant.make1 (KerName.make2 mp (Label.make "fst"))) false, t)
	   
let rec translate env fctx sigma c =
  match kind_of_term c with
  | Rel n ->
     (c, sigma)
  | Var id ->
     apply_global env sigma (VarRef id) Univ.Instance.empty fctx
  | Sort s ->
     (c, sigma)
  | Cast (c, k, t) ->
     let mc, sigma = translate env fctx sigma c in
     let mt, sigma = translate_type env fctx sigma t in
     (mkCast (mc, k, mt), sigma)
  | Prod (na, t, u) ->
     let (mt, sigma) = (translate_type env fctx sigma t) in
     let (mu, sigma) = (translate_type (push_rel (na, None, t) env) fctx sigma u) in
     (mkProd (na, mt, mu), sigma)
  | Lambda (na, a, t) ->
     let ma, sigma = translate_type env fctx sigma a in
     let mt ,sigma = translate (push_rel (na, None, a) env) fctx sigma t in
     (mkLambda (na, ma, mt), sigma)
  | App (t, args) when isInd t -> (* e.g. @paths A *)
     let ((ind,i),k) = destInd t in
     translate_ind env fctx sigma ind i k args
  | App (t, args) when isConstruct t -> (* e.g. @idpath A a *)
     let (((ind,i),j),k) = destConstruct t in
     translate_construct env fctx sigma ind i j k args
  | App (t, args) ->
     let mt, sigma = translate env fctx sigma t in
     let fold u sigma = translate env fctx sigma u in
     let (args_, sigma) = CArray.fold_map' fold args sigma in
     mkApp (mt, args_), sigma
  | Const (p,u) ->
     apply_global env sigma (ConstRef p) u fctx
  | Ind ((ind,i),k) ->
     translate_ind env fctx sigma ind i k [||]
  | Construct (((ind,i), u), k) ->
     translate_construct env fctx sigma ind i u k [||]
  | LetIn (na, c, t, u) ->
     Errors.anomaly (Pp.str "let_in not implemented");
  | Case (ci, c, r, p) -> assert false
  | Fix f -> assert false
  | CoFix f -> assert false
  | Proj (p, c) -> assert false
  | Meta _ -> assert false
  | Evar _ -> assert false

and translate_type env fctx sigma t =
  translate env fctx sigma t

and translate_ind env fctx sigma ind i k args =
  let _, oib = Inductive.lookup_mind_specif env (ind,i) in
  let name = Id.to_string oib.mind_typename in
  let sigma, translator = Evarutil.new_global sigma fctx.trans.timesBool in
  if ("Stream" = name) then
    match args with
    | [| a |] ->
       let ma, sigma = translate_type env fctx sigma a in
       (mkApp (translator, [| mkApp(mkIndU ((ind, i), k), [| ma |]) |]), sigma)
    | _ -> assert false
  else if ("EqSt" = name) then
    match args with
    | [| a ; s1 ; s2 |] ->
       let ma, sigma = translate_type env fctx sigma a in
       let ms1, sigma = translate env fctx sigma s1 in
       let ms2, sigma = translate env fctx sigma s2 in
       (mkApp (mkIndU ((ind, i), k), [| ma ; fst_ ms1 ; fst_ ms2 |]), sigma)
    | _ -> assert false
  else
    let f u sigma = translate env fctx sigma u in
    let margs, sigma = CArray.fold_map' f args sigma in
    mkApp (mkIndU ((ind, i), k), margs), sigma
  
	
and translate_construct env fctx sigma ind i j k args =
  (* let f u sigma = translate env fctx sigma u in *)
  (* let margs, sigma = CArray.fold_map' f args sigma in *)
  (* mkApp (mkConstructU (((ind, i), j), k), margs), sigma *)
  Errors.anomaly (Pp.str "translation of constructors not implemented")
