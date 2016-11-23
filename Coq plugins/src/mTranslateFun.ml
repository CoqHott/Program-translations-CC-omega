open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

       
type translator = global_reference Refmap.t
exception MissingGlobal of global_reference
			     
let get_inductive trans ind =
  let gr = IndRef ind in
  let gr_ =
    try Refmap.find gr trans
    with Not_found -> raise (MissingGlobal gr)
  in
  match gr_ with
  | IndRef ind_ -> ind_
  | _ -> assert false

let apply_global env sigma gr u trans =
  (** FIXME *)
  let p' =
    try Refmap.find gr trans
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  match gr with
  | IndRef _ -> assert false
  | _ -> (c, sigma)


let mp = ModPath.MPfile (DirPath.make (List.rev_map Id.of_string ["TranslationDemo"; "theories"; "BoolProd"]))	
let bool__ = (MutInd.make1 (KerName.make2 mp (Label.make "bool")), 0)
let bool_ = mkInd bool__
let true_ = mkConstruct (ith_constructor_of_inductive bool__ 1)
let prod__ = (MutInd.make1 (KerName.make2 mp (Label.make "prod")), 0)
let prod_ = mkInd prod__
let pair_ = mkConstruct (ith_constructor_of_inductive prod__ 1)
let fst_ = fun t -> mkProj (Projection.make (Constant.make1 (KerName.make2 mp (Label.make "fst"))) true, t)

			   
let rec translate env trans sigma c =
  match kind_of_term c with
  | Rel n ->
     (c, sigma)
  | Var id ->
     apply_global env sigma (VarRef id) Univ.Instance.empty trans
  | Sort s ->
     (c, sigma)
  | Cast (c, k, t) ->
     let mc, sigma = translate env trans sigma c in
     let mt, sigma = translate_type env trans sigma t in
     (mkCast (mc, k, mt), sigma)
  | Prod (na, t, u) ->
     let (mt, sigma) = (translate_type env trans sigma t) in
     let (mu, sigma) = (translate_type (push_rel (na, None, t) env) trans sigma u) in
     mkApp (prod_, [| mkProd (na, mt, mu) ; bool_ |]), sigma
  | Lambda (na, a, t) ->
     let ma, sigma = translate_type env trans sigma a in
     let mt ,sigma = translate (push_rel (na, None, a) env) trans sigma t in
     let mt' = mkLambda (na, ma, mt) in
     let sigma, mu  = Typing.type_of env sigma mt' in
     let c' = mkApp (pair_, [| mu ; bool_; mt' ; true_ |]) in
     c', sigma
  | App (t, args) when isInd t -> (* e.g. @paths A *)
     let ((ind,i),k) = destInd t in
     translate_ind env trans sigma ind i k args
  | App (t, args) when isConstruct t -> (* e.g. @idpath A a *)
     let (((ind,i),j),k) = destConstruct t in
     translate_construct env trans sigma ind i j k args
  | App (t, args) ->
     let t =
       match Array.length args with
       | 0 -> assert false
       | 1 -> t
       | n -> mkApp (t, Array.sub args 0 (n-1)) in
     let u = args.((Array.length args) - 1) in
     let mt, sigma = translate env trans sigma t in
     let mu, sigma = translate env trans sigma u in
     let c' = mkApp (fst_ mt, [| mu |]) in
     c', sigma
  | Const (p,u) ->
     apply_global env sigma (ConstRef p) u trans
  | Ind ((ind,i),k) ->
     translate_ind env trans sigma ind i k [||]
  | Construct (((ind,i), u), k) ->
     translate_construct env trans sigma ind i u k [||]
  | LetIn (na, c, t, u) ->
     Errors.anomaly (Pp.str "let_in not implemented");
  | Case (ci, c, r, p) -> assert false
  | Fix f -> assert false
  | CoFix f -> assert false
  | Proj (p, c) -> assert false
  | Meta _ -> assert false
  | Evar _ -> assert false

and translate_type env trans sigma t =
  let mt, sigma = translate env trans sigma t in
  mt, sigma
	
and translate_ind env trans sigma ind i k args =
  let _, oib = Inductive.lookup_mind_specif env (ind,i) in
  let name = Id.to_string oib.mind_typename in
  if ("eq" = name) then
    match args with
    | [| t; a; b |] ->
       let mt, sigma = translate_type env trans sigma t in
       let ma, sigma = translate env trans sigma a in
       let mb, sigma = translate env trans sigma b in
       (mkApp(mkIndU ((ind, i), k), [| mt; ma; mb |]), sigma)
    | _ -> assert false
  else if ("sigT" = name) then
    match args with
    | [| a; b |] ->
       let ma, sigma = translate_type env trans sigma a in
       let na, a, b' = destLambda b in
       let mb, sigma = translate_type (push_rel (na, None, a) env) trans sigma b' in
       (mkApp(mkIndU ((ind, i), k), [| ma; mkLambda (na, ma, mb) |]), sigma)
    | _ -> assert false
  else
    mkIndU ((ind, i), k), sigma
  
	
and translate_construct env trans sigma ind i j k args =
  let f u sigma = translate env trans sigma u in
  let margs, sigma = CArray.fold_map' f args sigma in
  mkApp (mkConstructU (((ind, i), j), k), margs), sigma  
