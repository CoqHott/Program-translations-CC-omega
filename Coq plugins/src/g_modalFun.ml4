DECLARE PLUGIN "mTranslateFun"


VERNAC COMMAND EXTEND TransTranslation CLASSIFIED AS SIDEFF
| [ "Translate" global(gr) ] -> [ MPluginFun.translate gr None ]
(*
| [ "Translate" global(gr) "as" ne_ident_list(id) "using" global(transProd) global(transLam)] ->
  [ MPlugin.trans_translate (transProd,transLam) gr (Some id) ]
*)
END


let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)


VERNAC COMMAND EXTEND TransImplementation CLASSIFIED BY classify_impl
| [ "Implement" ident(id) ":" lconstr(typ) ] -> [ MPluginFun.implement id typ None ]
(*
| [ "Trans" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') "using" global(transProd) global(transLam)] ->
  [ MPlugin.trans_implement (transProd,transLam) id typ (Some id') ]
*)
END