structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=mainLevel, label="print",
			formals=[TString], result=TUnit, extern=true}),
	 ("flush", Func{level=mainLevel, label="flush",
			formals=[], result=TUnit, extern=true}),
	 ("getchar", Func{level=mainLevel, label="getstr",
			  formals=[], result=TString, extern=true}),
	 ("ord", Func{level=mainLevel, label="ord",
		      formals=[TString], result=TInt, extern=true}),
	 ("chr", Func{level=mainLevel, label="chr",
		      formals=[TInt], result=TString, extern=true}),
	 ("size", Func{level=mainLevel, label="size",
		       formals=[TString], result=TInt, extern=true}),
	 ("substring", Func{level=mainLevel, label="substring",
			    formals=[TString, TInt, TInt], result=TString, extern=true}),
	 ("concat", Func{level=mainLevel, label="concat",
			 formals=[TString, TString], result=TString, extern=true}),
	 ("not", Func{level=mainLevel, label="not",
		      formals=[TInt], result=TInt, extern=true}),
	 ("exit", Func{level=mainLevel, label="exit",
		       formals=[TInt], result=TUnit, extern=true})
    ])

fun tipoReal (TTipo s, (env : tenv)) : Tipo = 
  (case tabBusca(s , env) of 
       NONE => raise Fail "tipoReal Ttipo"
     | SOME t => t)
  | tipoReal (t, _) = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo _) b =
    (* let *)
    (* 	val a = case !r of *)
    (* 		SOME t => t *)
    (* 		| NONE => raise Fail "No debería pasar! (1)" *)
    (* in *)
    (* 	tiposIguales a b *)
    (* end *)raise Fail "No debería pasar! (1)"
  | tiposIguales a (TTipo _) =
    (* let *)
    (* 	val b = case !r of *)
    (* 		SOME t => t *)
    (* 		| NONE => raise Fail "No debería pasar! (2)" *)
    (* in *)
    (* 	tiposIguales a b *)
    (* end *)raise Fail "No debería pasar! (2)"
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
  let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
      fun trexp(VarExp v) = trvar(v)
	| trexp(UnitExp _) = {exp=(), ty=TUnit}
	| trexp(NilExp _)= {exp=(), ty=TNil}
	| trexp(IntExp(i, _)) = {exp=() ,ty=TInt}
	| trexp(StringExp(s, _)) = {exp=(), ty=TString}
	| trexp(CallExp({func, args}, nl)) =
	  {exp=(), ty=TUnit} (*COMPLETAR*)
	| trexp(OpExp({left, oper=EqOp, right}, nl)) =
	  let
	      val {exp=_, ty=tyl} = trexp left
	      val {exp=_, ty=tyr} = trexp right
	  in
	      if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
	      else error("Tipos no comparables", nl)
	  end
	| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
	  let
	      val {exp=_, ty=tyl} = trexp left
	      val {exp=_, ty=tyr} = trexp right
	  in
	      if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
	      else error("Tipos no comparables", nl)
	  end
	| trexp(OpExp({left, oper, right}, nl)) = 
	  let
	      val {exp=_, ty=tyl} = trexp left
	      val {exp=_, ty=tyr} = trexp right
	  in
	      if tiposIguales tyl tyr then
		  case oper of
		      PlusOp => if tipoReal(tyl, tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | MinusOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | TimesOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | DivideOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | LtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | LeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | GtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | GeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		    | _ => raise Fail "No debería pasar! (3)"
	      else error("Error de tipos", nl)
	  end
	| trexp(RecordExp({fields, typ}, nl)) =
	  let
	      (* Traducir cada expresión de fields *)
	      val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

	      (* Buscar el tipo *)
	      val (tyr, cs) = case tabBusca(typ, tenv) of
				  SOME t => (case tipoReal(t,tenv) of
						 TRecord (cs, u) => (TRecord (cs, u), cs)
					       | _ => error(typ^" no es de tipo record", nl))
				| NONE => error("Tipo inexistente ("^typ^")", nl)
					       
	      (* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
	      fun verificar [] [] = ()
		| verificar (c::cs) [] = error("Faltan campos", nl)
		| verificar [] (c::cs) = error("Sobran campos", nl)
		| verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
		  if s<>sy then error("Error de campo", nl)
		  else if tiposIguales ty (!t) then verificar cs ds
		  else error("Error de tipo del campo "^s, nl)
	      val _ = verificar cs tfields
	  in {exp=(), ty=tyr} end
	| trexp(SeqExp(s, nl)) =
	  let	val lexti = map trexp s
		val exprs = map (fn{exp, ty} => exp) lexti
		val {exp, ty=tipo} = hd(rev lexti)
	  in {exp=(), ty=tipo} end
	| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
	  let val {exp=ee, ty=te} = trexp exp
	      val tv = if tabEsta(s,tenv) then tabSaca(s,tenv) else error("Error variable sin definir", nl) 
              val _ = if not(tiposIguales tv TIntRO) then error("Error de asignación a variable de solo lectura", nl) else ()
	  in {exp=(), ty=TUnit} end (*COMPLETAR*)
	| trexp(AssignExp({var, exp}, nl)) =
	  let val {exp=ev, ty=tv} = trvar(var, nl)
	      val {exp=ee, ty=te} = trexp(exp)
	      val _ = if te <> TUnit andalso tiposIguales tv te then () else error("Error de asignación, el tipo declarado no coincide con el tipo asignado",nl) 
	  in  {exp=(), ty=TUnit}(*COMPLETAR*) end 
	| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
	  let val {exp=testexp, ty=tytest} = trexp test
	      val {exp=thenexp, ty=tythen} = trexp then'
	      val {exp=elseexp, ty=tyelse} = trexp else'
	  in
	      if tipoReal(tytest,tenv)=TInt andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
	      else error("Error de tipos en if" ,nl)
	  end
	| trexp(IfExp({test, then', else'=NONE}, nl)) =
	  let val {exp=exptest,ty=tytest} = trexp test
	      val {exp=expthen,ty=tythen} = trexp then'
	  in
	      if tipoReal(tytest,tenv)=TInt andalso tythen=TUnit then {exp=(), ty=TUnit}
	      else error("Error de tipos en if", nl)
	  end
	| trexp(WhileExp({test, body}, nl)) =
	  let
	      val ttest = trexp test
	      val tbody = trexp body
	  in
	      if tipoReal(#ty ttest, tenv) = TInt andalso #ty tbody = TUnit then {exp=(), ty=TUnit}
	      else if tipoReal(#ty ttest, tenv) <> TInt then error("Error de tipo en la condición", nl)
	      else error("El cuerpo de un while no puede devolver un valor", nl)
	  end
	| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
	  let
	      val {exp=explo, ty=tylo} = trexp lo
	      val _ = if tylo = TInt then () else error("Error 1",nl)
	      val {exp=exphi, ty=tyhi} = trexp hi
	      val _ = if tyhi = TInt then () else error("Error 2",nl)
	      val venv' = tabInserta(var, (Var{ty=TIntRO}), venv)
	      val {exp=expbody, ty=tybody} = transExp(venv', tenv) body
	      val _ = if tybody = TUnit then () else error("Error 3",nl)
	  in
	      {exp=(), ty=TUnit}
	  end (*COMPLETAR*)
	| trexp(LetExp({decs, body}, _)) =
	  let
	      val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
	      val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
	  in 
	      {exp=(), ty=tybody}
	  end
	| trexp(BreakExp nl) =
	  {exp=(), ty=TUnit} (*COMPLETAR*)
	| trexp(ArrayExp({typ, size, init}, nl)) =
            let
                val {exp=exps,ty=tys} = trexp size
                val {exp=expi,ty=tyi} = trexp init
                val _ = if tiposIguales tys (TIntRO) then () else error("El size del arreglo no es entero",nl) 
                val (ta,ur) = ( case tabBusca(typ,tenv) of
                                  SOME t => ( case t of
                                                  TArray (ta',ur') => (ta',ur')
                                                | _ => error("El tipo "^typ^" no es un arreglo",nl) )
                                  | _ => error("Tipo "^typ^" no definido",nl) )
                val _ = if tiposIguales (!ta) tyi then () else error("La expresion inicializadora no es un "^typ,nl)(*no habria que imprimir !ta?*)
            in {exp=(), ty=TArray (ta,ur)} end 
      and trvar(SimpleVar s, nl) =
          let
	      val enventry = case tabBusca(s, venv) of
                             SOME (Var{ty}) => ty
                           | _ => error("Variable no definida en el scope",nl)
          in {exp=(), ty=enventry} end(*COMPLETAR*)
	| trvar(FieldVar(v, s), nl) =
	  let
          val {exp=expv, ty=tyv} = trvar(v,nl)
	      val vartype = case tyv of
				            TRecord (l,_) => ( case List.filter (fn x => #1x = s) l of
                                                   [] => error("Record no tiene campo "^s,nl)
                                                   | (e::_) => #2e )
                            | _ => (tigerpp.prettyPrintTipo(tyv) ; error("No se puede indexar porque no es Record",nl)) 
      in {exp=(), ty=(!vartype)} (*COMPLETAR*) end
	| trvar(SubscriptVar(v, e), nl) =
      let
          val {exp=expe, ty=te} = trexp e
          val {exp=expv, ty=tv} = trvar(v,nl)
          val _ = if tiposIguales te (TInt) then () else error("Indice debe ser entero",nl)
      in case tv of
             TArray (t,_) => {exp=(), ty=(!t)}
             | _ => error("Indexando algo que no es un arreglo", nl) end
      and trdec (venv, tenv) (VarDec ({name,escape,typ,init},pos)) = 
         (* let val {expinit, tyinit} = transExp(tenv, venv, init)
              val tyv = case typ of
                            NONE => if tiposIguales tyinit TNil then error("Error HA HA! Baboso", nl) else tyinit 
                            | SOME => *)
	  (venv, tenv, []) (*COMPLETAR*)
	| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
	  (venv, tenv, []) (*COMPLETAR*)
	| trdec (venv,tenv) (FunctionDec fs) =
	  (venv, tenv, []) (*COMPLETAR*)
	| trdec (venv,tenv) (TypeDec ts) =
	  (venv, tenv, []) (*COMPLETAR*)
  in trexp end
fun transProg ex =
  let	val main =
	    LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
					result=NONE, body=ex}, 0)]],
		    body=UnitExp 0}, 0)
	val _ = transExp(tab_vars, tab_tipos) ex (*main*)
  in	print "bien!\n" end
end

