structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertopsort
open tigertrans

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

fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")

fun cmpTipo(t1,t2,nl) = if tiposIguales t1 t2 then t1 else error("Tipos distintos en cmpTipo!",nl)

fun transExp(venv, tenv) =
  let fun trexp(VarExp v) = trvar(v)
	| trexp(UnitExp _) = {exp=intExp 0, ty=TUnit}
	| trexp(NilExp _)= {exp=intExp 0, ty=TNil}
	| trexp(IntExp(i, _)) = {exp=intExp i ,ty=TInt}
	| trexp(StringExp(s, _)) = {exp=stringExp s, ty=TString}
	| trexp(CallExp({func, args}, nl)) =
	  let
              val (targs,tresult) = case tabBusca(func,venv) of
					SOME (Func {formals=formals,result=result,level=_,label=_,extern=_}) => (formals,result)
				      | _ => error (func^" no es funciÃ³n o no estÃ¡ siendo definida en este batch.",nl)
              val lteargs = List.map trexp args
              val ltargs = List.map (#ty) lteargs
              val _ = if List.length targs = List.length ltargs then () else error("FunciÃ³n "^func^" invocada con una cantidad incorrecta de argumentos!",nl)
              val _ = List.map (fn(x,y) => cmpTipo(x,y,nl)) (ListPair.zip(ltargs,targs))
                      handle Empty => error("NÂº de args",nl)
	  in {ty=tresult, exp=SCAF} end (*COMPLETAR*)
	| trexp(OpExp({left, oper=EqOp, right}, nl)) =
	  let
	      val {exp=_, ty=tyl} = trexp left
	      val {exp=_, ty=tyr} = trexp right
	  in
	      if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt}
	      else error("Tipos no comparables", nl)
	  end
	| trexp(OpExp({left, oper=NeqOp, right}, nl)) =
	  let
	      val {exp=_, ty=tyl} = trexp left
	      val {exp=_, ty=tyr} = trexp right
	  in
	      if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt}
	      else error("Tipos no comparables", nl)
	  end
	| trexp(OpExp({left, oper, right}, nl)) =
	  let
	      val {exp=_, ty=tyl} = trexp left
	      val {exp=_, ty=tyr} = trexp right
	  in
	      if tiposIguales tyl tyr then
		  case oper of
		      PlusOp => if tipoReal(tyl, tenv)=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | MinusOp => if tipoReal(tyl,tenv)=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | TimesOp => if tipoReal(tyl,tenv)=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | DivideOp => if tipoReal(tyl,tenv)=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | LtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | LeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | GtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
		    | GeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
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
	  in {exp=SCAF, ty=tyr} end
	| trexp(SeqExp(s, nl)) =
	  let	val lexti = map trexp s
		val exprs = map (fn{exp, ty} => exp) lexti
		val {exp, ty=tipo} = hd(rev lexti)
	  in {exp=SCAF, ty=tipo} end
	| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
	  let val {exp=ee, ty=te} = trexp exp
	      val tv = if tabEsta(s,tenv) then tabSaca(s,tenv) else error("Error variable sin definir", nl)
              val _ = if not(tiposIguales tv TIntRO) then error("Error de asignación a variable de solo lectura", nl) else ()
	  in {exp=SCAF, ty=TUnit} end (*COMPLETAR*)
	| trexp(AssignExp({var, exp}, nl)) =
	  let val {exp=ev, ty=tv} = trvar(var, nl)
	      val {exp=ee, ty=te} = trexp(exp)
	      val _ = if te <> TUnit andalso tiposIguales tv te then () else error("Error de asignación, el tipo declarado no coincide con el tipo asignado",nl)
	  in  {exp=SCAF, ty=TUnit}(*COMPLETAR*) end
	| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
	  let val {exp=testexp, ty=tytest} = trexp test
	      val {exp=thenexp, ty=tythen} = trexp then'
	      val {exp=elseexp, ty=tyelse} = trexp else'
	  in
	      if tipoReal(tytest,tenv)=TInt andalso tiposIguales tythen tyelse then {exp=SCAF, ty=tythen}
	      else error("Error de tipos en if" ,nl)
	  end
	| trexp(IfExp({test, then', else'=NONE}, nl)) =
	  let val {exp=exptest,ty=tytest} = trexp test
	      val {exp=expthen,ty=tythen} = trexp then'
	  in
	      if tipoReal(tytest,tenv)=TInt andalso tythen=TUnit then
                {exp=ifThenExp exptest expthen, ty=TUnit}
	      else error("Error de tipos en if", nl)
	  end
	| trexp(WhileExp({test, body}, nl)) =
	  let
	      val ttest = trexp test
	      val tbody = trexp body
	  in
	      if tipoReal(#ty ttest, tenv) = TInt andalso #ty tbody = TUnit then {exp=SCAF, ty=TUnit}
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
	      {exp=SCAF, ty=TUnit}
	  end (*COMPLETAR*)
	| trexp(LetExp({decs, body}, _)) =
	  let
	      val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
	      val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
	  in
	      {exp=SCAF, ty=tybody}
	  end
	| trexp(BreakExp nl) =
	  {exp=SCAF, ty=TUnit} (*COMPLETAR*)
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
          in {exp=SCAF, ty=TArray (ta,ur)} end
      and trvar(SimpleVar s, nl) =
          let
	      val enventry = case tabBusca(s, venv) of
				 SOME (Var{ty}) => ty
                               | _ => error("Variable no definida en el scope",nl)
          in {exp=SCAF, ty=enventry} end(*COMPLETAR*)
	| trvar(FieldVar(v, s), nl) =
	  let
              val {exp=expv, ty=tyv} = trvar(v,nl)
	      val vartype = case tyv of
				TRecord (l,_) => ( case List.filter (fn x => #1x = s) l of
                                                       [] => error("Record no tiene campo "^s,nl)
                                                     | (e::_) => #2e )
                              | _ => (tigerpp.prettyPrintTipo(tyv) ; error("No se puede indexar porque no es Record",nl))
	  in {exp=SCAF, ty=(!vartype)} (*COMPLETAR*) end
	| trvar(SubscriptVar(v, e), nl) =
	  let
              val {exp=expe, ty=te} = trexp e
              val {exp=expv, ty=tv} = trvar(v,nl)
              val _ = if tiposIguales te (TInt) then () else error("Indice debe ser entero",nl)
	  in case tv of
		 TArray (t,_) => {exp=SCAF, ty=(!t)}
               | _ => error("Indexando algo que no es un arreglo", nl) end
      and trdec (venv, tenv) (VarDec ({name,escape,typ,init},pos)) =
          let val {exp=expinit, ty=tyinit} = trexp init
              val tyv = case typ of
                            NONE => if tiposIguales tyinit TNil then error("Error HA HA! Baboso", pos) else tyinit
                          | SOME nt => let val t' = case tabBusca(nt, tenv) of
							SOME t'' => t''
						      | NONE => error("VER ERROR",pos)
                                           val _  = if tiposIguales tyinit t' then () else error("Error (VER QUE VA)", pos)
                                       in t' end
              val venv' = tabInserta(name, (Var{ty=tyv}), venv)
          in (venv', tenv, []) end
	| trdec (venv,tenv) (FunctionDec fs) = (* COMPLETAR *)
          let (* Buscar si hay nombres repetidos. Recordar que no se pueden sobreescribir funciones dentro de un mismo batch *)
              fun reps [] = false
              |   reps (({name,...},nl) :: t) = if List.exists (fn ({name = x,...},_) => x = name) t then true else reps t
              val _ = if reps fs then raise Fail ("trdec(FunctionDec): Nombres repetidos\n") else ()

              fun tyToTipo [] = []
                | tyToTipo ({typ=NameTy s, ... } :: ss) =
                  (case tabBusca(s, tenv) of
                       SOME t => (t :: tyToTipo ss)
                     | _ => raise Fail ("trdec(FunctionDec): el tipo "^s^" es inexistente\n"))
                | tyToTipo _ = raise Fail ("trdec(FunctionDec): esto no deberia pasar!\n") (* no puede pasar ya que la sintaxis de tiger no permite que los argumentos tengan explicitamente tipo record o array. Para ello hay que definir una etiqueta *)

              fun aux venv' [] = venv'
                | aux venv' (({name, params, result, ...}, nl)::fss) =
                  let val resultType = case result of
                                           NONE => TUnit
                                         | SOME t => case tabBusca(t, tenv) of
                                                         NONE => error ("trdec(FunctionDec) (aux): el tipo "^t^" no existe!", nl)
                                                       | SOME t' => t'
                      val entry = Func {level=(), label=tigertemp.newlabel(), formals=tyToTipo params, result=resultType, extern=false}
                      (* extern=false ya que las funciones externas se definen en runtime *)
                      val venv'' = tabRInserta(name, entry, venv')
                  in aux venv'' fss end
              fun addParams venv [] = ()
              |   addParams venv (({name,params, body, ...}, nl)::fss) =
                  let
                      val tipos = tyToTipo params
                      val nombres = map #name params
                      fun addParam [] [] venv = venv
                      |   addParam (n::ns) (t::ts) venv = addParam ns ts (tabRInserta(n,Var{ty=t},venv))
                      |   addParam _ _ _ = error("trdec(FunctionDec): Error interno en addParams 1",nl)
                      val venv' = addParam nombres tipos venv
                      val {ty = tyBody,...} = transExp (venv',tenv) body
                      val tyResult = case tabBusca(name,venv) of
                                         NONE => error("trdec(FunctionDec): Error interno en addParams 2",nl)
                                       | SOME (Func{result,...}) => result
                                       | SOME _ => error("trdec(FunctionDec): Error interno en addParams 3",nl)
                      (* val _ = printTipo tyBody
                        val _ = printTipo tyResult *)
                      val _ = if tiposIguales tyBody tyResult then () else error("trdec(FunctionDec): Los tipos de retorno de la funcion y el tipo de su body no coinciden",nl)
                  in addParams venv fss end

              val venv' = aux venv fs
              val _ = addParams venv' fs
          in (venv', tenv, []) end
	| trdec (venv,tenv) (TypeDec ts) =
          let val sortedNames = Listsort.sort
                                (fn (({name=x,ty=_},_), ({name=y,ty=_},_)) => if x<y then LESS else (if x>y then GREATER else EQUAL))
                                ts
              val _ = List.foldr (* Chequea que no hay dos seguidos iguales en sortedNames *)
                      (fn (t1 as ({name=n1,ty=_},posx), ({name=n2,ty=_},_)) => if n1=n2 then error("Se definiÃ³ dos veces el tipo "^n1^" en un mismo batch.",posx) else t1)
                      ({name="",ty=NameTy ""},0) (* Invento un tipo con nombre "" que no va a ser igual a ninguno de los que se definan. *)
                      sortedNames
              val ltsinpos = List.map (fn (x,pos) => x) ts
              val tenv' = tigertopsort.fijaTipos ltsinpos tenv
	  in (venv, tenv', []) end (*COMPLETAR*)
  in trexp end
fun transProg ex =
  let val main =
	    LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
					result=NONE, body=ex}, 0)]],
		    body=UnitExp 0}, 0)
	val _ = transExp(tab_vars, tab_tipos) ex (*main*)
  in	print "bien!\n" end
end
