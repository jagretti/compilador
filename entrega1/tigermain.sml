open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigerabs
open BasicIO Nonstdio

fun maxIntInList(l) = List.foldr Int.max 0 l

fun maxargs (VarExp(var,_)) = printInVar var
  | maxargs (CallExp({func, args},_)) = if func = "print" then Int.max((List.length args),(maxIntInList(List.map maxargs args))) else maxIntInList(List.map maxargs args)
  | maxargs (OpExp({left, oper, right},_)) = Int.max(maxargs left, maxargs right)
  | maxargs (RecordExp({fields,...},_)) = maxIntInList(List.map (maxargs o #2) fields)
  | maxargs (SeqExp(exp,_)) = maxIntInList(List.map maxargs exp)
  | maxargs (AssignExp({exp,...},_)) = maxargs exp
  | maxargs (IfExp({test, then', else'},_)) = Int.max(Int.max(maxargs test, maxargs then'), if Option.isSome(else') then maxargs (Option.valOf(else')) else 0)
  | maxargs (WhileExp({test, body},_)) = Int.max(maxargs test, maxargs body)
  | maxargs (ForExp({lo, hi, body,...},_)) = Int.max(Int.max(maxargs lo, maxargs hi), maxargs body)
  | maxargs (LetExp({decs,body},_)) = Int.max(maxargs body, maxIntInList(List.map printInDec decs))
  | maxargs (ArrayExp({size,init,...},_)) = Int.max(maxargs size, maxargs init)
  | maxargs _ = 0
and printInVar (SubscriptVar(var,exp)) = Int.max(printInVar var, maxargs exp)
  | printInVar (FieldVar(var,_)) = printInVar var
  | printInVar _ = 0
and printInDec (VarDec({init,...},_)) = maxargs init
  | printInDec (FunctionDec(li)) = maxIntInList(List.map (maxargs o #body o #1) li)
  | printInDec _ = 0

fun sum (x,y) = x + y
fun isplus (PlusOp) = 1
| isplus _ = 0
fun sumList l = foldr sum 0 l
fun cantplus (VarExp(var,_)) = plusInVar var
  | cantplus (CallExp({func, args},_)) = sumList(List.map cantplus args)
  | cantplus (OpExp({left, oper, right},_)) = isplus(oper) + (cantplus left) + (cantplus right)
  | cantplus (RecordExp({fields,...},_)) = sumList(List.map (cantplus o #2) fields)
  | cantplus (SeqExp(exp,_)) = sumList(List.map cantplus exp)
  | cantplus (AssignExp({exp,...},_)) = cantplus exp
  | cantplus (IfExp({test, then', else'},_)) = (cantplus test) + (cantplus then') + (if Option.isSome(else') then cantplus (Option.valOf(else')) else 0)
  | cantplus (WhileExp({test, body},_)) = (cantplus test) + (cantplus body)
  | cantplus (ForExp({lo, hi, body,...},_)) = (cantplus lo) + (cantplus hi) + (cantplus body)
  | cantplus (LetExp({decs,body},_)) = (cantplus body) + sumList(List.map plusInDec decs)
  | cantplus (ArrayExp({size,init,...},_)) = (cantplus size) + (cantplus init)
  | cantplus _ = 0
and plusInVar (SubscriptVar(var,exp)) = (plusInVar var) + (cantplus exp)
  | plusInVar (FieldVar(var,_)) = plusInVar var
  | plusInVar _ = 0
and plusInDec (VarDec({init,...},_)) = cantplus init
  | plusInDec (FunctionDec(li)) = sumList(List.map (cantplus o #body o #1) li)
  | plusInDec _ = 0
		       
fun lexstream(is: instream) =
	Lexing.createLexer(fn b => fn n => buff_input is b 0 n)
fun errParsing(lbuf) = (print("Error en parsing!("
	^(makestring(!num_linea))^
	")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")
fun main(args) =
  let	fun arg(l, s) =
	  (List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
	val (arbol, l1)		= arg(args, "-arbol")
	val (escapes, l2)	= arg(l1, "-escapes") 
	val (ir, l3)		= arg(l2, "-ir") 
	val (canon, l4)		= arg(l3, "-canon") 
	val (code, l5)		= arg(l4, "-code") 
	val (flow, l6)		= arg(l5, "-flow") 
	val (inter, l7)		= arg(l6, "-inter") 
	val entrada =
	    case l7 of
		[n] => ((open_in n)
			handle _ => raise Fail (n^" no existe!"))
	      | [] => std_in
	      | _ => raise Fail "opcio'n dsconocida!"
	val lexbuf = lexstream entrada
	val expr = prog Tok lexbuf handle _ => errParsing lexbuf
	val _ = findEscape(expr)
	val _ = if arbol then tigerpp.exprAst expr else ()
	val argsSize = maxargs(expr)
	val plusAmount = cantplus(expr)
(*	val lista = [("print", Func{level=mainLevel, label="print",
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
        ]*)
  in
      transProg(expr);
      print "yes!!\n";
      print (Int.toString(argsSize));
      print "\n";
      print (Int.toString(plusAmount));
      print "\n"
      (*prettyPrintEnv(map (#2) lista)*)
  end	handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
