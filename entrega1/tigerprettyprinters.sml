open tigersres
open tigermuestratipos

fun prettyPrintEnv (VIntro) = print "VIntro\n"
  | prettyPrintEnv (Var(ty)) =  (print "Var"; printTTipos([ty]))	
  | prettyPrintEnv (Func({label, formals, result, ...})) = (print "Func " ; print label; printTTipos formals; printTipo(result))
