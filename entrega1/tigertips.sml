structure tigertips =
struct

type unique = unit ref
datatype Tipo = TUnit
	      | TNil
	      | TInt
	      | TIntRO
	      | TString
	      | TArray of Tipo ref  * unique
	      | TRecord of (string * Tipo ref * int) list * unique
	      | TTipo of string 
end
