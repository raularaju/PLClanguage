(* Plc interpreter main file *)

fun run(e: expr) =
    let
        val eType = teval e []
        val eValue = eval e []
    in  
        (val2string eValue) ^ " : " ^ (type2string eType)
    end
    handle
        SymbolNotFound => "Symbol not found."
      | EmptySeq => "Empty sequence."
      | UnknownType => "Unknown type."
      | NotEqTypes => "Types in comparison are different."
      | WrongRetType => "Wrong return type in function."
      | Impossible => "Impossible to evaluate expression."
      | HDEmptySeq => "'hd' called with an empty sequence argument."
      | TLEmptySeq => "'tl' called with an empty sequence argument."
      | ValueNotFoundInMatch => "Value not found in match."
      | NotAFunc => "Eval Call: not a function."
      | DiffBrTypes => "'if' branch types differ."
      | IfCondNotBool => "'if' condition not Boolean."
      | NoMatchResults => "No Match results."
      | MatchResTypeDiff => "'match' result types differ."
      | MatchCondTypesDiff => "'match' condition types differ matching expression's type."
      | CallTypeMisM => "Type mismatch in function call."
      | NotFunc => "Not a function."
      | ListOutOfRange => "List index out of range."
      | OpNonList => "Selection with operator # applied to non-list."



        