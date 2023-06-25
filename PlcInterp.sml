(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

fun eval (e: expr) (env: plcVal env) : plcVal =
    case e of 
        Var x => lookup env x
        | ConI i => IntV i
        | ConB b => BoolV b
        | List [] => ListV []
        | List l =>
            let val lis = map(fn )
        | Prim1(opr, e1) =>
            let
                val v1 = eval e1 env
            in
                case (opr, v1) of   
                    ("print", _) =>
                                    let
                                        val s = val2string v1
                                    in 
                                        print(s^"\n"); ListV []
                                    end
                    | ("-", IntV i) => IntV (~i)
                    | ("!", BoolV b) => BoolV (not b)
                    | ("hd", SeqV _) => if v1 = ListV [] then raise HDEmptySeq else hd l
                    | ("tl", SeqV _) => if v1 = ListV [] then raise TLEmptySeq else ListV (tl l)
                    | ("ise", SeqV _) => if v1 = ListV [] then BoolV true else BoolV false
                    | _ => raise Impossible
            end
        | Prim2(opr, e1, e2) =>
            let
                val v1 = eval e1 env
                val v2 = eval e2 env
            in
                case (opr, v1, v2) of
                     ("+", IntV i1, IntV i2) => IntV (i1 + i2)
                    | ("-", IntV i1, IntV i2) => IntV (i1 - i2)
                    | ("*", IntV i1, IntV i2) => IntV (i1 * i2)
                    | ("/", IntV i1, IntV i2) => IntV (i1 div i2)
                    | (";", _, _) => v2
                    | _ => raise Impossible
            end
        | Let(x, e1, e2) =>
            let 
                val v = eval e1 env
                val env' = (x,v)::env
            in 
                eval e2 env'
            end
        | _ => raise Impossible