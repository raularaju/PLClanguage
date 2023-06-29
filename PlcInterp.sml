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
        | List l => ListV (map (fn x => eval x env) l)
        | ESeq (SeqT t) => SeqV []
        | If(e1, e2, e3) =>
            let
                val v1 = eval e1 env
            in 
                case v1 of
                    BoolV true => eval e2 env
                    | BoolV false => eval e3 env
                    | _ => raise Impossible
            end
        | Match(e, l) => (* Não considera que pode haver matches redundantes *)
            let
                val v = eval e env
            in 
                case l of 
                        (NONE , e1) :: tl => eval e1 env
                        | (SOME e1, e2 ) :: tl => 
                            let val v1 = eval e1 env
                            in
                                if v = v1 then eval e2 env
                                else eval (Match(e, tl)) env
                            end  
            end
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
                    | ("hd", SeqV l) => if v1 = SeqV [] then raise HDEmptySeq else hd l
                    | ("tl", SeqV l) => if v1 = SeqV [] then raise TLEmptySeq else SeqV (tl l)
                    | ("ise", SeqV _) => if v1 = SeqV [] then BoolV true else BoolV false
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
                    | ("&&", BoolV b1, BoolV b2) => BoolV (b1 andalso b2)
                    | ("::", _, SeqV l) => SeqV (v1 :: l)
                    | ("<", IntV i1, IntV i2) => BoolV (i1 < i2)
                    | ("<=", IntV i1, IntV i2) => BoolV (i1 <= i2)
                    | ("=",  i1,  i2) => BoolV (i1 = i2)
                    | ("!=", x, y) => BoolV (x <> y)
                    | (";", _, _) => v2
                    | _ => raise Impossible
            end
        | Item(i, l) =>
            let 
                val v = eval l env
            in 
                case v of
                    ListV l => List.nth(l, i-1)
                    | _ => raise OpNonListT
            end
        | Let(x, e1, e2) =>
            let 
                val v = eval e1 env
                val env' = (x,v)::env
            in 
                eval e2 env'
            end
        | Anon(t, x, e) => Clos("", x, e, env)
        | Call(func, p) => 
            let
                val v = eval func env
                val param = eval p env
            in
                case v of
                    Clos(t, x, e, fenv) =>
                        eval e ((t, v) :: (x, param) :: fenv)
                    | _ => raise NotFunc
            end
        | Letrec(f, tf, x, tx, e1, e2) =>
            let 
                val v = Clos(f, x, e1, env)
                val env' = (f, v)::env
            in
                eval e2 env'
            end
        | _ => raise Impossible