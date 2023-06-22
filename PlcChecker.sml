(* PlcChecker *)

exception EmptySeq
exception UnknownType
exception NotEqTypes
exception WrongRetType
exception DiffBrTypes
exception IfCondNotBool
exception NoMatchResults
exception MatchResTypeDiff
exception MatchCondTypesDiff
exception CallTypeMisM
exception NotFunc
exception ListOutOfRange
exception OpNonListT

fun isEqualType (t: plcType) : bool = 
    case t of 
        IntT => true
        | BoolT => true
        | ListT [] => true
        | ListT (hd :: tl) => isEqualType hd andalso isEqualType (ListT tl)
        | SeqT t => isEqualType t
        | _ => false
fun ithTypeList (l: plcType list) (i: int) : plcType = 
    case l of 
        [] => raise ListOutOfRange
        | (hd :: tl) => if i = 1 then hd else ithTypeList tl (i-1)

fun teval (e: expr) (env: plcType env) : plcType = 
    case e of 
        Var x => lookup env x
        | ConI x => IntT
        | ConB _ => BoolT 
        | List [] => ListT []
        | List (x :: t) =>
            let val types = map (fn e => teval e env) (x :: t)
            in
                ListT types
            end
        | ESeq (SeqT t)  => SeqT t
        (* | Letrec (f, t1, x, t2, e1, e2) =>
            let
                val env' = (f, FunT (t1, t2)) :: env
                val env'' = (x, t1) :: env'
                val t3 = teval e1 env''
            in
                if t2 = t3 then
                    teval e2 env'
                else
                    raise WrongRetType
            end *)
        | Prim1(opr, e1) =>
            let val t1 = teval e1 env
            in
                case (opr, t1) of
                    ("print", _) => ListT []
                    | ("-", IntT) => IntT
                    | ("!", BoolT) => BoolT
                    | ("hd", SeqT t) => if t1 = ListT [] then raise EmptySeq else t
                    | ("tl", SeqT t) => SeqT t
                    | ("ise", SeqT _) => BoolT
                    | _ => raise UnknownType
            end
        | Prim2(opr, e1, e2) =>
            let
                val t1 = teval e1 env
                val t2 = teval e2 env
            in
                case (opr, t1, t2) of
                 ("*", IntT, IntT) => IntT
                | ("/", IntT, IntT) => IntT
                | ("+", IntT, IntT) => IntT
                | ("-", IntT, IntT) => IntT
                | ("&&", BoolT, BoolT) => BoolT
                | ("::", _ , SeqT tSeq) => if t1 = tSeq then SeqT tSeq else raise UnknownType 
                | ("<", IntT, IntT) => BoolT
                | ("<=", IntT, IntT) => BoolT
                | ("=",_ , _) => if isEqualType t1 andalso isEqualType t2 andalso t1 = t2 then BoolT else raise NotEqTypes
                | ("!=",_ , _) => if isEqualType t1 andalso isEqualType t2 andalso t1 = t2 then BoolT else raise NotEqTypes                
                | (";", _, _ ) => t2
                | _ => raise UnknownType
            end
        | Item (i, l) =>
            let
                val t = teval l env
            in
                case t of
                    ListT types =>  ithTypeList (types) i 
                    | _ => raise OpNonListT
            end
        | Let(x, e1, e2) =>
            let
                val t1 = teval e1 env
                val env' = (x,t1) :: env
            in
                teval e2 env'
            end
        | _ => raise UnknownType
