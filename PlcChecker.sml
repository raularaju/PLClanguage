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


fun teval (e: expr) (env: plcType env) : plcType = 
    case e of 
        Var x => lookup env x
        | Prim1(opr, e1) =>
            let val t1 = teval e1 env
            in
                case (opr, t1) of
                    ("print", _) => ListT []
                    | _ => raise UnknownType
            end
        | Prim2(opr, e1, e2) =>
            let
                val t1 = teval e1 env
                val t2 = teval e2 env
            in
                case (opr, t1, t2) of
                 ("*", IntT, IntT) => IntT
                | ("/", IntT, ListT _) => IntT
                | ("+", IntT, ListT _) => IntT
                | ("-", IntT, ListT _) => IntT
                | (";", _, _ ) => t2
                | _ => raise UnknownType
            end
        | Let(x, e1, e2) =>
            let
                val t = teval e1 env
                val env' = (x,t) :: env
            in
                teval e2 env'
            end

        | _ => raise UnknownType
