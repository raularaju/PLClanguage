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
exception OpNonList

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
        | ESeq _ => raise EmptySeq
        | Letrec (f, t1, x, t2, e1, e2) =>
            let
                val env' = (f, FunT (t1, t2)) :: env
                val env'' = (x, t1) :: env'
                val t3 = teval e1 env''
            in
                if t2 = t3 then
                    teval e2 env'
                else
                    raise WrongRetType
            end
        | If (e1, e2, e3) =>
            let
                val t1 = teval e1 env
                val t2 = teval e2 env
                val t3 = teval e3 env
            in
                if t1 = BoolT then
                    if t2 = t3 then
                        t2
                    else
                        raise DiffBrTypes
                else
                    raise IfCondNotBool
            end
        | Match (e, l) =>
            let 
                val t1 = teval e env
                fun areAllCondTypesMatchSame (l: (expr option * expr) list) (t1: plcType) (env: plcType env) : bool =
                    case l of 
                        [] => true
                        | (NONE , _) :: tl => areAllCondTypesMatchSame tl t1 env
                        | (SOME e, _) :: tl => 
                            let val t = teval e env
                            in
                                if t = t1 then areAllCondTypesMatchSame tl t1 env else false
                            end                 
                fun areAllRetuTypesMatchSame (l: (expr option * expr) list) (env: plcType env): bool =
                    case l of 
                        [] => true   
                        | (_, _) :: [] => true                          
                        | (_, e1) :: (ec, e2) ::tl => 
                            let val t1 = teval e1 env
                                val t2 = teval e2 env
                            in
                                if t1 = t2 then areAllRetuTypesMatchSame (( ec, e2) :: tl) env else false 
                            end
            in 
            case l of 
                [] => raise NoMatchResults
                | _ =>  if areAllCondTypesMatchSame l t1 env then
                            if areAllRetuTypesMatchSame l env then
                                let 
                                    val (_, er) = hd l
                                in
                                    teval er env
                                end
                            else
                                raise MatchResTypeDiff
                        else
                            raise MatchCondTypesDiff
            end 
        | Anon(s, x, e) => 
            let 
                val t = teval e ((x,s) :: env)
            in
                FunT (s, t)
            end
        | Call(e2, e1) =>
            let
                val t1 = teval e1 env
                val t2 = teval e2 env
            in
                case t2 of
                    FunT (t1', t2') => if t1 = t1' then t2' else raise CallTypeMisM
                    | _ => raise NotFunc
            end
        | Prim1(opr, e1) =>
            let val t1 = teval e1 env
            in
                case (opr, t1) of
                    ("print", _) => ListT []
                    | ("-", IntT) => IntT
                    | ("!", BoolT) => BoolT
                    | ("hd", SeqT t) => t
                    | ("tl", SeqT t) => t1
                    | ("ise", SeqT _) => BoolT
                    | _ => raise UnknownType
            end
        | Prim2(opr, e1, e2) =>
            let
                val t1 = teval e1 env
                val t2 = teval e2 env
            in
                case (opr, t1, t2) of
                  ("+", IntT, IntT) => IntT
                | ("-", IntT, IntT) => IntT
                | ("*", IntT, IntT) => IntT
                | ("/", IntT, IntT) => IntT
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
                    ListT types =>  if 0 < i andalso i <= List.length types then List.nth(types, i - 1) else raise ListOutOfRange
                    | _ => raise OpNonList
            end
        | Let(x, e1, e2) =>
            let
                val t1 = teval e1 env
                val env' = (x,t1) :: env
            in
                teval e2 env'
            end

