namespace HList

open System

//Strongly-typed query language for schemas.
//The main idea here is to use a nameless representation, so
//we can tie the query to the schema.
//The below is just a proof-of-concept GADT language.
//We can add arithmetic pretty naturally, handle more operators, that kind of thing.
type Query<'a, 'r> =
    | Var of Getter<'a,'r>
    | Const of 'r
    | Less of Teq<'r,bool>*QueryPairCrate<'a>
    | Greater of Teq<'r,bool>*QueryPairCrate<'a>
    | Eq of Teq<'r,bool>*QueryPairCrate<'a>
    | Or of Teq<'r,bool>*Query<'a,bool>*Query<'a,bool>
    | And of Teq<'r,bool>*Query<'a,bool>*Query<'a,bool>
and QueryPairCrate<'a> = //An existential, exists b . Query<'a,'b>*Query<'a,'b>
    abstract member Apply : QueryPairCrateEvaluator<'a,'r> -> 'r
and QueryPairCrateEvaluator<'a,'r> =
    abstract member Eval<'b when 'b : comparison> : Query<'a,'b> -> Query<'a,'b> -> 'r

type UntypedQuery =
    | UVar of string
    | UConst of string
    | ULess of UntypedQuery*UntypedQuery
    | UGreater of UntypedQuery*UntypedQuery
    | UEq of UntypedQuery*UntypedQuery
    | UOr of UntypedQuery*UntypedQuery
    | UAnd of UntypedQuery*UntypedQuery

type QueryCrate<'a> =
    abstract member Apply: QueryCrateEvaluator<'a,'r> -> 'r
and QueryCrateEvaluator<'a,'r> =
    abstract member Eval<'b when 'b : comparison> : Query<'a,'b> -> 'r

module Query =
    let rec eval<'a,'r> (q: Query<'a, 'r>) (r: CSVRow<'a>) : 'r =
        match q with
        | Var getter -> getter r
        | Const c -> c
        | Less (teq, crate) ->
            crate.Apply { new QueryPairCrateEvaluator<_,'r> with
                member __.Eval<'b when 'b : comparison> (left: Query<'a,'b>) right =
                    Teq.cast (Teq.sym teq) (eval left r < eval right r)
            }
        | Greater (teq, crate) ->
            crate.Apply { new QueryPairCrateEvaluator<_,'r> with
                member __.Eval<'b when 'b : comparison> (left: Query<'a,'b>) right =
                    Teq.cast (Teq.sym teq) (eval left r > eval right r)
            }
        | Eq (teq, crate) ->
            crate.Apply { new QueryPairCrateEvaluator<_,'r> with
                member __.Eval<'b when 'b : comparison> (left: Query<'a,'b>) right =
                    Teq.cast (Teq.sym teq) (eval left r = eval right r)
            }
        | Or (teq, left, right) ->
            Teq.cast (Teq.sym teq) (eval left r || eval right r)
        | And (teq, left, right) ->
            Teq.cast (Teq.sym teq) (eval left r && eval right r)

    let cong<'a, 'b, 'c> (t: Teq<'b, 'c>) : Teq<Query<'a,'b>,Query<'a,'c>> =
        box Teq.refl<Query<'a,'b>> |> unbox

module QueryPairCrate =
    let make a b =
        { new QueryPairCrate<'a> with
            member __.Apply evaler =
                evaler.Eval a b
        }

type 'a Error = Result<'a, string>

module Result =
    let zip (ma: 'a Error) (mb: 'b Error): ('a * 'b) Error =
        ma
        |> Result.bind (fun a ->
            Result.map (fun b -> (a,b)) mb)

module Untyped =
    let private crate<'a, 'b when 'b : comparison> (q: Query<'a,'b>) : QueryCrate<'a> =
        { new QueryCrate<'a> with
            member __.Apply evaler = evaler.Eval q
        }

    let private wrap<'a, 'b when 'b : comparison> (g: Getter<'a,'b>) : QueryCrate<'a> =
        let q = Var g
        crate q

    let private maybe<'a> (f: string -> bool*'a) s: 'a Option =
        let ok, value = f s
        if ok then
            Some value
        else
            None

    //Build a query out of some subexpressions, asserting that 'c = 'd = 'e.
    //The caller is responsible for dynamically checking that.
    let private assertSubExprs<'a,'b,'c,'d> (constructor: Query<'a,'c> -> Query<'a,'c> -> Query<'a,'b> Error) (a: Query<'a,'c>) (b: Query<'a,'d>): Query<'a,'b> Error =
        let teqB: Teq<'d,'c> = Teq.refl<'c> |> unbox
        let qtB = Query.cong teqB
        constructor a (Teq.cast qtB b)

    //Within the type checker, we commonly have operators where we need to assert both sides have the same type, then
    //invoke some optional further checking based on that type.
    //To generalise that, we define this type of universally-quantified operator constructors that may fail.
    type private OpConstructor<'a,'c> =
        abstract member Apply<'b when 'b : comparison> : Query<'a,'b> -> Query<'a,'b> -> Query<'a,'c> Error

    //The type checker comes in two parts.
    //One checks operators, by recursively typechecking both sides, then comparing their types reflectively.
    //If the types match up, we invoke our operator-specific universally quantified check function.
    let rec private checkOp<'a,'c when 'c : comparison> (op: OpConstructor<'a,'c>) (getters: 'a Getters) (lhs: UntypedQuery) (rhs: UntypedQuery) : Query<'a,'c> Error =
        let maybeL = typecheck getters lhs
        let maybeR = typecheck getters rhs
        (maybeL, maybeR)
        ||> Result.zip
        |> Result.bind (fun (lCrate, rCrate) ->
            lCrate.Apply { new QueryCrateEvaluator<'a, _> with
                member __.Eval<'l when 'l : comparison> (qA: Query<'a,'l>) =
                    rCrate.Apply { new QueryCrateEvaluator<'a, _> with
                        member __.Eval<'r when 'r : comparison> (qB: Query<'a,'r>) =
                            if not <| typeof<'l>.Equals(typeof<'r>) then
                                sprintf "Type error: Left-hand side of operator has type %s, right-hand side has type %s." typeof<'l>.Name typeof<'r>.Name
                                |> Result.Error
                            else
                                (qA, qB)
                                ||> assertSubExprs (fun a b -> op.Apply a b)
                    }
            })
    //Part two checks constants, by attempting to parse them at the supported types and wrapping, and variables
    //by attempting to look them up.
    //It also constructs OpConstructors and calls checkOp.
    and typecheck<'a> (getters: 'a Getters) (q: UntypedQuery) : 'a QueryCrate Error =
        match q with
        | UVar n ->
            [
                Map.tryFind n getters.Ints |> Option.map wrap
                Map.tryFind n getters.Floats |> Option.map wrap
                Map.tryFind n getters.Bools |> Option.map wrap
                Map.tryFind n getters.Strings |> Option.map wrap
            ]
            |> List.tryPick id
            |> fun maybeV ->
                match maybeV with
                | None -> Result.Error (sprintf "Unbound variable %s" n)
                | Some v -> Result.Ok v
        | UConst s ->
            let quotedString (s: string) =
                if s.StartsWith("\"") && s.EndsWith("\"") then
                    true, s.Substring(1, s.Length - 2)
                else
                    false, ""
            [
                maybe Int32.TryParse s |> Option.map (Const >> crate)
                maybe Double.TryParse s |> Option.map (Const >> crate)
                maybe Boolean.TryParse s |> Option.map (Const >> crate)
                maybe quotedString s |> Option.map (Const >> crate)
            ]
            |> List.tryPick id
            |> fun maybeC ->
                match maybeC with
                | None -> Result.Error (sprintf "Could not parse constant %s" s)
                | Some c -> Result.Ok c
        | UEq (a, b) ->
            let cons =
                { new OpConstructor<'a,bool> with
                    member __.Apply<'b when 'b : comparison> (l: Query<'a,'b>) r =
                        Eq (Teq.refl, QueryPairCrate.make l r) |> Result.Ok
                }
            checkOp cons getters a b
            |> Result.map crate
        | ULess(a, b) ->
            let cons =
                { new OpConstructor<'a,bool> with
                    member __.Apply<'b when 'b : comparison> (l: Query<'a,'b>) r =
                        Less (Teq.refl, QueryPairCrate.make l r) |> Result.Ok
                }
            checkOp cons getters a b
            |> Result.map crate
        | UGreater(a, b) ->
            let cons =
                { new OpConstructor<'a,bool> with
                    member __.Apply<'b when 'b : comparison> (l : Query<'a,'b>) r =
                        Greater (Teq.refl, QueryPairCrate.make l r) |> Result.Ok
                }
            checkOp cons getters a b
            |> Result.map crate
        | UOr(a, b) ->
            let cons =
                { new OpConstructor<'a,bool> with
                    member __.Apply<'b when 'b : comparison> (l : Query<'a,'b>) r =
                        if typeof<'b>.Equals(typeof<bool>) then
                            Or (Teq.refl, unbox l, unbox r)
                            |> Result.Ok
                        else
                            sprintf "Type error: Or can only be applied to boolean queries, not to %s" typeof<'b>.Name
                            |> Result.Error
                }
            checkOp cons getters a b
            |> Result.map crate
        | UAnd(a, b) ->
            let cons =
                { new OpConstructor<'a,bool> with
                    member __.Apply<'b when 'b : comparison> (l : Query<'a,'b>) r =
                        if typeof<'b>.Equals(typeof<bool>) then
                            And (Teq.refl, unbox l, unbox r)
                            |> Result.Ok
                        else
                            sprintf "Type error: And can only be applied to boolean queries, not to %s" typeof<'b>.Name
                            |> Result.Error
                }
            checkOp cons getters a b
            |> Result.map crate