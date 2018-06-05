namespace HList

open System
open System.Text.RegularExpressions

type 'a Parser = string -> 'a option

//So.. can we write strongly-typed versions of the usual CSV stuff?
//My answer: Maybe.
//Step 1: Define a schema as a full-header thing, so we can use MattWK's 'a -> 'b -> 'c trick.
//The crate here is mainly to wrap up that 'a = 'c -> 'b, and we have a 'b Schema.
//Furthermore, by fixing the 'c in each constructor, we can 'peel off' a single layer at a time,
//using the Teq to retrieve its type.
type 'a CSVSchema =
    | SNil of Teq<'a, unit>
    | SInt of string*SchemaCrate<'a, int>
    | SFloat of string*SchemaCrate<'a, float>
    | SString of string*SchemaCrate<'a, string>
    | SBool of string*SchemaCrate<'a, bool>
and SchemaCrate<'a, 'b> =
    abstract member Apply<'r> : SchemaCrateEvaluator<'a, 'b, 'r> -> 'r
and SchemaCrateEvaluator<'a, 'b, 'r> =
    abstract member Eval<'c> : Teq<'a, 'b -> 'c> -> CSVSchema<'c> -> 'r

type CSVSchemaCrate =
    abstract member Apply<'r> : CSVSchemaEvaluator<'r> -> 'r
and CSVSchemaEvaluator<'r> =
    abstract member Eval<'a> : CSVSchema<'a> -> 'r

module CSVSchema =
    let empty : CSVSchema<unit> =
        SNil Teq.refl

    let private cons (n: string) (r: CSVSchema<'b>) (c: string*SchemaCrate<'a -> 'b, 'a> -> CSVSchema<'a -> 'b>): CSVSchema<'a -> 'b> =
        let crate =
            { new SchemaCrate<'a -> 'b, 'a> with
                member __.Apply evaler =
                    evaler.Eval Teq.refl r
            }
        c (n, crate)

    let cInt (n: string) (r: CSVSchema<'a>): CSVSchema<int -> 'a> =
        cons n r SInt

    let cFloat (n: string) (r: CSVSchema<'a>): CSVSchema<float -> 'a> =
        cons n r SFloat

    let cString (n: string) (r: CSVSchema<'a>): CSVSchema<string -> 'a> =
        cons n r SString

    let cBool (n: string) (r: CSVSchema<'a>): CSVSchema<bool -> 'a> =
        cons n r SBool


    let private wrap<'a> (s: CSVSchema<'a>): CSVSchemaCrate =
            { new CSVSchemaCrate with
                member __.Apply e =
                    e.Eval s
            }        
    let rec private parserInner (input: string list) : CSVSchemaCrate option =
        match input with
        | [] ->
            wrap (SNil Teq.refl)
            |> Some
        | p :: ps ->
            let m = Regex.Match(p, @"\s*(?<name>[a-zA-Z_]+)[[]\s*(?<type>int|float|bool|string)\s*[]]\s*")
            if m.Success then
                parserInner ps
                |> Option.map (fun c ->
                    c.Apply { new CSVSchemaEvaluator<CSVSchemaCrate> with
                        member __.Eval<'a> (s: CSVSchema<'a>) : CSVSchemaCrate =
                            let name = m.Groups.["name"].Value
                            match m.Groups.["type"].Value with
                            | "int" -> cInt name s |> wrap
                            | "float" -> cFloat name s |> wrap
                            | "bool" -> cBool name s |> wrap
                            | "string" -> cString name s |> wrap
                            | _ -> failwithf "Unrecognised type: %s" m.Groups.["type"].Value
                        })
            else
                None

    let parse (input: string) : CSVSchemaCrate option =
        input.Split(',')
        |> List.ofArray
        |> parserInner

type 'a CSVRow = 'a HList

module Parsing =
    let rec parserInner<'a> (schema: CSVSchema<'a>) (parts: string list): CSVRow<'a> option =
        let recurse (v: 'b) (c: SchemaCrate<'a, 'b>) (ps: string list) : CSVRow<'a> option =
            c.Apply {new SchemaCrateEvaluator<'a, 'b, CSVRow<'a> option> with
                member __.Eval<'c> (teq: Teq<'a, 'b -> 'c>) (tail: CSVSchema<'c>): CSVRow<'a> option =
                    let recval = parserInner tail ps
                    recval
                    |> Option.map (fun t ->
                        let hlt =
                            teq
                            |> Teq.sym
                            |> Cong.hList
                        let res = HList.cons v t
                        Teq.cast hlt res)
            }
        let parseAndRecurse (parser: string -> bool*'b) (c: SchemaCrate<'a,'b>) (p: string) (ps: string list) : CSVRow<'a> option =
            let ok, v = parser p
            if ok then
                recurse v c ps
            else
                None
        match schema, parts with
        | SNil teq, [] ->
            Some <| Teq.cast (Teq.sym <| Cong.hList teq) HList.empty
        | SInt (_, c), p :: ps ->
            parseAndRecurse Int32.TryParse c p ps
        | SFloat (_, c), p :: ps ->
            parseAndRecurse Double.TryParse c p ps
        | SBool (_, c), p :: ps ->
            parseAndRecurse Boolean.TryParse c p ps
        | SString (_, c), p :: ps ->
            let m = Regex.Match(p,@"\s*[""](?<content>[^""]*)[""]\s*")
            parseAndRecurse (fun _ -> m.Success, if m.Success then m.Groups.["content"].Value else "") c p ps
        | _, _ -> None

    let parser (schema: 'a CSVSchema) (input: string): 'a CSVRow option =
        input.Split(',')
        |> List.ofArray
        |> parserInner schema

type Getter<'a, 'b> = HList<'a> -> 'b

type 'a Getters =
    {
        Ints: Map<string, Getter<'a,int>>
        Floats: Map<string, Getter<'a,float>>
        Bools: Map<string, Getter<'a,bool>>
        Strings: Map<string, Getter<'a,string>>
    }

module Indexing =
    let private really_believe_me (t: Teq<'a,'b>) : Teq<'c,'d> =
        box t |> unbox

    let congGetter (t: Teq<'a, 'b>) : Teq<Getters<'a>, Getters<'b>> =
        really_believe_me (Teq.refl: Teq<Getters<'a>,Getters<'a>>)

    let private lift (g: Getters<'a>) : Getters<'b -> 'a> =
        let liftOne (g: Getter<'a, 'c>): Getter<'b -> 'a, 'c> =
            HList.tail >> g
        {
            Ints = g.Ints |> Map.map (fun _ -> liftOne)
            Floats = g.Floats |> Map.map (fun _ -> liftOne)
            Bools = g.Bools |> Map.map (fun _ -> liftOne)
            Strings = g.Strings |> Map.map (fun _ -> liftOne)
        }

    let rec private recurse<'a, 'b> (adder: (HList<'a> -> 'b) -> Getters<'a> -> Getters<'a>) (c: SchemaCrate<'a,'b>) =
        c.Apply { new SchemaCrateEvaluator<'a, 'b, Getters<'a>> with
            member __.Eval<'c> teq (tail: CSVSchema<'c>) : Getters<'a> =
                let here (hl: HList<'a>) =
                    Teq.cast (Cong.hList teq) hl
                    |> HList.head
                let there : Getters<'a> =
                    getters tail
                    |> lift
                    |> Teq.cast (teq |> congGetter |> Teq.sym)
                adder here there
        }
    and getters<'a> (schema: CSVSchema<'a>) : Getters<'a> =
        match schema with
        | SNil _ ->
            {
                Ints = Map.empty
                Floats = Map.empty
                Bools = Map.empty
                Strings = Map.empty
            }
        | SInt (n, c) ->
            recurse (fun here there -> {there with Ints = Map.add n here there.Ints}) c
        | SFloat (n, c) ->
            recurse (fun here there -> {there with Floats = Map.add n here there.Floats}) c
        | SBool (n, c) ->
            recurse (fun here there -> {there with Bools = Map.add n here there.Bools}) c
        | SString (n, c) ->
            recurse (fun here there -> {there with Strings = Map.add n here there.Strings}) c