namespace HList

open FParsec.CharParsers

open System.IO

module App =
    let getLines (f: StreamReader) =
        seq {
            let mutable l = f.ReadLine()
            while l <> null do
                yield l
                l <- f.ReadLine()
        }

    [<EntryPoint>]
    let main args =
        let f = System.IO.File.OpenText args.[0]
        let query = args.[1]
        let header = f.ReadLine()
        match CSVSchema.parse header with
        | None -> failwithf "Failed to parse header %s" header
        | Some c ->
            c.Apply { new CSVSchemaEvaluator<int> with
                member __.Eval<'a> (s: CSVSchema<'a>) : int =
                    match runParserOnString QueryParsers.query () "query" query with
                    | Failure (errorStr, _, _) ->
                        eprintfn "Could not parse query: %s" errorStr
                        1
                    | Success (query, _, _) ->
                        printfn "%s" header
                        let available = Indexing.getters s
                        match Untyped.typecheck available query with
                        | Error err -> failwithf "Error type-checking query: %s" err
                        | Ok q ->
                            q.Apply { new QueryCrateEvaluator<'a, int> with
                                member __.Eval<'b when 'b : comparison> (q: Query<'a,'b>) =
                                    if not <| typeof<'b>.Equals(typeof<bool>) then
                                        failwithf "Type error: A query should be a boolean expression."
                                    let (t: Teq<'b, bool>) = Teq.refl<bool> |> unbox
                                    let q = q |> Teq.cast (Query.cong t)
                                    getLines f
                                    |> Seq.iter (fun l ->
                                        match Parsing.parser s l with
                                        | None -> failwithf "Could not parse row %s" l
                                        | Some r ->
                                            if Query.eval q r then
                                                printfn "%s" l)
                                    0
                            }
                }