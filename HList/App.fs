namespace HList

open System.IO

//Currently, this runs a fixed query over the CSV.
//TODOs:
//- Define untyped query language and type checker
//- Write a parser for the untyped query language
//- Wire up parsing a query, type checking against the schema etc.
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
        let header = f.ReadLine()
        match CSVSchema.parse header with
        | None -> failwithf "Failed to parse header %s" header
        | Some c ->
            c.Apply { new CSVSchemaEvaluator<int> with
                member __.Eval<'a> (s: CSVSchema<'a>) : int =
                    //Hacky proof-of-concept query: check for prices less than 100.
                    let available = Indexing.getters s
                    if not <| Map.containsKey "price" available.Floats then
                        failwith "Proof of concept query requires a price column of type float."
                    let q = LessF (Teq.refl, Var (Map.find "price" available.Floats), Const 100.0)
                    getLines f
                    |> Seq.iteri (fun i l ->
                        match Parsing.parser s l with
                        | None -> failwithf "Could not parse row %s" l
                        | Some r ->
                            if Query.eval q r then
                                printfn "Row %d matches" i)
                    0
                }