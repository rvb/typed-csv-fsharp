namespace HList

type HList<'a> =
    | Nil of Teq<'a, unit>
    | Cons of ConsCrate<'a>
and ConsCrate<'a> =
    abstract member Apply: ConsCrateEvaluator<'a, 'r> -> 'r
and ConsCrateEvaluator<'a, 'r> =
    abstract member Eval<'b, 'c> : Teq<'a, 'b -> 'c> -> 'b -> HList<'c> -> 'r

module Cong =
    let private really_believe_me (t: Teq<'a,'b>) : Teq<'c,'d> =
        box t |> unbox

    let hList (t: Teq<'a, 'b>) : Teq<HList<'a>, HList<'b>> =
        really_believe_me Teq.refl<HList<'a>>

    let domain (t: Teq<'a -> 'b, 'c -> 'd>): Teq<'a, 'c> =
        really_believe_me Teq.refl<'a>

    let codomain (t: Teq<'a -> 'b, 'c -> 'd>): Teq<'b, 'd> =
        really_believe_me Teq.refl<'b>


module HList =
    let empty: HList<unit> =
        Nil Teq.refl

    let cons (head: 'a) (tail: HList<'b>): HList<'a -> 'b> =
        Cons { new ConsCrate<'a -> 'b> with
            member __.Apply evaler =
                evaler.Eval Teq.refl head tail
            }

    let head (l: HList<'a -> 'b>) : 'a =
        match l with
        | Nil _ -> failwith "Unreachable"
        | Cons c ->
            c.Apply {new ConsCrateEvaluator<'a -> 'b, 'a> with
                member __.Eval teq h _ =
                    let td =
                        teq
                        |> Cong.domain
                        |> Teq.sym
                    Teq.cast td h
            }

    let tail (l: HList<'a -> 'b>) : HList<'b> =
        match l with
        | Nil _ -> failwith "Unreachable"
        | Cons c ->
            c.Apply {new ConsCrateEvaluator<'a -> 'b, HList<'b>> with
                member __.Eval teq _ t =
                    Teq.cast (teq |> Cong.codomain |> Teq.sym |> Cong.hList) t
            }