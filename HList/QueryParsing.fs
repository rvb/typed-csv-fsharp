namespace HList

open FParsec

type 'a QParser = Parser<'a,unit>

module QueryParsers =
    let variable : UntypedQuery QParser =
        regex @"[a-zA-Z_][a-zA-Z0-9_]*"
        .>> spaces
        |>> UVar

    let number : string QParser =
        regex @"[+-]?[0-9]+\.?[0-9]*"

    let bool : string QParser =
        regex "true|false"

    let string : string QParser =
        regex @"""[^""]*"""

    let constant : UntypedQuery QParser =
        (number <|> bool <|> string)
        .>> spaces
        |>> UConst

    let cmp : UntypedQuery QParser =
        variable
        .>>. (anyOf "=<>" .>> spaces)
        .>>. constant
        |>> fun ((l, op), r) ->
            if op = '=' then
                UEq (l,r)
            elif op = '<' then
                ULess (l,r)
            else
                UGreater (l,r)

    let query : UntypedQuery QParser =
        let andExpr, andExprRef = FParsec.Primitives.createParserForwardedToRef ()
        let orExpr, orExprRef = FParsec.Primitives.createParserForwardedToRef ()
        andExprRef := chainl1 orExpr (pstring "&&" .>> spaces >>% fun l r -> UAnd (l,r))
        let singleOrExpr = cmp <|> (between (pchar '(' .>> spaces) (pchar ')' .>> spaces) andExpr)
        orExprRef :=
            chainl1 singleOrExpr (pstring "||" .>> spaces >>% fun l r -> UOr (l,r))
        andExpr