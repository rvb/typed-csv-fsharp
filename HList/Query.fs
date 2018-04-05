namespace HList

//Strongly-typed query language for schemas.
//The main idea here is to use a nameless representation, so
//we can tie the query to the schema.
//The below is just a proof-of-concept GADT language.
//We can add arithmetic pretty naturally, handle more operators, that kind of thing.
type Query<'a, 'r> =
    | Var of Getter<'a,'r>
    | Const of 'r
    | LessI of Teq<'r,bool>*Query<'a,int>*Query<'a,int>
    | LessF of Teq<'r,bool>*Query<'a,float>*Query<'a,float>
    | EqI of Teq<'r,bool>*Query<'a,int>*Query<'a,int>
    | EqS of Teq<'r,bool>*Query<'a,string>*Query<'a,string>

module Query =
    let rec eval<'a,'r> (q: Query<'a, 'r>) (r: CSVRow<'a>) : 'r =
        match q with
        | Var getter -> getter r
        | Const c -> c
        | LessI (teq, left, right) ->
            Teq.cast (Teq.sym teq) (eval left r < eval right r)
        | LessF (teq, left, right) ->
            Teq.cast (Teq.sym teq) (eval left r < eval right r)
        | EqI (teq, left, right) ->
            Teq.cast (Teq.sym teq) (eval left r = eval right r)
        | EqS (teq, left, right) ->
            Teq.cast (Teq.sym teq) (eval left r = eval right r)