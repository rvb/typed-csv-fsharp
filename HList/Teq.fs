namespace HList

//Teqs, so we can do the GADT trick
type Teq<'a,'b> =
    private Refl of (('a -> 'b) * ('b -> 'a)) //Technically Iso, but whatever.

module Teq =
    let refl<'a> : Teq<'a,'a> = Refl (id, id)

    let cast<'a, 'b> (Refl (toB, toA)): 'a -> 'b =
        toB

    let sym<'a,'b> (Refl (ab, ba): Teq<'a,'b>) : Teq<'b,'a> =
        Refl (ba, ab)