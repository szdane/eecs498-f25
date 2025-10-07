datatype Variables = Variables(y:int, isGoingNorth: bool)

predicate Init(v: Variables){
    && v.y == 5
    && v.isGoingNorth
}

predicate MoveNorth(v:Variables, v':Variables){
    && v.isGoingNorth
    && v' == v.(y := v.y + 1)
}

predicate MoveSouth(v:Variables, v':Variables){
    && !v.isGoingNorth
    && v' == v.(y := v.y - 1)
}

predicate Flip(v:Variables, v':Variables){
    && v'.y + v.y == 0
    && v'.isGoingNorth != v.isGoingNorth
}

predicate Next(v:Variables, v':Variables){
    || MoveNorth(v, v')
    || MoveSouth(v, v')
    || Flip(v, v')
}

predicate Safety(v:Variables){
    && v.y*v.y > 9
}

predicate Inv(v:Variables){
    (v.y >= 5 && v.isGoingNorth) || (v.y <= -5 && !v.isGoingNorth)
}
lemma InvImpliesSafety(v:Variables)
    requires Inv(v)
    ensures Safety(v)
{
}

lemma InitImpliesInv(v:Variables)
    requires Init(v)
    ensures Inv(v)
{

}

lemma NextMaintainsInv(v:Variables, v':Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
{

}