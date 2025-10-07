datatype Constants = Constants(ids: seq<nat>){
    ghost predicate ValidIdx(i:nat){
        i < |ids|
    }

    ghost predicate WellFormed(){
        1 < |ids|
    }
    ghost predicate UniqueIds(){
        forall i, j | 
        && 0 <= i < |ids|
        && 0<= j < |ids| 
        && ids[i] == ids[j] :: i == j
    }
    ghost function getNextID(actor:nat): nat {
        if actor == |ids|-1 then 0 else actor+1
    }
}

datatype Variables = Variables(max_seen: seq<int>) {
    ghost predicate WellFormed(c: Constants){
        && c.WellFormed()
        && |max_seen| == |c.ids|
    }
}

ghost predicate Init(c: Constants, v: Variables){
    && v.WellFormed(c)
    && c.UniqueIds()
    && forall i:nat | c.ValidIdx(i) :: v.max_seen[i] == -1
}

ghost function max(a:int, b:int) : (ret:int)
    ensures ret == a || ret == b
    ensures ret >= a && ret >= b 
{
    if a < b then b else a
}

ghost predicate Update(c:Constants, v:Variables, v': Variables, actor: nat){
    && c.ValidIdx(actor)
    && v.WellFormed(c)
    && var nextActor := c.getNextID(actor);
    && var msg := max(c.ids[actor], v.max_seen[actor]);
    && v'.max_seen == v.max_seen[nextActor := max(msg, v.max_seen[nextActor])]
}

datatype Step = UpdateStep(actor:nat)

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step:Step){
    match step 
        case UpdateStep(actor) => Update(c,v,v',actor)
}

ghost predicate Next(c:Constants, v:Variables, v':Variables){
    exists step:Step :: NextStep(c,v,v',step)
}

ghost predicate IsLeader(c:Constants, v:Variables, actor:nat){
    && c.ValidIdx(actor)
    && v.WellFormed(c)
    && v.max_seen[actor] == c.ids[actor]
}

ghost predicate Safety(c:Constants, v:Variables){
    // && v.WellFormed(c)
    && forall i: nat, j:nat | c.ValidIdx(i) && c.ValidIdx(j) && IsLeader(c,v,i) && IsLeader(c,v,j) :: i==j
}

ghost predicate InBetween(start:nat, mid:nat, end:nat){
    if start > end then
        mid > start || mid < end
    else  start < mid < end
}

ghost predicate ChordDominates(c:Constants, v:Variables){
    && v.WellFormed(c)
    && (forall start:nat, mid:nat, end:nat | 
        && c.ValidIdx(start) 
        && c.ValidIdx(mid)
        && c.ValidIdx(end)
        && v.max_seen[end] == c.ids[start]
        && InBetween(start, mid, end) 
            :: c.ids[mid] < c.ids[start]
        )
}

ghost predicate Inv(c:Constants, v:Variables){
    // && v.WellFormed(c)
    && Safety(c,v)  
    // && c.UniqueIds()
    && ChordDominates(c,v)
}

lemma InvImpliesSafety(c:Constants, v: Variables) 
    requires Inv(c, v)
    ensures Safety(c, v)
{   
}

lemma InitImpliesInv(c:Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
{
    assert v.WellFormed(c);
    assert c.UniqueIds();
  
}

lemma NextPreservesInv(c:Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{
    assert Inv(c,v');
}