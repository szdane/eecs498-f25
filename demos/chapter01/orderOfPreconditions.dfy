predicate bar()

predicate foo(x: int) 
    requires bar()
{
    x > 5
}

predicate baz(x:int ) 
{
    && bar()
    && foo(x)
}

predicate IsMaxIndex(a:seq<int>, x:int) {
    && 0<= x < |a|
    && (forall i | 0 <= i < |a| :: a[i] <= a[x])
    // && 0 <= x < |a|
}
