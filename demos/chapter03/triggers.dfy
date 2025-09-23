predicate P(x: int)
predicate Q(x: int)
predicate R(x: int)
// it only learns for forall when there is a trigger
lemma foo() 
    requires forall x{:trigger P(x)} :: P(x) && Q(x) && R(x)
    ensures R(0)
    {
        // assert P(0);
        var x := P(0); // it doesn't have to be true, you just have to mention it
    }