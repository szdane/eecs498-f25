//#title IsSeqSorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsSeqSorted(intSeq:seq<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intSeq[..])
{
  /*{*/
  var count:nat := 0;
  if |intSeq| <= 1 {
    return true;
  }
  while (count < |intSeq| -1) 
  invariant 0 <= count < |intSeq|
  invariant forall i:nat,j:nat | i<j<=count :: intSeq[i] <= intSeq[j]
  {
    if (intSeq[count] > intSeq[count+1]) {
      return false;
    }
    count := count + 1;
  }
  return true;
  /*}*/
}
