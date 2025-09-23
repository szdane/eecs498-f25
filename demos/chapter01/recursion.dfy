function Evens(count:int) : (outseq:seq<int>)
  ensures forall idx :: 0<=idx<|outseq| ==> outseq[idx] == 2 * idx
  ensures |outseq| == count
{
  if count==0 
  then [] 
  else 
    Evens(count-1) + [2 * (count-1)]
}
