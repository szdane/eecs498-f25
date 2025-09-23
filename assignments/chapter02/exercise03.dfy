//#title Merge Sort
//#desc More specification practice.

// Implement a merge sort that guarantees the result is sorted.
// merge() should merge its two sorted inputs into a sorted output.
// merge_sort picks a pivot, recursively merge_sort()s the subsequences,
// and then uses merge() to put them back together. We've provided
// signatures for merge and merge_sort to get you started.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

/*{*/
/*}*/
method merge_sort(input:seq<int>) returns (output:seq<int>)
/*{*/
  ensures IsSorted(output)
  ensures |output| == |input|
  decreases |input|
  ensures multiset(output) == multiset(input)
/*}*/
{
/*{*/
  if |input| <= 1 {
    output := input;
    return;
  }
  var mid := |input| / 2;
  var left := input[0..mid];
  var right := input[mid..|input|];
  var sorted_left := merge_sort(left);
  var sorted_right := merge_sort(right);
  assert multiset(sorted_left) == multiset(left);
  assert multiset(sorted_right) == multiset(right);
  output := merge(sorted_left, sorted_right);
  assert multiset(output) == multiset(sorted_left) + multiset(sorted_right);
  assert input == left + right;
  assert multiset(input) == multiset(left) + multiset(right);
  assert multiset(input) == multiset(sorted_left) + multiset(sorted_right);
/*}*/
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
/*{*/
  decreases |seqa| 
  decreases |seqb|
  ensures IsSorted(output)
  ensures |output| == |seqa| + |seqb|
  ensures multiset(output) == multiset(seqa) + multiset(seqb)
/*}*/
{
/*{*/
  var i, j := 0, 0;
  if |seqa| == 0 {
    output := seqb;
    return;
  }
  if |seqb| == 0 {
    output := seqa;
    return;
  }
  output := [];
  // while i < |seqa| && j < |seqb|
  //   invariant 0 <= i <= |seqa|
  //   invariant 0 <= j <= |seqb|
  //   invariant |output| == i + j
  //   invariant IsSorted(output)
  //   invariant i < |seqa| ==> (|output| == 0 || output[|output|-1] <= seqa[i])
  //   invariant j < |seqb| ==> (|output| == 0 || output[|output|-1] <= seqb[j])
  //   decreases (|seqa| - i) + (|seqb| - j)
  //   invariant multiset(output) + multiset(seqa[i..]) + multiset(seqb[j..])
  //             == multiset(seqa) + multiset(seqb)
  // {
  //   if seqa[i] <= seqb[j] {
  //     output := output + [seqa[i]];
  //     assert seqa[i] in output;
  //     assert seqa[i..] == [seqa[i]] + seqa[i+1..];
  //     i := i + 1;
  //   } else {
  //     output := output + [seqb[j]];
  //     assert seqb[j] in output;
  //     assert seqb[j..] == [seqb[j]] + seqb[j+1..];
  //     j := j + 1;
  //   }
  // }

  // if j < |seqb| {
  //   while j < |seqb|
  //     invariant 0 <= i <= |seqa|
  //     invariant 0 <= j <= |seqb|
  //     invariant |output| == i + j
  //     invariant IsSorted(output)
  //     invariant IsSorted(seqb)
  //     invariant j < |seqb| ==> (|output| == 0 || output[|output|-1] <= seqb[j])
  //     invariant multiset(output) + multiset(seqa[i..]) + multiset(seqb[j..])
  //               == multiset(seqa) + multiset(seqb)
  //     decreases |seqb| - j
  //     {
  //       output := output + [seqb[j]];
  //       assert seqb[j..] == [seqb[j]] + seqb[j+1..];
  //       assert seqb[j] in output;
  //       j := j + 1;
  //     }
  // }
  
  // while i < |seqa|
  //   invariant 0 <= i <= |seqa|
  //   invariant 0 <= j <= |seqb|
  //   invariant |output| == i + j
  //   invariant IsSorted(output)
  //   invariant  multiset(output) + multiset(seqa[i..]) + multiset(seqb[j..])
  //             == multiset(seqa) + multiset(seqb)
  //   invariant (i < |seqa| && |seqa| > 0)  ==> (|output| == 0 || output[|output|-1] <= seqa[i])
  //   decreases |seqa| - i
  // {
  //   output := output + [seqa[i]];
  //   assert seqa[i] in output;
  //   assert seqa[i..] == [seqa[i]] + seqa[i+1..];
  //   i := i + 1;
  // }
  // assert IsSorted(seqb);
  while i < |seqa| || j < |seqb|
    invariant 0 <= i <= |seqa|
    invariant 0 <= j <= |seqb|
    invariant |output| == i + j
    invariant IsSorted(output)
    invariant (i < |seqa| && |output| > 0) ==> output[|output|-1] <= seqa[i]
    invariant (j < |seqb| && |output| > 0) ==> output[|output|-1] <= seqb[j]
    invariant  multiset(output) + multiset(seqa[i..]) + multiset(seqb[j..])
              == multiset(seqa) + multiset(seqb)
    decreases |seqa| + |seqb| - (i + j)
{
    if i < |seqa| && (j >= |seqb| || seqa[i] <= seqb[j]) {
        output := output + [seqa[i]];
        assert seqa[i..] == [seqa[i]] + seqa[i+1..];
        i := i + 1;
    } else {
        output := output + [seqb[j]];
        assert seqb[j..] == [seqb[j]] + seqb[j+1..];
        j := j + 1;
    }
  }
  
/*}*/
}

