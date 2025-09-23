//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

include "UtilitiesLibrary.dfy"
import opened UtilitiesLibrary

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

/*{*/
// you should define your Tree datatype here.
datatype Tree = Node(value:int, left:Tree, right:Tree) | Nil
/*}*/

// This lemma is here to guide you in defining the tree in a way
// that will help with the rest of the exercise.
lemma DatatypeCheck()
{
  var emptyTree := Nil;
  var littleTree := Node(9, Nil, Nil);
  var biggerTree := Node(10, littleTree, littleTree); // Note: not sorted
}

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// Note: a function method is just like a ghostfunction, except it
// can be used in an "imperative" context (i.e., inside a method)

ghost function TreeAsSequence(tree:Tree) : seq<int>
{
/*{*/  
    match tree{
      case Nil => []
      case Node(value, left, right) => TreeAsSequence(left) + [value] + TreeAsSequence(right)
    }  
/*}*/
}

// If this predicate is true about sorted sequences, then everything
// in seq1 is <= everything in seq2.
ghost predicate SequencesOrderedAtInterface(seq1:seq<int>, seq2:seq<int>)
{
  if |seq1|==0 || |seq2|==0
  then true
  else Last(seq1) <= seq2[0]
}

// Write a recursive definition for what it means for a Tree to be sorted
ghost predicate IsSortedTree(tree:Tree) {
/*{*/
    match tree {
      case Nil => true
      case Node(value, Nil, Nil) => true
      case Node(value, left, right) =>
        IsSortedTree(left) &&
        IsSortedTree(right) &&
        SequencesOrderedAtInterface(TreeAsSequence(left), [value]) &&
        SequencesOrderedAtInterface([value], TreeAsSequence(right))
    }
/*}*/
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

datatype TreeSortedness = Unsorted | Empty | Bounded(low: int, high: int)

// Write a recursive implementation that checks if a tree
// is sorted by checking the children, then using TreeAsSequence
// on the children to confirm that both children stay on their
// respective sides of the pivot.
method CheckIfSortedTree(tree:Tree) returns (out: TreeSortedness)
    ensures IsSortedTree(tree) <==> !out.Unsorted?
  /*{*/
    ensures tree == Nil <==> out == Empty
    ensures IsSortedTree(tree) && tree != Nil <==> 
            exists low:int, high:int :: out == Bounded(low, high) &&
            low <= high &&
            low == TreeAsSequence(tree)[0] &&
            high == Last(TreeAsSequence(tree))
  /*}*/
{
  /*{*/
  if tree == Nil{
    return Empty;
  }
  var leftSorted := CheckIfSortedTree(tree.left);
  var rightSorted := CheckIfSortedTree(tree.right);
  if leftSorted.Unsorted? || rightSorted.Unsorted?{
    return Unsorted;
  }
  if leftSorted == Empty && rightSorted == Empty{
    return Bounded(tree.value, tree.value);
  }
  if leftSorted == Empty{
    var Bounded(rLow, rHigh) := rightSorted;
    if tree.value <= rLow{
      return Bounded(tree.value, rHigh);
    } else {
      return Unsorted;
    }
  }
  if rightSorted == Empty{
    var Bounded(lLow, lHigh) := leftSorted;
    if lHigh <= tree.value{
      return Bounded(lLow, tree.value);
    } else {
      return Unsorted;
    }
  }
  else {
    var Bounded(lLow, lHigh) := leftSorted;
    var Bounded(rLow, rHigh) := rightSorted;
    if lHigh <= tree.value && tree.value <= rLow{
      return Bounded(lLow, rHigh);
    } else {
      return Unsorted;
    }
  }
  return Empty;
  /*}*/
}






