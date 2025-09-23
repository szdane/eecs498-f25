//#title Binary Tree Search
//#desc Implement search in a binary tree and prove it works.
//#desc Practice with proof diagnosis.

include "exercise21.dfy"
//#extract exercise21.template solution exercise21.dfy

// This exercise builds on exercise21 (so make sure you have completed
// that one, too). If in doubt about your solution to exercise21, contact 
// an instructor during office hours to make sure you're on the right path. 

predicate SequenceIsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

lemma SortedTreeMeansSortedSequence(tree:Tree)
    requires IsSortedTree(tree)
    ensures SequenceIsSorted(TreeAsSequence(tree))
{
}

method FindInBinaryTree(tree:Tree, needle:int) returns (found:bool)
    requires IsSortedTree(tree)
    ensures found <==> needle in TreeAsSequence(tree)
{
/*{*/
    var found_l := false;
    var found_r := false;
    var found_m := false;
    if tree == Nil {
        assert needle !in TreeAsSequence(tree);
        return false;
    }
    else if tree.value == needle {
        // found_m := true;
        // assert found_m <==> needle in TreeAsSequence(tree);
        // assert needle in TreeAsSequence(tree) ==> found_m;
        return true;
    }
    else if tree.left == Nil && tree.right == Nil {
        assert needle !in TreeAsSequence(tree);
        return false;
    }
    // assert !found_m;
    else if needle < tree.value{
        if tree.left == Nil {
            SortedTreeMeansSortedSequence(tree.right);
            return false;
        }
        found_l := FindInBinaryTree(tree.left, needle);
        assert found_l <==> needle in TreeAsSequence(tree.left);
        assert SequenceIsSorted(TreeAsSequence(tree.right)) ==> needle !in TreeAsSequence(tree.right);
        // assert needle < TreeAsSequence(tree.right)[0] && IsSortedTree(tree) <==> !(needle in TreeAsSequence(tree.right));
        assert tree.value != needle;
        // assert found_l <==> needle in TreeAsSequence(tree);
        SortedTreeMeansSortedSequence(tree.right);
        return found_l;
    }
    else if needle > tree.value{
        if tree.right == Nil {
            assert SequenceIsSorted(TreeAsSequence(tree.left)) ==> needle !in TreeAsSequence(tree.left);
            // assert IsSortedTree(tree.left) ==> needle !in TreeAsSequence(tree.left);
            SortedTreeMeansSortedSequence(tree.left);
            assert IsSortedTree(tree) ==> SequenceIsSorted(TreeAsSequence(tree));
            assert SequenceIsSorted(TreeAsSequence(tree.left));
            assert needle !in TreeAsSequence(tree.left);
            return false;
        }
        found_r := FindInBinaryTree(tree.right, needle);
        assert found_r <==> needle in TreeAsSequence(tree.right);
        assert TreeAsSequence(tree) == TreeAsSequence(tree.left) + [tree.value] + TreeAsSequence(tree.right);
        assert needle in TreeAsSequence(tree.right) ==> needle in TreeAsSequence(tree);
        assert found_r ==> needle in TreeAsSequence(tree);
        assert !found_l;
        assert tree.value != needle;
        assert tree.left != Nil || tree.right != Nil;
        SortedTreeMeansSortedSequence(tree.left);
        // assert (!found_l && found_r && tree.value !=needle) <==> needle in TreeAsSequence(tree);
        return found_r;
    }

    // assert found_l || found_r || found_m <==> needle in TreeAsSequence(tree);
    // return found_l || found_r || found_m;

/*}*/
}
