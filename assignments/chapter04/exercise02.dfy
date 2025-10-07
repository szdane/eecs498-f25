//#title Single-Server Lock Service Proof
//#desc A more realistic invariant proof of the previous chapter's lock
//#desc service.

// Copy your solution for chapter03/exercise03 into the current directory with
// this name:
include "chapter03-exercise03.dfy"
//#extract ../../chapter03-state-machines/exercises/exercise03.template solution chapter03-exercise03.dfy


/*{*/
/*}*/
ghost predicate Inv(c:Constants, v:Variables) {
/*{*/
   v.WellFormed(c) && (
    (v.server == (true, -1) &&
     (forall i:nat | i < |v.clientsHoldingLock| :: !v.clientsHoldingLock[i]))
    ||
    (!v.server.0 && 0 <= v.server.1 < c.clients &&
     (forall i:nat | i < |v.clientsHoldingLock| :: v.clientsHoldingLock[i] ==> i == v.server.1))
  )
  /*}*/
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(c:Constants, v:Variables, v':Variables)
  ensures Init(c, v) ==> Inv(c, v)
  ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
  ensures Inv(c, v) ==> Safety(c, v)
{
/*{*/
  assert Init(c, v) ==> Inv(c, v);
  assert forall i:nat | i<|v.clientsHoldingLock| :: Inv(c, v) && Release(c, v, v', i) ==> Inv(c, v');
  assert forall i:nat | i<|v.clientsHoldingLock| :: Inv(c, v) && Acquire(c, v, v', i) ==> Inv(c, v');
  // assert Inv(c, v) && Acquire(c, v, v', 0) ==> Inv(c, v');
  assert Inv(c, v) && Next(c, v, v') ==> Inv(c, v');
/*}*/
}
