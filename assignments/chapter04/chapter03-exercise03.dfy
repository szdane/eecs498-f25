//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

datatype Constants = Constants(
/*{*/ // You define this ...
  clients:nat 
/*}*/
) {
  ghost predicate WellFormed() { true }
/*{*/
/*}*/
}

/*{*/
/*}*/

datatype Variables = Variables(
/*{*/ // You define this ...
    server: (bool, int), clientsHoldingLock: seq<bool>
/*}*/
) {
  ghost predicate WellFormed(c: Constants) {
/*{*/
    && c.WellFormed()
    && |clientsHoldingLock| == c.clients
/*}*/
  }
}

ghost predicate Init(c:Constants, v:Variables) {
  && v.WellFormed(c)
/*{*/
  && v.server == (true, -1) 
  && forall i:nat | i < |v.clientsHoldingLock| :: v.clientsHoldingLock[i] == false
/*}*/
}

/*{*/
ghost predicate Acquire(c:Constants, v:Variables, v':Variables, clientIndex:nat)
  // requires clientIndex < c.clients
{
  && clientIndex < c.clients
  && v.WellFormed(c)
  && v'.WellFormed(c)
  && v.server == (true, -1)
  && v'.server == (false, clientIndex)
  && v'.clientsHoldingLock == v.clientsHoldingLock[clientIndex := true]
}

ghost predicate Release(c:Constants, v:Variables, v':Variables, clientIndex:nat)
  // requires clientIndex < c.clients
{
  && clientIndex < c.clients
  && v.WellFormed(c)
  && v'.WellFormed(c)
  && v.server == (false, clientIndex)
  && v'.server == (true, -1)
  && v'.clientsHoldingLock == v.clientsHoldingLock[clientIndex := false]
}
/*}*/
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
/*{*/
  | AcquireStep(clientIndex:nat)
  | ReleaseStep(clientIndex:nat)
/*}*/

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
/*{*/
  case AcquireStep(clientIndex) => Acquire(c, v, v', clientIndex)
  case ReleaseStep(clientIndex) => Release(c, v, v', clientIndex)
/*}*/
}

ghost predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(c:Constants, v:Variables) {
/*{*/
  && v.WellFormed(c)
  && (forall i:nat,j:nat | (i < |v.clientsHoldingLock|) && (j < |v.clientsHoldingLock|) && v.clientsHoldingLock[i] && v.clientsHoldingLock[j] :: i == j)
/*}*/
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(c: Constants, v: Variables, clientIndex: nat)
  requires v.WellFormed(c)
{
/*{*/
  && clientIndex < c.clients
  && clientIndex < |v.clientsHoldingLock|
  && v.clientsHoldingLock[clientIndex]
/*}*/
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (c: Constants, behavior:seq<Variables>)
    requires clientA == 2
    requires clientB == 0
    ensures 0 < |behavior|  // precondition for index operators below
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1]) // Behavior satisfies your state machine
    ensures forall i | 0 <= i < |behavior| :: Safety(c, behavior[i]) // Behavior always satisfies the Safety predicate
    ensures behavior[0].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[0], clientA)
    ensures behavior[|behavior|-1].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[|behavior|-1], clientB)
{
/*{*/
  c := Constants(3);
  // var v0 := Variables((true, -1),[false,false,false]);
  var v1 := Variables((false, clientA), [false, false, true]);
  var v2 := Variables((true, -1), [false, false, false]);
  var v3 := Variables((false, clientB), [true, false, false]);
  behavior := [v1, v2, v3];
  // assert c.clients > 0 ==> (v0.clientsHoldingLock[0] == false);
  assert |behavior[0].clientsHoldingLock| == c.clients;
  assert behavior[0].WellFormed(c);
  // assert behavior[0].server == (true, -1);
  // assert Init(c, behavior[0]);
  // assert Acquire(c, behavior[0], behavior[1], clientA);
  assert Release(c, behavior[0], behavior[1], clientA);
  assert Acquire(c, behavior[1], behavior[2], clientB);
  var step0 := AcquireStep(clientA);
  var step1 := ReleaseStep(clientA);
  var step2 := AcquireStep(clientB);
  // assert NextStep(c, behavior[0], behavior[1], step0);
  assert NextStep(c, behavior[0], behavior[1], step1);
  assert NextStep(c, behavior[1], behavior[2], step2);
  assert Safety(c, behavior[0]);
  assert Safety(c, behavior[1]);
/*}*/
}

