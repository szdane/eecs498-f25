datatype Card = Shelf | Patron(name: string)
datatype Book = Book(title: string)
type Variables = map<Book, Card>    // our Library state

ghost predicate Init(v: Variables) {
  forall book | book in v :: v[book] == Shelf
}

ghost predicate CheckOut(v:Variables, v':Variables, book:Book, patron:string) {
  && book in v
  && v[book] == Shelf
  && (forall book | book in v :: v[book] != Patron(patron))
  && v' == v[book := Patron(patron)]
}

ghost predicate CheckIn(v:Variables, v':Variables, book:Book, patron:string) {
  && book in v
  && v[book] == Patron(patron)
  && v' == v[book := Shelf]
}

ghost predicate CheckInVerse(v:Variables, v':Variables, book:Book, patron:string){
  CheckOut(v', v, book, patron)
}

ghost predicate Next(v:Variables, v':Variables) {
  || (exists book, patron :: CheckInVerse(v, v', book, patron))
  || (exists book, patron :: CheckOut(v, v', book, patron))
}

ghost predicate Safety(v:Variables) {
  forall book1, book2 |
  && book1 in v 
  && book2 in v 
  && !v[book1].Shelf?
  && !v[book2].Shelf? 
  && v[book1] == v[book2] 
  :: book1 == book2
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Safety(v)
  ensures forall v, v' | Safety(v) && Next(v, v') :: Safety(v')
{
  forall v:Variables, v':Variables | Safety(v) && Next(v,v') ensures Safety(v') {
    forall book1, book2 |
    && book1 in v' 
    && book2 in v' 
    && !v'[book1].Shelf?
    && !v'[book2].Shelf? 
    && v'[book1] == v'[book2]
    ensures book1 == book2 
    // {
    //   if exists book, patron :: CheckIn(v, v', book, patron){
    //     assert book1 == book2;
    //   }
    //   else if exists book, patron:: CheckOut(v, v', book, patron){
    //     assert book1 == book2;
    //   }
    // }
    {assert book1 in v;
    assert book2 in v;} // we need the safety of v for book1 in v' ensures safety of v' but doesnt help in this case
  }
}