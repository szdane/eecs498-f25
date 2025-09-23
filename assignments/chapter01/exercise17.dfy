//#title Fibo
//#desc Recursion challenge.

ghost function fibo(val:nat) : nat
{
/*{*/
  match val {
    case 0 => 0
    case 1 => 1
    case _ => fibo(val-1) + fibo(val-2)
  }
/*}*/
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(20) == 6765
{
}

