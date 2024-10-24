function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n-1) + fib(n-2)
}

// 0 1
// primo 0
// secondo 1
// next = primo + secondo
// primo = secondo
// secondo = next
method Fibonacci(n: nat) returns (secondTerm: nat)
  ensures secondTerm == fib(n)
{
  if (n == 0) {
    secondTerm := 0;
    return;
  }
  var i:nat := 1;
  var firstTerm := 0;
  secondTerm := 1;
  while i < n
    invariant 0 < i <= n;
    invariant secondTerm == fib(i)
    invariant firstTerm == fib(i-1)
  {
    firstTerm, secondTerm := secondTerm, firstTerm + secondTerm;
    i := i + 1;
  }
}