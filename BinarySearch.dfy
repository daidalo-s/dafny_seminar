predicate sorted(A: array<int>)
  reads A
{
  forall j,k :: 0 <= j < k < A.Length ==> A[j] <= A[k]
}

method BinarySearch(A: array<int>, key : int) returns (index: int)
  requires sorted(A)
  ensures 0 <= index ==> index < A.Length && A[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < A.Length ==> A[k] != key
{
  var low, high := 0, A.Length;
  while (low < high)
    invariant 0 <= low <= high <= A.Length
    invariant forall i :: 0 <= i < A.Length && !(low <= i < high) ==> A[i] != key
  {
    var mid := (low + high) / 2;
    if (A[mid] < key) {
      low := mid + 1;
    } else if (key < A[mid]) {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}