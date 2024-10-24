class TreeNode {
  var data: int
  var left: TreeNode?
  var right: TreeNode?

  ghost var Repr : set<object>
  ghost var Contents : set<int>

  ghost predicate Valid()
    reads Repr, this
  {
    this in Repr &&
    (left != null ==>
       left in Repr &&
       left.Repr <= Repr && this !in left.Repr &&
       (forall e :: e in left.Contents ==> e < data) &&
       left.Valid()) &&
    (right != null ==>
       right in Repr &&
       right.Repr <= Repr && this !in right.Repr &&
       (forall e :: e in right.Contents ==> data < e) &&
       right.Valid())
    && (left != null && right != null ==> left.Repr !! right.Repr) &&
    Contents == (if left == null then {} else left.Contents) +
    (if right == null then {} else right.Contents) +
    {data}
  }

  constructor (x: int)
    ensures fresh(Repr - {this})
    ensures Valid()
    ensures Contents == {x}
  {
    data := x;
    left := null;
    right := null;
    Repr := {this};
    Contents := {data};
  }

  method Insert(x: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + {x}
    decreases Repr
  {
    if x == data {
      return;
    }
    if x < data {
      if left == null {
        left := new TreeNode(x);
      } else {
        left.Insert(x);
      }
      Repr := Repr + left.Repr;
    } else {
      if right == null {
        right := new TreeNode(x);
      } else {
        right.Insert(x);
      }
      Repr := Repr + right.Repr;
    }
    Contents := Contents + {x};
  }
}
