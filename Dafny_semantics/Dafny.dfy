type Var = string
type Val = int

datatype AExpr = N(Val)
               | V(Var)
               | Plus(AExpr, AExpr)

datatype BExpr = B(bool)
               | Less(AExpr, AExpr)
               | Eq(AExpr, AExpr)
               | Not(BExpr)
               | And(BExpr, BExpr)

datatype Com = Skip
             | Assign(Var, AExpr)
             | Seq(Com, Com)
             | If(BExpr, Com, Com)
             | While(BExpr, Com)

type Env = map<Var, Val>
type Configuration = (Com, Env)
type Derivation = seq<Configuration>

function bigstep_aexpr(a: AExpr, s: Env): Val {
  match(a) {
    case N(n) => n
    case V(x) => if x in s then s[x] else 0
    case Plus(a0, a1) => bigstep_aexpr(a0, s) + bigstep_aexpr(a1, s)
  }
}

function bigstep_bexprr(b: BExpr, s: Env): bool {
  match(b) {
    case B(v) => v
    case Less(a0, a1) => bigstep_aexpr(a0, s) < bigstep_aexpr(a1, s)
    case Eq(a0, a1) => bigstep_aexpr(a0, s) == bigstep_aexpr(a1, s)
    case Not(op) => !bigstep_bexprr(op, s)
    case And(b0, b1) => bigstep_bexprr(b0, s) && bigstep_bexprr(b1, s)
  }
}

predicate bigstep(c: Com, s:Env, s':Env, k:nat)
  decreases c,k
{
  match(c) {
    case Skip =>
      k == 1 && s == s'
    case Assign(v,a) =>
      k == 1 && s[v := bigstep_aexpr(a,s)] == s'
    case Seq(c1, c2) =>
      exists k':nat, s'':Env ::
        0 < k' < k &&
        bigstep(c1, s, s'', k') &&
        bigstep(c2, s'', s', k-k')
    case If(b, c1, c2) =>
      if(bigstep_bexprr(b,s)) then bigstep(c1, s, s', k)
      else bigstep(c2, s, s',k)
    case While(b, c') =>
      if (bigstep_bexprr(b,s)) then
        exists s'' : Env, k' : nat :: 0 < k' < k &&
                                      bigstep(c', s, s'', k')  &&
                                      bigstep(c, s'', s', k-k')
      else k == 1 && s == s'
  }
}