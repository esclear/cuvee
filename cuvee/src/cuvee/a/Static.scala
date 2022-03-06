package cuvee.a

import cuvee.pure._

object Static {
  def staticArgs(df: Def): List[Int] = {
    val Def(f, cases) = df
    val is = 0 until f.args.length
    is.toList.filter { i: Int =>
      cases forall { case C(args, guard, body) =>
        isStatic(f, i, args(i), body)
      }
    }
  }

  def isStatic(f: Fun, i: Int, a: Expr, e: Expr): Boolean = e match {
    case _: Lit => true
    case y: Var => true

    case App(Inst(`f`, _), args) =>
      args(i) == a

    case App(_, args) =>
      args.forall(isStatic(f, i, a, _))
  }
}
