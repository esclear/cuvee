package cuvee.a

import cuvee.pure._

object Unused {
  def unused(df: Def): Option[(Def, Rule)] = {
    val Def(f, cases) = df
    
    val is = usedArgs(df)
    val f_ = Fun(f.name, f.params, is map f.args, f.res)

    if (is.length < f.args.length) {
      val cases_ = for (C(args, guard, body) <- cases) yield {
        C(is map args, guard, keep(f, f_, is, body))
      }

      val df_ = Def(f_, cases_)
      val xs = Expr.vars("x", f.args)
      val eq = Rule(App(f, xs), App(f_, is map xs))

      Some((df_, eq))
    } else {
      None
    }
  }

  def keep(f: Fun, f_ : Fun, is: List[Int], e: Expr): Expr = e match {
    case k: Lit => k
    case y: Var => y

    case App(Inst(`f`, su), args) =>
      App(Inst(f_, su), is map args)

    case App(inst, args) =>
      App(inst, args map (keep(f, f_, is, _)))
  }

  // compute those argument positions that are needed
  def usedArgs(df: Def): List[Int] = {
    val Def(f, cases) = df
    val is = 0 until f.args.length
    is.toList.filter { i: Int =>
      cases exists { case C(args, guard, body) =>
        args(i) match {
          case x: Var =>
            (x in guard) || isUsed(f, i, x, body)
          case _ =>
            true
        }
      }
    }
  }

  def isUsed(f: Fun, i: Int, x: Var, e: Expr): Boolean = e match {
    case _: Lit => false
    case y: Var => x == y

    case App(Inst(`f`, _), args) =>
      args.zipWithIndex.exists { case (arg, j) =>
        j != i && isUsed(f, i, x, arg)
      }

    case App(_, args) =>
      args.exists(isUsed(f, i, x, _))
  }
}
