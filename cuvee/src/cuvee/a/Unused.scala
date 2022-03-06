package cuvee.a

import cuvee.pure._

object Unused {
  def main(args: Array[String]) {
    import Fun._

    val f = Fun("f", List(a, b), List(b, list_a), list_a)
    val x = Var("x", a)
    val y = Var("y", b)
    val xs = Var("xs", list_a)

    val nil_ = Const(nil, list_a)

    val df = Def(
      f,
      List(
        C(List(y, nil_), Nil, nil_),
        C(List(y, cons(x, xs)), Nil, cons(x, f(y, xs)))
      )
    )

    for ((df_, eq) <- unused(df)) {
      println(df_)
      println()
      println(eq)
    }
  }

  def unused(df: Def): Option[(Def, Rule)] = {
    val Def(f, cases) = df

    val is = usedArgs(df)

    val args_ = is map f.args
    val params_ = f.params filter (_ in args_)
    val f_ = Fun(f.name + "'", params_, args_, f.res)

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
      // get rid of superflous parameters here
      val su_ = su filter { case (p, t) => f_.params contains p }
      App(Inst(f_, su_), is map args)

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
