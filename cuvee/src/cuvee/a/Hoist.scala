package cuvee.a

import cuvee.pure._

object Hoist {
  def main(args: Array[String]) {
    import Fun._

    val snoc = Fun("snoc", List(a), List(list_a, a), list_a)
    val x = Var("x", a)
    val y = Var("y", a)
    val xs = Var("xs", list_a)

    val nil_ = Const(nil, list_a)

    val df = Def(
      snoc,
      List(
        C(List(nil_, y), Nil, cons(y, nil_)),
        C(List(cons(x, xs), y), Nil, cons(x, snoc(xs, y)))
      )
    )

    for ((df_, eq) <- static(df)) {
      println(df_)
      println()
      println(eq)
    }
  }

  def static(df: Def): Option[(Def, Rule)] = {
    val Def(f, cases) = df

    val static = staticArgs(df)
    // println("static arguments of " + df.fun.name + " = " + static)

    val stuff =
      for (C(args, guard, body) <- cases)
        yield {
          val args_ = static map args
          val xs = args_.free
          val (guard_, su1) = hoist(guard, xs)
          val (body_, su2) = hoist(body, xs)
          val cs_ = C(args, guard_, body_)
          (cs_, su1 ++ su2)
        }

    val (cases_, su) = stuff.unzip
    val (zs, as) = su.flatten.unzip

    if (zs.nonEmpty) {
      val f_ = Fun(f.name + "'", f.params, f.args ++ zs.types, f.res)

      val cases__ =
        for (C(args, guard, body) <- cases_)
          yield {
            C(args ++ zs, guard, extend(f, f_, zs, body))
          }

      val xs = Expr.vars("x", f.args)
      val df_ = Def(f_, cases__)
      val eq = Rule(App(f, xs), App(f_, xs ++ as))

      Some((df_, eq))
    } else {
      None
    }
  }

  def hoist(e: Expr, xs: Set[Var]): (Expr, List[(Var, Expr)]) = {
    e match {
      case x: Var => // don't hoist plain variables
        (x, Nil)

      case _ if e.free subsetOf xs => // e is a (maximal) static subterm
        val z = Expr.fresh("z", e.typ)
        (z, List(z -> e))

      case App(inst, args) =>
        val (args_, su) = hoist(args, xs)
        (App(inst, args_), su)
    }
  }

  def hoist(
      es: List[Expr],
      xs: Set[Var]
  ): (List[Expr], List[(Var, Expr)]) = {
    val stuff = es map (hoist(_, xs))
    val (es_, su) = stuff.unzip
    (es_, su.flatten)
  }

  def extend(f: Fun, f_ : Fun, xs: List[Var], e: Expr): Expr = e match {
    case k: Lit => k
    case y: Var => y

    case App(Inst(`f`, su), args) =>
      App(Inst(f_, su), args ++ xs)

    case App(inst, args) =>
      App(inst, args map (extend(f, f_, xs, _)))
  }

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
