package cuvee.a

import cuvee.pure._

object Hoist {
  def static(df: Def): Option[(Def, Rule)] = {
    val Def(f, cases) = df

    val static = Static.staticArgs(df)

    val stuff =
      for (C(args, guard, body) <- cases)
        yield {
          val args_ = static map args
          val xs = args_.free
          val (body_, su) = decompose(body, xs)
          val cs_ = C(args, guard, body_)
          (cs_, su)
        }

    val (cases_, su) = stuff.unzip
    val (zs, as) = su.flatten.unzip

    if (zs.nonEmpty) {
      val f_ = Fun(f.name, f.params, f.args ++ zs.types, f.res)

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

  def decompose(e: Expr, xs: Set[Var]): (Expr, List[(Var, Expr)]) = {
    e match {
      case x: Var => // don't hoist plain variables
        (x, Nil)

      case _ if e.free subsetOf xs => // e is a (maximal) static subterm
        val z = Expr.fresh("z", e.typ)
        (z, List(z -> e))

      case App(inst, args) =>
        val (args_, su) = decompose(args, xs)
        (App(inst, args_), su)
    }
  }

  def decompose(
      es: List[Expr],
      xs: Set[Var]
  ): (List[Expr], List[(Var, Expr)]) = {
    val stuff = es map (decompose(_, xs))
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
}
