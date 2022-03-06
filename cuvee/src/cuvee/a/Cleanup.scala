package cuvee.a

import cuvee.pure._

object Cleanup {
  def main(args: Array[String]) {
    import Fun._

    val id = Fun("id", List(a), List(list_a), list_a)
    val f = Fun("f", List(a, b), List(list_a, b), b)
    val x = Var("x", a)
    val y = Var("y", b)
    val xs = Var("xs", list_a)

    val nil_ = Const(nil, list_a)

    val df = Def(
      f,
      List(
        C(List(nil_, y), Nil, y),
        C(List(cons(x, xs), y), Nil, f(xs, y))
      )
    )

    for (eq <- constant(df)) {
      println(eq)
    }

    val dg = Def(
      id,
      List(
        C(List(nil_), Nil, nil_),
        C(List(cons(x, xs)), Nil, cons(x, id(xs)))
      )
    )

    for (eq <- identity(dg)) {
      println(eq)
    }
  }

  // example: remove when all are taken
  def identity(df: Def): Option[Rule] = {
    val Def(f, cases) = df

    val ok = cases forall {
      case C(List(x: Var), Nil, y)
          if x == y => // TODO: cannot recognize complete guard splits
        true
      case C(List(App(c, xs)), Nil, App(d, es))
          if c == d => // TODO: assumes c is a constructor
        (xs zip es) forall {
          case (x: Var, y) if x == y =>
            true // argument passed unchanged
          case (x: Var, App(Inst(`f`, _), List(y))) if x == y =>
            true // argument passed through recursive call
          case cs =>
            false
        }
      case cs =>
        false
    }

    if (ok) {
      val List(t) = f.args
      val x = Var("x", t)
      Some(Rule(f(x), x))
    } else {
      None
    }
  }

  // remove when none is taken
  // assuming base cases are abstracted by variables already
  def constant(df: Def): Option[Rule] = {
    val Def(f, cases) = df
    val static = Hoist.staticArgs(df)

    val stuff = cases map {
      case C(args, guard, x: Var) => // x is static
        val ok = static find { (i: Int) => args(i) == x }
        ok match {
          case None =>
            (false, None)
          case Some(i) =>
            (true, Some(i))
        }
      case C(args, guard, App(Inst(`f`, _), _)) => // tail-recursive
        (true, None)
      case cs =>
        (false, None)
    }

    val (oks, is_) = stuff.unzip
    val ok = oks.forall(b => b)
    val is = is_.flatten

    (ok, is) match {
      case (true, List(i)) =>
        val xs = Expr.vars("x", f.args)
        val eq = Rule(App(f, xs), xs(i))
        Some(eq)
      case _ =>
        None
    }
  }
}
