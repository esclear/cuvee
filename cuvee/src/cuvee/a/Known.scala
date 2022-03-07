package cuvee.a

import cuvee.pure._

object Known {
  // Note: do not try to specialize known definitions,
  //       this is done via factoring
  // def known(df: Def, all: Iterable[Def]): List[Rule] = {
  //   all flatMap { known(df, _) }
  // }

  def known(df: Def, dg: Def): Option[Rule] = {
    if (
      df.fun != dg.fun &&
      df.fun.params == dg.fun.params &&
      df.fun.args == dg.fun.args &&
      df.fun.res == dg.fun.res &&
      df.cases.length == dg.cases.length
    ) {
      val Def(f, fcases) =
        df // Check: can we guarantee order via fuse/factoring maintained?
      val Def(g, gcases) = dg

      val ok_ =
        (fcases zip gcases) forall { case (cf, cg) =>
          ok(f, cf, g, cg)
        }

      if (ok_) {
        val xs = Expr.vars("x", f.args)
        val lhs = App(f, xs)
        val rhs = App(g, xs)
        val eq = Rule(lhs, rhs, True)
        // println("can represent " + f + " as " + g)
        Some(eq)
      } else {
        None
      }
    } else {
      None
    }
  }

  def ok(f: Fun, cf: C, g: Fun, cg: C): Boolean = {
    val C(fargs, fguard, fbody) = cf
    val C(gargs, gguard, gbody) = cg

    var ok = true
    var re: Map[Var, Var] = Map()

    def rename(a: Expr, b: Expr): Unit = (a, b) match {
      case (x: Var, y: Var) =>
        re += (x -> y)
      case (App(f, as), App(g, bs)) if f == g =>
        renames(as, bs)
      case _ =>
        ok = false
    }

    def renames(as: List[Expr], bs: List[Expr]): Unit = (as, bs) match {
      case (Nil, Nil) =>
      case (a :: as, b :: bs) =>
        rename(a, b)
        renames(as, bs)
    }

    renames(fargs, gargs)

    if (ok) {
      val _fguard = fguard rename re
      val _gguard = gguard rename re

      val _fbody = fbody rename re
      val _gbody = gbody rename re bottomup {
        case App(Inst(`g`, su), args) => App(Inst(`f`, su), args)
        case e => e
      }

      ok = _fguard == _gguard && _fbody == _gbody

      // if(!ok && _fguard != _gguard)
      //   println("; guards different: " + _fguard + " and " + _gguard)
      // if(!ok && _fbody != _gbody)
      //   println("; bodies different: " + _fbody + " and " + _gbody)
    }

    ok
  }
}
