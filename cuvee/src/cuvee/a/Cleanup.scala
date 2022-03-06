package cuvee.a

import cuvee.pure._

object Cleanup {
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

  def main(args: Array[String]) {
    import Fun._

    val id = Fun("id", List(a), List(list_a), list_a)
    val x = Var("x", a)
    val xs = Var("xs", list_a)

    val nil_ = Const(nil, list_a)

    val df = Def(
      id,
      List(
        C(List(nil_), Nil, nil_),
        C(List(cons(x, xs)), Nil, cons(x, id(xs)))
      )
    )

    val eq = identity(df)
    println(eq)
  }
}
