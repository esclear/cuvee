package cuvee.a

import cuvee.pure._
import cuvee.StringOps

object Variant {
  def main(args: Array[String]) {
    // val as = List(1, 2, 3)
    // for (bs <- powerset(as))
    //   println(bs)

    import Fun._

    val remove = Fun("remove", List(a), List(a, list_a), list_a)
    val x = Var("x", a)
    val y = Var("y", a)
    val xs = Var("xs", list_a)

    val nil_ = Const(nil, list_a)

    val df = Def(
      remove,
      List(
        C(List(y, nil_), Nil, nil_),
        C(List(y, cons(x, xs)), List(x === y), remove(y, xs)),
        C(List(y, cons(x, xs)), List(x !== y), cons(x, remove(y, xs)))
      )
    )

    for ((dp, df, eq) <- restricted(df)) {
      println(eq)
      println()
      println(dp)
      println()
      println(df)
      println()
      println()
    }
  }

  def restricted(df: Def): List[(Def, Def, Expr)] = {
    val Def(f, cases) = df
    val variants = powerset(cases)
    for ((cases, i) <- variants.zipWithIndex if isUseful(f, cases))
      yield restricted(f, i, cases)
  }

  def isUseful(f: Fun, cases: List[(Boolean, C)]) = {
    // don't generate variants in the following situations
    // - all cases are picked:  just gives back original definition
    // - there is no base case: cannot happen for terminating functions (which is assumed)
    // - there is no recursive case: trivial/not useful

    val notAll = cases exists (!_._1)

    val hasBase = cases exists { case (take, cs) =>
      take && !cs.isRecursive(f)
    }

    val hasRec = cases exists { case (take, cs) =>
      take && cs.isRecursive(f)
    }

    notAll && hasBase && hasRec
  }

  def restricted(
      f: Fun,
      i: Int,
      cases: List[(Boolean, C)]
  ): (Def, Def, Expr) = {
    val p_ = Fun(f.name + "_pre" __ i, f.params, f.args, Sort.bool)
    val f_ = Fun(f.name + "$" __ i, f.params, f.args, f.res)

    val pcases_ = for ((take, C(args, guard, body)) <- cases) yield {
      C(args, guard, bool(take))
    }

    val all =
      for (((take, C(args, guard, body)), i) <- cases.zipWithIndex if take)
        yield {
          (args, i)
        }

    val fcases_ =
      for (((take, C(args, guard, body)), j) <- cases.zipWithIndex if take)
        yield {
          val needsGuard = all exists { case (pats, i) =>
            i != j && mayOverlap(args, pats)
          }

          if (needsGuard)
            C(args, guard, body)
          else // we can drop all guards of patterns that have no overlap
            C(args, Nil, body)
        }

    val dp_ = Def(p_, pcases_)
    val df_ = Def(f_, fcases_)

    val xs = Expr.vars("x", f.args)
    val eq = Forall(xs, Imp(App(p_, xs), Eq(App(f, xs), App(f_, xs))))

    (dp_, df_, eq)
  }

  def powerset[A](as: List[A]): List[List[(Boolean, A)]] = as match {
    case Nil =>
      List(Nil)
    case a :: as =>
      val bs = powerset(as)
      val y = bs map { (true, a) :: _ }
      val n = bs map { (false, a) :: _ }
      y ++ n
  }

  // check whether two patterns may have overlap,
  // assuming functions are constructors
  def mayOverlap(pat1: Expr, pat2: Expr): Boolean = {
    (pat1, pat2) match {
      case (_: Var, _) | (_, _: Var) =>
        true
      case (App(Inst(fun1, _), args1), App(Inst(fun2, _), args2)) =>
        fun1 == fun2 && mayOverlap(args1, args2)
    }
  }

  def mayOverlap(pats1: List[Expr], pats2: List[Expr]): Boolean = {
    require(pats1.length == pats2.length)
    (pats1 zip pats2) forall { case (pat1, pat2) =>
      mayOverlap(pat1, pat2)
    }
  }
}
