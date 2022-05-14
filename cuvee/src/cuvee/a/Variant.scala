package cuvee.a

import cuvee.pure._
import cuvee.StringOps

object Variant {
  /* def boolean(f: Fun, f_ : Fun, expr: Expr, negate: Boolean): Expr = {
    expr match {
      case True  => if (negate) False else True
      case False => if (negate) True else False

      case Not(expr) => // neet to get down to recursive calls
        boolean(f, f_, expr, !negate)
      case Imp(phi, psi) =>
        And(boolean(f, f_, phi, !negate), boolean(f, f_, psi, negate))
      case And(phis) =>
        Or(boolean(f, f_, phis, negate))
      case Or(phis) =>
        And(boolean(f, f_, phis, negate))
      case App(Inst(`f`, su), args) =>
        App(Inst(f_, su), args)

      case _ =>
        Not(expr)
    }
  }

  def boolean(
      f: Fun,
      f_ : Fun,
      exprs: List[Expr],
      negate: Boolean
  ): List[Expr] = {
    exprs map (boolean(f, f_, _, negate))
  }

  def negated(df: Def): (Def, Rule) = {
    val Def(f, cases) = df
    require(
      f.res == Sort.bool,
      "cannot generate negated variant, not a predicate"
    )

    val f_ = Fun("not_" + f.name, f.params, f.args, f.res)
    val cases_ =
      for (C(args, guard, body) <- cases)
        yield C(args, guard, boolean(f, f_, body, negate = true))

    val df_ = Def(f_, cases_)
    val xs = Expr.vars("x", f.args)
    val eq = Rule(Not(App(f, xs)), App(f_, xs))

    (df_, eq)
  } */

  def canNegate(f: Fun, cs: C) = cs match {
    case C(args, guard, x: Var) =>
      args contains x
    case C(args, guard, App(Inst(`f`, _), _)) =>
      true
    case _ =>
      false
  }

  def negated(df: Def): Option[Rule] = {
    val Def(f, cases) = df

    if (cases forall (canNegate(f, _))) {
      val xs = Expr.vars("x", f.args)

      val is =
        for (C(args, guard, x: Var) <- cases)
          yield args indexOf x

          // THIS SUCKS. We need to backchain on variations of original encodings, i.e.
          // hook onto contains_(x₀, x₁, true, false) because it seems useful,
          // but not onto contains_(x₀, x₁, false, true) because that already recovers...

      ???
    } else {
      None
    }
  }

  def restricted(df: Def): List[(Def, Def, Rule)] = {
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

  def recurse(f: Fun, p: Fun, expr: Expr): List[Expr] = expr match {
    case App(Inst(`f`, su), args) =>
      List(App(Inst(p, su), args))
    case App(_, args) =>
      args flatMap (recurse(f, p, _))
    case _ =>
      Nil
  }

  def restricted(
      f: Fun,
      i: Int,
      cases: List[(Boolean, C)]
  ): (Def, Def, Rule) = {
    val p_ = Fun(precondition(i)(f.name), f.params, f.args, Sort.bool)
    val f_ = Fun(casevariant(i)(f.name), f.params, f.args, f.res)

    val pcases_ = for ((take, C(args, guard, body)) <- cases) yield {
      if (take) {
        val body_ = recurse(f, p_, body)
        C(args, guard, And(body_))
      } else {
        C(args, guard, False)
      }
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

          val body_ = body replace (f, f_)

          if (needsGuard)
            C(args, guard, body_)
          else // we can drop all guards of patterns that have no overlap
            C(args, Nil, body_)
        }

    val dp_ = Def(p_, pcases_)
    val df_ = Def(f_, fcases_)

    val xs = Expr.vars("x", f.args)
    val eq = Rule(App(f, xs), App(f_, xs), App(p_, xs))

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
