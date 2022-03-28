package cuvee.a

import cuvee.StringOps
import cuvee.pure._
import cuvee.smtlib.DeclareFun
import cuvee.smtlib.Assert

case class Query(funs: List[Fun], constraints: List[Expr]) {
  override def toString = {
    funs.mkString("exists\n  ", "  \n", "\n") + constraints.mkString(
      "where\n  ",
      "  \n",
      ""
    )
  }

  def cmds = {
    val decls =
      for (Fun(name, Nil, args, res) <- funs)
        yield DeclareFun(name, args, res)

    val conds =
      for (phi <- constraints)
        yield Assert(phi)

    decls ++ conds
  }

}

object Promote {
  def main(args: Array[String]) {
    // val as = List(1, 2, 3)
    // for (bs <- powerset(as))
    //   println(bs)

    import Fun._

    val length = Fun("length'", List(a), List(list_a, Sort.int), Sort.int)
    val x = Var("x", a)
    val n = Var("n", Sort.int)
    val xs = Var("xs", list_a)

    val nil_ = Const(nil, list_a)

    val df = Def(
      length,
      List(
        C(List(nil_, n), Nil, n),
        C(List(cons(x, xs), n), Nil, length(xs, n) + One)
      )
    )

    println(df)
    println()

    val (Query(funs, constraints), df_, eq) = results(df)
    println("exists")
    for (f <- funs)
      println("  " + f)
    println("where")
    for (c <- constraints)
      println("  " + c)
    println("such that")
    println("  " + eq)
    println()
    println(df_)
  }

  def free(expr: Expr): List[Var] = expr match {
    case l: Lit       => Nil
    case x: Var       => List(x)
    case App(_, args) => free(args)
  }

  def free(exprs: List[Expr]): List[Var] = {
    exprs flatMap free
  }

  def abstracted(
      f: Fun,
      exprs: List[Expr]
  ): (List[Expr], List[(Var, List[Expr])]) = {
    val stuff = exprs map (abstracted(f, _))
    val (exprs_, xs) = stuff.unzip
    (exprs_, xs.flatten)
  }

  def abstracted(f: Fun, expr: Expr): (Expr, List[(Var, List[Expr])]) = {
    expr match {
      case x: Var =>
        (x, Nil)
      case l: Lit =>
        (l, Nil)
      case App(Inst(`f`, _), args) =>
        var z = Expr.fresh("z", f.res)
        (z, List(z -> args))
      case App(inst, args) =>
        val (args_, xs) = abstracted(f, args)
        (App(inst, args_), xs)
    }
  }

  // note: Def must not have non-static base cases
  def results(df: Def): (Query, Def, Rule) = {
    val Def(f, cases) = df

    val typ = f.res
    val params = f.params filter (_ in typ)
    val ⊕ = Fun("oplus", params, List(typ, typ), typ)

    val z = Var("z", typ)
    val f_ = Fun(f.name + "'", f.params, f.args, f.res)

    val b = Fun("b", params, Nil, typ)
    val b_ = Const(b, typ)

    val base = Forall(List(z), z === ⊕(b_, z))

    val stuff =
      for ((cs @ C(args, guard, body), i) <- cases.zipWithIndex) yield {
        if (cs.isRecursive(f)) {

          val (body_, rs) = abstracted(f, body)
          val (ys, es) = rs.unzip
          val ws = body_.free filterNot ys.contains
          val vs = guard.free
          val as = ys map { ⊕(_, z) }
          val su = Expr.subst(ys, as)
          val lhs = body_ subst su

          val xs = ws.toList ++ vs.toList
          val zs = xs ++ ys
          val ts = zs.types
          val params = f.params filter (_ in ts)
          val φ = Fun("phi" + i, params, ts, typ)
          val rhs = ⊕(App(φ, zs), z)

          val cond = Clause(z :: zs, guard, lhs === rhs)

          val bs_ = es map { App(f_, _) }
          val φ_ = App(φ, xs ++ bs_)
          val cs_ = C(args, guard, φ_)
          (Some(φ), cs_, Some(cond))
        } else {
          val cs_ = C(args, guard, b_)
          (None, cs_, None)
        }
      }

    val (φs_, cases_, conds_) = stuff.unzip3
    val φs = φs_.flatten
    val conds = conds_.flatten

    val xs = Expr.vars("x", f.args)
    val q = Query(b :: ⊕ :: φs, base :: conds)
    val eq = Rule(App(f, xs), ⊕(App(f_, xs), b_))

    val df_ = Def(f_, cases_)
    (q, df_, eq)
  }
}
