package cuvee.a

import cuvee.StringOps
import cuvee.backtrack
import cuvee.toControl
import cuvee.pure._
import cuvee.smtlib.DeclareFun
import cuvee.smtlib.Assert

case class Query(typ: Type, funs: List[Fun], base: Expr, conds: List[Expr]) {
  def constraints = base :: conds

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

    for ((q, df_, eq) <- maybeResults(df)) {
      println("exists")
      for (f <- q.funs)
        println("  " + f)
      println("where")
      for (c <- q.constraints)
        println("  " + c)
      println("such that")
      println("  " + eq)
      println()
      println(df_)
    }
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

  def results(df: Def): List[(Query, Def, Rule)] = try {
    maybeResults(df)
  } catch {
    case _: arse.Backtrack =>
      println("not promoting (backtrack): " + df.fun)
      Nil
  }

  // note: Def must not have non-static base cases

  // TODO: we *can* promote individual base cases, and should do so (e.g. contains),
  //       but then we have to make sure that the other base cases are robust against it,
  //       similarly to the recursive cases
  def maybeResults(df: Def): List[(Query, Def, Rule)] = {
    val Def(f, cases) = df

    val recursiveCases = cases.count { cs =>
      cs.isRecursive(f) && !cs.isTailRecursive(f)
    }

    val isLinear = recursiveCases <= 1

    if (!isLinear) {
      // in this case, we could synthesize a function that aggregates all occurrences
      println(
        "not promoting: " + f + " with " + recursiveCases + " recursive cases"
      )
      Nil
    } else {
      val is = cases.zipWithIndex collect {
        case (C(args, guard, x: Var), i) if args contains x =>
          (i, args indexOf x)
      }

      val typ = f.res
      val params = f.params filter (_ in typ)
      val ⊕ = Fun("oplus", params, List(typ, typ), typ)

      val z = Var("z", typ)

      val b = Fun("b", params, Nil, typ)
      val b_ = Const(b, typ)

      val base = Forall(List(z), z === ⊕(b_, z))
      val xs = Expr.vars("x", f.args)

      for ((i, k) <- is) yield {
        val f_ = Fun(promoted(i)(f.name), f.params, f.args, f.res)

        val stuff =
          for ((cs @ C(args, guard, body), k) <- cases.zipWithIndex)
            yield body match {
              case x: Var if i == k =>
                assert(args contains x) // guaranteed from earlier
                val j = args indexOf x
                (cs, None, Some(j -> b_))

              case x: Var if args contains x =>
                val j = args indexOf x

                val c = Fun("c", params, Nil, typ)
                val c_ = Const(c, typ)

                val lhs = c_
                val rhs = ⊕(c_, z)
                val cond = Forall(List(z), lhs === rhs)

                (cs, Some(c -> cond), Some(j -> c_))

              // tail recursive case is irrelevant
              case App(Inst(`f`, su), as) =>
                val body_ = App(Inst(f_, su), as)
                val cs_ = C(args, guard, body_)
                (cs_, None, None)

              // case _ if cs.isRecursive(f) =>
              case _ =>
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
                val φ = Fun("phi" + k, params, ts, typ)
                val rhs = ⊕(App(φ, zs), z)

                val cond = Clause(z :: zs, guard, lhs === rhs)

                val bs_ = es map { App(f_, _) }
                val φ_ = App(φ, xs ++ bs_)
                val cs_ = C(args, guard, φ_)
                (cs_, Some(φ -> cond), None)

              // case _ =>
              //   backtrack("cannot promote " + f + ", base not hoisted: " + body)
            }

        val (cases_, stuff_, js_) = stuff.unzip3
        val (φs, conds) = stuff_.flatten.unzip
        val js = js_.flatten.toMap // can only a single result

        val q = Query(typ, b :: ⊕ :: φs, base, conds)
        val df_ = Def(f_, cases_)

        val ys =
          for ((x, j) <- xs.zipWithIndex)
            yield
              if (js contains j) js(j)
              else x

        val xk = xs(k)
        val eq = Rule(App(f, xs), ⊕(App(f_, ys), xk), True, List(xk -> b_))

        (q, df_, eq)
      }
    }
  }

  val rules = List(
    (Sort.int, Zero, Plus),
    (Sort.int, One, Times),
    (Sort.bool, False, Or),
    (Sort.bool, True, And)
  )

  def not(phi: Expr) = phi match {
    case True  => False
    case False => True
  }

  def builtin(
      q: Query,
      typ: Type,
      base: Expr,
      fun: Sugar.commutative
  ): Option[List[Rule]] = {
    q match {
      case Query(
            `typ`,
            List(b0, f0, g0),
            Clause(fs, Nil, Eq(w, App(f, List(App(b, Nil), w_)))),
            List(
              Clause(fs_, pre_, Eq(w__, App(f_, List(App(g_, xs_), z_))))
            )
          ) if b0 == b.fun && f0 == f.fun && w == w_ && (xs_ contains w__) =>
        val xs = Expr.vars("x", f0.args)

        val eq1 = Rule(Const(b0, typ), base)
        val eq2 = Rule(App(f0, xs), fun(xs))
        val eq3 = Rule(App(g0, xs_), not(base))

        // println("query: ")
        // for(phi <- q.base :: q.conds)
        //   println("  " + phi)
        // println("solution: ")
        // println("  " + eq1)
        // println("  " + eq2)
        // println("  " + eq3)

        Some(List(eq1, eq2, eq3))

      case Query(
            `typ`,
            List(b0, f0, g0),
            Clause(fs, Nil, Eq(w, App(f, List(App(b, Nil), w_)))),
            List(
              Clause(
                fs_,
                Nil,
                Eq(
                  fun(List(x_, App(f_, List(y_, z_)))),
                  App(f__, List(App(g_, List(x__, y__)), z__))
                )
              )
            )
          )
          if b0 == b.fun && f0 == f.fun && g0 == g_.fun && w == w_ && f == f_ && f_ == f__ && x_ == x__ && y_ == y__ && z_ == z__ =>
        val xs = Expr.vars("x", f0.args)
        val ys = Expr.vars("y", g0.args)

        val eq1 = Rule(Const(b0, typ), base)
        val eq2 = Rule(App(f0, xs), fun(xs))
        val eq3 = Rule(App(g0, ys), fun(ys))

        Some(List(eq1, eq2, eq3))

      case _ =>
        None
    }
  }

  def builtin(q: Query): List[List[Rule]] = {
    for (
      (typ, base, fun) <- rules;
      eqs <- builtin(q, typ, base, fun)
    )
      yield eqs
  }
}
