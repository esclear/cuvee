package cuvee.a

import cuvee.StringOps
import cuvee.backtrack
import cuvee.toControl
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Tool
import java.io.File
import scala.io.Source
import java.io.StringReader

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
        var z = Expr.fresh("y", f.res)
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


  def maybeAccumulator(df: Def): List[(Query, Def, Rule)] = {
    ???
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

    val isLinear = recursiveCases == 1

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

        sealed trait P
        case object Tail extends P
        case class Base(pos: Int, arg: Expr) extends P
        case class Arg(pos: Int, arg: Expr, fun: Fun, phi: Expr) extends P
        case class Rec(fun: Fun, phi: Expr) extends P

        val stuff =
          for ((cs @ C(args, guard, body), k) <- cases.zipWithIndex)
            yield body match {
              case x: Var if i == k =>
                assert(args contains x) // guaranteed from earlier
                val j = args indexOf x
                (cs, Base(j, b_))

              case x: Var if args contains x =>
                val j = args indexOf x

                val c = Fun("phi", params, Nil, typ)
                val c_ = Const(c, typ)

                val lhs = c_
                val rhs = ⊕(c_, z)
                val cond = Forall(List(z), lhs === rhs)

                (cs, Arg(j, c_, c, cond))

              // tail recursive case is irrelevant
              case App(Inst(`f`, su), as) =>
                val body_ = App(Inst(f_, su), as)
                val cs_ = C(args, guard, body_)
                (cs_, Tail)

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

                (cs_, Rec(φ, cond))

              // case _ =>
              //   backtrack("cannot promote " + f + ", base not hoisted: " + body)
            }

        val (cases_, ps_) = stuff.unzip

        val φs = ps_ flatMap {
          case p: Arg => Some(p.fun)
          case p: Rec => Some(p.fun)
          case _      => None
        }

        val conds = ps_ flatMap {
          case p: Arg => Some(p.phi)
          case p: Rec => Some(p.phi)
          case _      => None
        }

        val is = Map(ps_ flatMap {
          case p: Arg => Some(p.pos -> p.arg)
          case _      => None
        }: _*)

        val js = Map(ps_ flatMap {
          case p: Arg  => Some(p.pos -> p.arg)
          case p: Base => Some(p.pos -> p.arg)
          case _       => None
        }: _*)

        val q = Query(typ, b :: ⊕ :: φs, base, conds.distinct)
        val df_ = Def(f_, cases_)

        val ys =
          for ((x, i) <- xs.zipWithIndex)
            yield
              if (is contains i) js(i)
              else x

        val zs =
          for ((x, j) <- xs.zipWithIndex)
            yield
              if (js contains j) js(j)
              else x

        val xk = xs(k)
        val eq = Rule(App(f, ys), ⊕(App(f_, zs), xk), True, List(xk -> b_))

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

  /*
(assert (= $0 0))
(assert (= $1 1))
(assert (= $false false))
(assert (= $true true))
   */

  val predefined = List(
    "(declare-fun $0 () Int)",
    "(declare-fun $1 () Int)",
    "(declare-fun $true () Bool)",
    "(declare-fun $false () Bool)",
    "(assert (forall ((x Int)) (= $0 0)))",
    "(assert (forall ((x Int)) (= $1 1)))",
    "(assert (forall ((x Int)) (= $false false)))",
    "(assert (forall ((x Int)) (= $true true)))",
    "(declare-fun $+   (Int Int) Int)",
    "(declare-fun $*   (Int Int) Int)",
    "(declare-fun $or  (Bool Bool) Bool)",
    "(declare-fun $and (Bool Bool) Bool)",
    "(assert (forall ((x Int) (y Int))   (= ($+ x y)   (+ x y))))",
    "(assert (forall ((x Int) (y Int))   (= ($* x y)   (* x y))))",
    "(assert (forall ((x Bool) (y Bool)) (= ($or x y)  (or x y))))",
    "(assert (forall ((x Bool) (y Bool)) (= ($and x y) (and x y))))"
  )

  val renaming = Map(
    "$0" -> cuvee.sexpr.Lit.num("0"),
    "$1" -> cuvee.sexpr.Lit.num("1"),
    "$true" -> cuvee.sexpr.Id("true"),
    "$false" -> cuvee.sexpr.Id("false"),
    "$+" -> cuvee.sexpr.Id("+"),
    "$*" -> cuvee.sexpr.Id("*"),
    "$or" -> cuvee.sexpr.Id("or"),
    "$and" -> cuvee.sexpr.Id("and")
  )

  def query(
      q: Query,
      df_ : Def,
      eq: Rule,
      cmds: List[Cmd],
      defs: List[Def],
      st0: State
  ): List[List[Rule]] = {
    val dir = "queries/"
    new File(dir).mkdirs()

    val file = dir + df_.fun.name + ".smt2"
    val tmp = log(file)

    for (cmd @ DeclareSort(_, _) <- cmds) {
      dump(tmp, cmd)
    }

    for (cmd @ DeclareDatatypes(_, _) <- cmds) {
      dump(tmp, cmd)
    }

    val decls =
      for (df <- defs)
        yield df.decl

    for (cmd <- decls)
      dump(tmp, cmd)

    // don't reuse the function we are rewriting
    val axioms =
      for (
        df <- defs if df.fun != eq.fun;
        cmd <- df.axioms
      )
        yield cmd

    val x = Var("x", Sort.int)

    // for (cmd <- axioms)
    //   dump(tmp, cmd)

    for (cmd <- axioms) {
      cmd match {
        case Assert(_ @Forall(_, _)) =>
          dump(tmp, cmd)

        case Assert(phi) =>
          val cmd_ = Assert(Forall(List(x), phi))
          tmp println ("; DUMMY QUANTIFIER")
          tmp println ("; PLEASE FIX THIS!!")
          dump(tmp, cmd_)

        case _ =>
          dump(tmp, cmd)
      }
    }

    for (cmd <- predefined)
      tmp.println(cmd)
    tmp.println()

    tmp.println("; query for " + df_.fun.name)
    tmp.println()

    for (cmd <- q.cmds)
      dump(tmp, cmd)
    tmp.println()

    for (cmd <- df_.cmds)
      dump(tmp, cmd, true)

    tmp.println("; lemma ")
    dump(tmp, eq, true)

    tmp.close()

    val m = predefined.count { line =>
      line.startsWith(("(assert"))
    }

    val n = axioms.count {
      case _: Assert => true
      case _         => false
    }

    val skip = m + n

    val (in, out, err, proc) =
      Tool.pipe("./ind", "--to", "10", "--defs", skip.toString, file)

    var solutions: List[List[Rule]] = Nil

    var line = out.readLine()
    while (line != null) {
      while (line != null && line != "model:") {
        if (line startsWith "replacing")
          println(line)
        line = out.readLine()
      }
      println()

      if (line == "model:") {
        println("solved")
        line = out.readLine()
        var text = new StringBuilder
        while (line != null && line.trim.nonEmpty) {
          text append line
          line = out.readLine()
        }

        val st1 = st0.copy()
        val text_ = text.toString
        val reader = new StringReader(text_)
        val from = cuvee.trace("scanning:\n" + text_) {
          cuvee.sexpr.parse(reader)
        }
        val from_ = from map (_ replace renaming)
        val res = cuvee.trace("parsing:\n" + from_) {
          cuvee.smtlib.parse(from_, st1)
        }

        val eqs =
          for (DefineFun(name, xs, res, rhs, false) <- res)
            yield {
              val fun = st1 funs name
              val lhs = App(fun, xs)
              val eq = Rule(lhs, rhs)
              eq
            }

        solutions = eqs :: solutions
      }
    }

    solutions
  }
}
