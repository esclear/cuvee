package cuvee.a

import arse.Control
import cuvee.pure._
import cuvee.backtrack

object Known {
  def main(args: Array[String]) {}

  def key(f: Fun)(c: C) = c match {
    case C(_, _, App(inst, args)) if inst.fun == f =>
      None // tail-recursive calls: delay matching

    case C(_, _, x: Var)          => None
    case C(_, _, App(inst, args)) => Some(inst.fun)
  }

  def prio(a: Option[Fun], b: Option[Fun]) = (a, b) match {
    case (None, None)       => true // stable
    case (None, Some(_))    => false
    case (Some(_), None)    => true
    case (Some(a), Some(b)) => a.name < b.name
  }

  def bind(
      cf: List[
        (C, Int)
      ], // the numbers are the ordering of cases in the definition
      cg: List[(C, Int)],
      p: List[Int],
      ty: Map[Param, Type],
      su: Map[Var, Expr] = Map()
  ) = {}

  def check(
      cases: List[(List[(C, Int)], List[(C, Int)])],
      p: List[Int] = Nil, // permutation that reorders function arguments
      ty: Map[Param, Type] = Map() // typing applies to the entire function
  ): List[(List[Int], Map[Param, Type])] =
    cases match {
      case Nil =>
        List((p, ty))

      case (fs, gs) :: rest if fs.length != gs.length =>
        Nil

      case (fs, gs) :: rest =>
        check(rest)
    }

  def invert(a: List[Int]) = {
    val b = a.zipWithIndex
    val c = b.sortBy(_._1)
    val (_, d) = c.unzip
    d
  }

  def foo(f: Fun, i: Int, cs: List[C]): Int = {
    val ks = cs.zipWithIndex collect {
      case (C(args, guard, x: Var), k) if (args indexOf x) == i =>
        k
    }

    ks match {
      case Nil => 0
      case List(k) =>
        k
      case _ =>
        println("  multiple occurrences of argument at " + i)
        println("  " + f)
        println("  " + ks.mkString(" "))
        ks.sum
    }
  }

  // dg is known already and we want to check whether df matches
  def known(df: Def, dg: Def): Option[Rule] = {
    if (
      df.fun != dg.fun &&
      df.fun.args.length == dg.fun.args.length &&
      // df.fun.args == dg.fun.args &&
      // df.fun.args == dg.fun.args &&
      // df.fun.res == dg.fun.res &&
      df.cases.length == dg.cases.length
    ) {
      val Def(f, fcases) =
        df // Check: can we guarantee order via fuse/factoring maintained?
      val Def(g, gcases) = dg

      // println(df.fun.name + "#" + Def.hash(df) + " ?= " + dg.fun.name + "#" + Def.hash(dg))
      // val x = cuvee.keyedPairings(fcases, gcases, key(f), key(g), prio)
      // val y = check(x)

      val fcases_ = fcases.sortBy(Def.hash(f, _))
      val gcases_ = gcases.sortBy(Def.hash(g, _))

      val F = f.args.zipWithIndex.sortBy { case (t, i) =>
        Def.hash(t) -> foo(f, i, fcases_)
      }
      val G = g.args.zipWithIndex.sortBy { case (t, i) =>
        Def.hash(t) -> foo(g, i, gcases_)
      }
      val (ftypes, fp) = F.unzip
      val (gtypes, gp) = G.unzip
      val ok_ =
        (fcases_ zip gcases_) forall { case (cf, cg) =>
          {
            val su = Type.binds(ftypes, g.res, gtypes, f.res, Map())

            val C(fargs, fguard, fbody) = cf
            val C(gargs, gguard, gbody) = cg inst su

            val res = ok(
              f,
              fp,
              fargs,
              fguard,
              fbody,
              g,
              gp,
              gargs,
              gguard,
              gbody,
              su
            )

            // println("  = " + res)
            res
          } or {
            false
          }
        }

      if (ok_) {
        val xs = Expr.vars("x", ftypes)
        val fm = invert(fp)
        val gm = invert(gp)

        val lhs = App(f, fm map xs)
        val rhs = App(g, gm map xs)
        val eq = Rule(lhs, rhs, True)

        // println("representation: " + eq)
        Some(eq)
      } else {
        if (Def.hash(df) == Def.hash(dg)) {
          println(
            "  potentially missed equivalence " + f.name + " == " + g.name
          )
        }

        None
      }
    } else {
      None
    }
  }

  def ok(
      f: Fun,
      fp: List[Int],
      fargs: List[Expr],
      fguard: List[Expr],
      fbody: Expr,
      g: Fun,
      gp: List[Int],
      gargs: List[Expr],
      gguard: List[Expr],
      gbody: Expr,
      su: Map[Param, Type]
  ): Boolean = {
    // println("checking ")
    // println(fargs.mkString(" ") + ". " + fbody)
    // println(gargs.mkString(" ") + ". " + gbody)

    var ok = true
    var re: Map[Var, Var] = Map()

    def rename(a: Expr, b: Expr): Unit = (a, b) match {
      case (x: Var, y: Var) =>
        re += (x -> y)
      case (App(Inst(f, fs), as), App(Inst(g, gs), bs)) if f == g =>
        renames(as, bs)
      case _ =>
        // println("no match: " + a + " != " + b)
        ok = false
    }

    def renames(as: List[Expr], bs: List[Expr]): Unit = (as, bs) match {
      case (Nil, Nil) =>
      case (a :: as, b :: bs) =>
        rename(a, b)
        renames(as, bs)
    }

    renames(fp map fargs, gp map gargs)

    if (ok) {
      val _fguard = fguard rename re
      val _gguard = gguard rename re

      val _fbody = fbody rename re bottomup {
        case App(Inst(`f`, _), args) => App(Inst(g, su), fp map args)
        case e                       => e
      }

      val _gbody = gbody rename re bottomup {
        case App(Inst(`g`, _), args) => App(Inst(g, su), gp map args)
        case e                       => e
      }

      ok = _fguard == _gguard && _fbody == _gbody

      if (!ok && _fguard != _gguard)
        println("; guards different: " + _fguard + " and " + _gguard)
      if (!ok && _fbody != _gbody)
        println("; bodies different: " + _fbody + " and " + _gbody)
    }

    ok
  }
}
