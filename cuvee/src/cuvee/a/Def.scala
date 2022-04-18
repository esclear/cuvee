package cuvee.a

import cuvee.error
import cuvee.pure._
import cuvee.smtlib._

case class C(args: List[Expr], guard: List[Expr], body: Expr) {
  def typ = body.typ
  def flat(self: Fun) = this

  def rename(re: Map[Var, Var]) = {
    C(args rename re, guard rename re, body rename re)
  }

  def inst(su: Map[Param, Type]) = {
    C(args inst su, guard inst su, body inst su)
  }

  def rule(self: Fun): Rule = {
    Rule(App(self, args), body, And(guard))
  }

  def axiom(self: Fun) = {
    val xs = args.free.toList
    Clause(xs, guard, Eq(App(self, args), body))
  }

  def isRecursive(fun: Fun): Boolean =
    fun in body

  def isTailRecursive(fun: Fun): Boolean =
    body match {
      case App(Inst(`fun`, _), args) =>
        true
      case _ =>
        false
    }

  override def toString = {
    if (guard.isEmpty)
      args.mkString("case ", ", ", "") + "\n  = " + body
    else
      args.mkString("case ", ", ", " if ") + guard.mkString(
        " /\\ "
      ) + "\n  = " + body
  }
}

case class Def(fun: Fun, cases: List[C]) {
  for (cs <- cases) {
    require(
      fun.args == cs.args.types,
      "type mismatch: " + fun + " applied to " + cs.args
    )
    require(
      fun.res == cs.typ,
      "type mismatch: " + fun + " in case " + cs + ": " + cs.typ
    )
  }

  def typ = fun.res

  def rules =
    cases map (_ rule fun)

  def map(f: C => C): Def =
    Def(fun, cases map f)

  def cmds =
    decl :: axioms

  def decl = {
    val Fun(name, Nil, args, res) = fun
    DeclareFun(name, args, res)
  }

  def axioms = {
    cases map (cs => Assert(cs axiom fun))
  }

  object Norm {
    def unapply(c: C) = {
      val C(args, guard, body) = c
      val ((d, r), (as, bs, cs)) = Split.split(fun, body)
      Some((args, guard, as, bs, cs, d))
    }
  }

  override def toString = {
    fun + cases.mkString("\n", "\n", "")
  }
}

object Def {
  def rw(
      xs: List[Var],
      guard: List[Expr],
      inst: Inst,
      args: List[Expr],
      x: Var,
      pat: Expr,
      body: Expr,
      st: State
  ): List[(Fun, C)] = {
    val su = Map(x -> pat)
    val _args = args subst su
    val _lhs = App(inst, _args)
    rw(xs ++ pat.free, guard, _lhs, body, st)
  }

  def rw(
      xs: List[Var],
      guard: List[Expr],
      lhs: App,
      rhs: Expr,
      st: State
  ): List[(Fun, C)] =
    (lhs, rhs) match {
      case (_, Ite(test, left, right)) =>
        val l = rw(xs, test :: guard, lhs, left, st)
        val r = rw(xs, Not(test) :: guard, lhs, right, st)
        l ++ r

      case (App(inst, args), Or(List(test, expr))) => // TODO: generalize
        val l = rw(xs, test :: guard, lhs, True, st)
        val r = rw(xs, Not(test) :: guard, lhs, expr, st)
        l ++ r

      case (App(inst, args), And(List(test, expr))) => // TODO: generalize
        val l = rw(xs, test :: guard, lhs, expr, st)
        val r = rw(xs, Not(test) :: guard, lhs, False, st)
        l ++ r

      case (App(inst, args), Match(x: Var, cases, typ)) if xs contains x =>
        for (
          Case(pat, body) <- cases;
          res <- rw(xs, guard, inst, args, x, pat, body, st)
        )
          yield res

      case (App(inst, args), Match(x, cases, typ)) =>
        error("cannot lift match statement: " + rhs)

      case (App(inst, args), rhs) =>
        List((inst.fun, C(args, guard, rhs)))

      case _ =>
        Nil
    }

  def rw(
      name: String,
      xs: List[Var],
      res: Type,
      body: Expr,
      st: State
  ): List[(Fun, C)] = {
    val fun = st funs name
    val lhs = App(fun, xs)
    rw(xs, Nil, lhs, body, st)
  }

  // TODO: inefficient?
  def rw(expr: Expr, st: State): List[(Fun, C)] =
    expr match {
      case Clause(xs, ant, Eq(lhs: App, rhs)) =>
        rw(xs, ant, lhs, rhs, st)

      case Clause(xs, ant, Not(lhs: Bind)) =>
        Nil

      case Clause(xs, ant, Not(lhs: App)) =>
        rw(xs, ant, lhs, False, st)

      case Clause(xs, ant, lhs: App) =>
        rw(xs, ant, lhs, True, st)

      case _ =>
        Nil
    }

  def rw(exprs: List[Expr], st: State): List[(Fun, C)] = {
    for (
      expr <- exprs;
      rule <- rw(expr, st)
    )
      yield rule
  }

  import scala.util.hashing.MurmurHash3
  val paramSeed = "Param".hashCode
  val varSeed = "Var".hashCode

  def hash(t: Type): Int = t match {
    case p: Param =>
      paramSeed
    case Sort(con, args) =>
      MurmurHash3.orderedHash(hash(args), con.hashCode())
  }

  def hash(t: Type, seed: Int): Int ={
    MurmurHash3.mix(hash(t), seed)
  }

  def hash(ts: List[Type]): List[Int] = {
    ts map (hash(_))
  }

  // weak hash function that captures the structure
  // but not the actual computation
  // it forgets variable names,
  // function name and order of arguments for recursive calls,
  // as well as all type instances
  def hash(f: Fun, e: Expr): Int = e match {
    case x: Var =>
      varSeed
    case App(Inst(`f`, _), args) =>
      MurmurHash3.unorderedHash(hash(f, args))
    case App(Inst(g, _), args) =>
      MurmurHash3.orderedHash(hash(f, args), g.name.hashCode())
  }

  def hash(f: Fun, es: List[Expr]): List[Int] = {
    es map (hash(f, _))
  }

  def hashs(f: Fun, es: List[Expr]): Int = {
    MurmurHash3.orderedHash(es map (hash(f, _)))
  }

  def hash(f: Fun, c: C): Int = c match {
    case C(args, guard, body) =>
      val h1 = hash(f, body)
      val h2 = MurmurHash3.unorderedHash(hash(f, args), h1)
      val h3 = MurmurHash3.unorderedHash(hash(f, guard), h2)
      h3
  }

  def hash(df: Def): Int = df match {
    case Def(f, cases) =>
      MurmurHash3.unorderedHash(cases map (hash(f, _)))
  }
}
