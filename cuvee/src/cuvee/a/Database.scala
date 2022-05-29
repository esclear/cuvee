package cuvee.a

import cuvee.pure._
import arse.Backtrack

class Database {
  var generalized: Set[Fun] = Set()
  var replaced: Set[Fun] = Set()

  var identities: List[Def] = Nil
  var templates: List[Rule] = Nil
  var definitions: List[Def] = Nil
  var normalization: List[Rule] = Nil
  var recovery: List[Rule] = Nil
  var unfoldOnce: List[Rule] = Nil

//   var recognized: List[(String, String)] = Nil

  def internalize(ty: Sort, dt: Datatype) = {
    val (df, eq) = Cleanup.identityFor(ty, dt)
    identities = df :: identities
    templates = eq :: templates
    eq
  }

  // add a definition to the database as is, possibly merging it with existing ones,
  // and adding constant/identity lemmas if needed
  // if keep is true then prefer the function of df one over existing defs
  // it is generally assumed that this function has been hoisted
  def internalize(df: Def, keep: Boolean) = {
    val f = df.fun

    for ((su, eq) <- _known(df, definitions)) {
      if (keep) {
        require(
          eq.canFlip,
          "preferring: " + f + ", but cannot flip rule: " + eq
        )
        replaceBy(eq.flip)
      } else {
        replaceBy(eq)
      }
    }

    if (!replaced(f)) {
      definitions = df :: definitions
      normalization = df.rules ++ normalization
      true
    } else {
      false
    }
  }

  // remove definition of f again, because it has been generalized,
  // or because it has been replaced
  def remove(f: Fun) {
    definitions = definitions filterNot (_.fun == f)
  }

  // replace an existing definition with a new one given by eq,
  // this rule must be guaranteed to be reversible
  def generalizeBy(eq: Rule) {
    val f = eq.fun
    require(!generalized(f), "generalizing again: " + f)
    require(!replaced(f), "generalizing, but already repalced: " + f)
    require(eq.canFlip, "generalizing, but cannot flip rule: " + eq)
    generalized += f
    remove(f)
    normalization = eq :: normalization
    recovery = eq.flip :: recovery
  }

  def rewriteBy(eq: Rule) {
    normalization = eq :: normalization
  }

  def unfoldOnceBy(eq: Rule) {
    unfoldOnce = eq :: unfoldOnce
  }

  // add a recovery rule, e.g. from fusion
  def recoverBy(eq: Rule) {
    require(eq.canFlip, "recovery by, but cannot flip rule: " + eq)
    recovery = eq.flip :: recovery
  }

  // replace an existing definition with a new one given by eq,
  // this rule will not be used reversed
  def replaceBy(eq: Rule) {
    val f = eq.fun
    require(!replaced(f), "replacing again: " + f)
    require(!generalized(f), "replacing, but already generalized: " + f)
    // require(eq.canFlip, "replacing, but cannot flip rule: " + eq)
    replaced += f
    remove(f)
    // println("  replacing " + f)
    normalization = eq :: normalization
  }

  // put e into normal form wrt. the current state
  def normalized(e: Expr): Expr = {
    val rws = normalization.groupBy(_.fun)
    Rewrite.rewrite(e, rws)
  }

  // put right hand side and guard of r into normal form wrt. the current state
  // def normalized(r: Rule): Rule = {
  //   val rws = normalization.groupBy(_.fun)
  //   val Rule(lhs, rhs, cond, avoid) = r
  //   val _rhs = Rewrite.rewrite(rhs, rws)
  //   val _cond = Rewrite.rewrite(cond, rws)
  //   Rule(lhs, _rhs, _cond, avoid)
  // }

  // def normalized(df: Def): Def = {
  //   val rws = normalization.groupBy(_.fun)
  //   val Def(f, cs) = df
  //   val cs_ =
  //     for (C(args, guard, body) <- cs)
  //       yield {
  //         val args_ = Rewrite.rewrites(args, rws)
  //         val guard_ = Rewrite.rewrites(guard, rws)
  //         val body_ = Rewrite.rewrite(body, rws)
  //         C(args_, guard_, body_)
  //       }

  //   Def(f, cs_)
  // }

  def instances(e: Expr, patterns: List[Expr]): List[(Map[Param, Type], Map[Var, Expr], Expr)] = {
    val e_ = normalized(e)

    val res = for (p <- patterns) yield try {
      val (ty, su) = Expr.bind(e_, p)
      Some((ty, su, e_ subst (ty, su)))
    } catch {
      case e: Backtrack =>
        println(e.message)
        None
    }

    // TODO: check why this!
    // val std = (Map[Param, Type](), Map[Var, Expr](), e_)
    // std :: res.flatten
    res.flatten
  }

  // find equivalence class of e
  def recover(e0: Expr, verbose: Boolean = false): List[Expr] = {
    val rws1 = normalization.groupBy(_.fun)
    // val rws2 = unfoldOnce.groupBy(_.fun) // assume these are not cyclic!
    val rws3 = recovery.groupBy(_.fun)
    println("  0. " + e0)
    val e1 = Rewrite.rewrite(e0, rws1)
    println("  1. " + e1)
    // val e2 = Rewrite.rewrite(e1, rws2)
    // println("  2. " + e2)
    val es3 = Rewrite.rewriteAll(e1, rws3)
    println("  3. " + es3)
    // println()
    es3
  }

  def _known(df: Def, defs: List[Def]) = {
    for (
      dg <- defs;
      eq <- Known.known(df, dg)
    )
      yield eq
  }
}
