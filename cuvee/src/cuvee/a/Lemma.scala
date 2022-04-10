package cuvee.a

import cuvee.pure._

class Lemma extends Database {
  var lemmas: List[Rule] = Nil
  var exprs: List[(Expr, Expr)] = Nil

  def normalize_(df: Def, root: Boolean) {
    Hoist.static(df) match {
      case None =>
        unused_(df, true)
      case Some((df_, eq)) =>
        if (root)
          exprs = (eq.lhs, eq.lhs) :: exprs
        generalizeBy(eq)
        unused_(df_, false)
    }
  }

  def unused_(df: Def, keep: Boolean) {
    Unused.unused(df) match {
      case None =>
        constant_(df, keep)

      case Some((df_, eq)) =>
        replaceBy(eq)
        constant_(df_, false)
    }
  }

  def constant_(df: Def, keep: Boolean) {
    Cleanup.constant(df) match {
      case None =>
        internalize(df, keep)
      case Some(eq) =>
        replaceBy(eq)
    }
  }

  def generateLemmas() {
    for (
      (lhs, rhs) <- exprs;
      rhs_ <- recover(rhs)
    ) {
      if (lhs != rhs_) {
        val eq = Rule(lhs, rhs_)
        lemmas = eq :: lemmas
      }
    }
  }

  def addOriginal(df: Def) {
    normalize_(df, true)
  }

  def addFused(dh: Def, eq: Rule) {
    normalize_(dh, false)
    recoverBy(eq)
    exprs = (eq.lhs, eq.rhs) :: exprs
  }
}
