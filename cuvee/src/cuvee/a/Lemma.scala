package cuvee.a

import cuvee.pure._

class Config {
  var fuse = false
  var variants: Set[String] = Set()
}

class Lemma(st: State, cfg: Config) extends Database {

  var lemmas: List[Rule] = Nil

  var formulas: List[(Expr, Expr, Expr)] = Nil
  var equations: List[(Expr, Expr)] = Nil

  def normalize_(df: Def, root: Boolean) {
    Hoist.static(df) match {
      case None =>
        unused_(df, true)
      case Some((df_, eq)) =>
        if (root)
          equations = (eq.lhs, eq.lhs) :: equations
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

  def promote_(df: Def) {
    // currently this generates a lemma of the form:
    // length'(x₀, x₁, x₂) = (length''(x₀, x₁, x₂) + 0)
    // which does not put 0 into the correct *argument* in the rec. call
    return

    val (q, df_, eq) = Promote.results(df)
    Promote.arithmetic(q) match {
      case Some(res) =>
        val rws = res.groupBy(_.fun)

        val Def(f_, cs) = df_
        val cs_ =
          for (C(args, guard, body) <- cs)
            yield {
              val args_ = Rewrite.rewrites(args, rws)
              val guard_ = Rewrite.rewrites(guard, rws)
              val body_ = Rewrite.rewrite(body, rws)
              C(args_, guard_, body_)
            }

        val df__ = Def(f_, cs_)
        val eq_ = Rewrite.rewrite(eq, rws)
        println(eq_)
        normalize_(df__, false)
      // rewriteBy(eq_)

      case None =>
    }
  }

  def variants_(df: Def) {
    if (cfg.variants contains "cases") {
      for ((df_pre_, df_, phi) <- Variant.restricted(df)) {
        normalize_(df_pre_, false)
        normalize_(df_, false) // don't chain this
        val Rule(lhs, rhs, cond, _) = phi
        formulas = (lhs, rhs, cond) :: formulas
      }
    }
  }

  def generateVariants() {
    // promote_(df)
    val todo = definitions
    for(df <- todo)
      variants_(df)
  }

  def generateLemmas() {
    for (
      (lhs, rhs) <- equations;
      rhs_ <- recover(rhs)
    ) {
      if (lhs != rhs_) {
        val eq = Rule(lhs, rhs_)
        lemmas = eq :: lemmas
      }
    }

    for (
      (lhs, rhs, cond) <- formulas;
      lhs_ <- recover(lhs, true);
      rhs_ <- recover(rhs);
      cond_ <- recover(cond)
    ) {
      val eq = Rule(lhs_, rhs_, cond_)
      lemmas = eq :: lemmas
    }
  }

  def addOriginal(dfs: List[Def]) {
    for (df <- dfs) {
      addOriginal(df)
    }

    if (cfg.fuse) {
      for (
        df <- dfs; dg <- dfs;
        (dh, eq) <- Fuse.fuse(df, dg, st.constrs)
      ) yield {
        addFused(dh, eq)
      }
    }
  }

  def addOriginal(df: Def) {
    normalize_(df, true)
  }

  def addFused(dh: Def, eq: Rule) {
    normalize_(dh, false)
    recoverBy(eq)
    equations = (eq.lhs, eq.rhs) :: equations
  }
}
