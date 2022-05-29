package cuvee.a

import cuvee.pure._
import java.io.PrintStream
import cuvee.smtlib.Cmd

class Config {
  var fuse = false
  var promote = false
  var variants: Set[String] = Set()
}

class Lemma(cmds: List[Cmd], defs: List[Def], st: State, cfg: Config)
    extends Database {

  var lemmas: List[Rule] = Nil
  var promotion: List[(Fun, Query, Def, Rule)] = Nil

  var formulas: List[(Expr, Expr, Expr)] = Nil
  var equations: List[(Expr, Expr)] = Nil

  def normalize_(df: Def, root: Boolean) {
    Hoist.static(df) match {
      case None =>
        unused_(df, root)
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
        // println("  internalize: " + df.fun + " (keep = "  + keep + ")")
        val kept = internalize(df, keep)

        if (kept) {
          // maybe recognize the identity function,
          // such that we can push the lemma instance to the front
          for (
            (su, eq @ Rule(lhs, rhs, cond, avoid)) <- _known(df, identities)
          ) {
            for ((ty_, su_, rhs_) <- instances(rhs, templates map (_.lhs inst su)) if su_.nonEmpty) {
              val lhs_ = lhs subst su_
              // TODO: this is ugly! cannot link the rhs directly via instances
              val rw = templates.groupBy(_.fun)
              val rhs__ = Rewrite.rewrite(rhs_, rw)
              // println(lhs_ + " == " + rhs__)
              val eq = Rule(lhs_, rhs__)
              rewriteBy(eq)
              println("(1) adding lemma: " + eq)
              lemmas = eq :: lemmas
            }
          }
        }

      case Some(eq) =>
        replaceBy(eq)
    }
  }

  def promote_(df: Def) {
    // currently this generates a lemma of the form:
    // length'(x₀, x₁, x₂) = (length''(x₀, x₁, x₂) + 0)
    // which does not put 0 into the correct *argument* in the rec. call
    for ((q, df_, eq) <- Promote.results(df)) {
      promotion = (df.fun, q, df_, eq) :: promotion

      if (cfg.promote) {
        val possible =
          try {
            Promote.query(q, df_, eq, cmds, defs, st)
          } catch {
            case e: Exception =>
              e.printStackTrace()
              Nil
          }

        for ((res, i) <- possible.zipWithIndex) {
          val rws = res.groupBy(_.fun)

          val Def(f_, cs) = df_
          val f__ = f_ rename indexed(i)
          val cs_ =
            for (C(args, guard, body) <- cs)
              yield {
                val args_ = Rewrite.rewrites(args, rws)
                val guard_ = Rewrite.rewrites(guard, rws)
                val body_ = Rewrite.rewrite(body, rws)
                C(args_, guard_, body_ replace (f_, f__))
              }

          val df__ = Def(f__, cs_)
          println(df__)
          normalize_(df__, false)

          println("  rewrites:  " + rws)

          val rhs_ = eq.rhs replace (f_, f__)
          val eq_ = Rewrite.rewrite(eq copy (rhs = rhs_), rws)
          println("  promotion: " + eq_)
          println("             " + eq_ + " (after normalizing)")
          // unfoldOnceBy(eq_)
          rewriteBy(eq_)
          println()
          println()
        }
      }
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

    if (cfg.variants contains "negated") {
      if (df.typ == Sort.bool) {
        for (eq <- Variant.negated(df))
          println(eq)
        // for(df_neg_ <- df_neg)
        //   normalize_(df_neg_, false)
        // recoverBy(eq)
      }
    }
  }

  def generateIdentities() {
    for ((name, dt) <- st.datatypes) {
      val ty = st.sort(name, dt.params)
      val Rule(lhs, rhs, True, Nil) = internalize(ty, dt)
      // equations = (lhs, rhs) :: equations
    }
  }

  def generateVariants() {
    val todo = definitions
    for (df <- todo)
      variants_(df)
  }

  def generatePromotions() {
    val todo = definitions
    for (df <- todo)
      promote_(df)
  }

  def generateLemmas() {
    for (
      (lhs, rhs) <- equations;
      (ty, su, lhs_) <- instances(lhs, recovery map (_.rhs))
    ) {
      // println("instantiating " + lhs + " == " + rhs)
      // println("found match: " + ty + " and " + su)
      // println("lhs_ = " + lhs_)
      println()
      for (rhs_ <- recover(rhs subst (ty, su)))
        (lhs, rhs_) match {
          case (_, `lhs`) =>

          case _ =>
            val eq = Rule(lhs, rhs_)
            // println("generated lemma instance: " + eq)

              println("(2) adding lemma: " + eq)
            lemmas = eq :: lemmas
        }
    }

    for (
      (lhs, rhs, cond) <- formulas;
      (ty, su, lhs_) <- instances(lhs, recovery map (_.rhs))
    ) {
      // println("  " + lhs + " for " + su)
      for (
        lhs__ <- recover(lhs_);
        rhs_ <- recover(rhs subst (ty, su));
        cond_ <- recover(cond subst (ty, su))
      ) (lhs__, rhs_, cond_) match {
        case (_, True, `lhs__`)     =>
        case (_, False, Not(`lhs`)) =>
        case _ =>
          val eq = Rule(lhs__, rhs_, cond_)
          if (!(lemmas contains eq)) {

              println("(3) adding lemma: " + eq)
            lemmas = eq :: lemmas
          }
        // else
        // println("  duplicate: " + eq)
        // println("recovered: " + eq)
        // if(ty.nonEmpty)
        //   println("  ty:    " + ty)
        // if(su.nonEmpty)
        //   println("  su:    " + su)
        // println("  lhs:   " + lhs)
        // println("  lhs':  " + lhs_)
        // println("  lhs\":  " + lhs__)
        // println("  rhs:   " + rhs)
        // println("  rhs':  " + rhs_)
        // println("  cond:  " + cond)
        // println("  cond': " + cond_)
      }
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
