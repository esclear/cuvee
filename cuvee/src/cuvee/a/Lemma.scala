package cuvee.a

import cuvee.error
import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._
import java.io.File
import java.io.BufferedWriter
import java.io.FileWriter

object Lemma extends Main {
  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (cmds, st) = parse(file)

    for (
      DeclareDatatypes(arities, dts) <- cmds;
      ((name, arity), dt) <- arities zip dts
    ) {
      st.datatype(name, dt)
    }

    val lemma = new Lemma(st)
    lemma.seed(cmds)
    // lemma.prove(cmds)
    // println()
    lemma.dump()
  }
}

class Lemma(st: State) {
  val constrs = {
    for (
      (_, dt) <- st.datatypes;
      (c, _) <- dt.constrs
    )
      yield c
  }.toSet

  // println("contstrs = " + constrs)

  // original functions that are part of the source theory
  // use these preferably during normalization,
  // and use these during lemma generation
  var original: Set[Fun] = Set()

  // definitions that are still to be incorporated
  var todo: List[Def] = Nil

  // definitions that are needed to explain the semantics
  // of those functions which are in fact used
  var definitions: Map[Fun, Def] = Map()

  // definitions that failed to normalize before,
  // try again later perhaps
  var failed: List[Def] = Nil

  // rules that perform normalization,
  // applied when internalizing a definition,
  // typically only a single rule per function
  var normalization: Map[Fun, List[Rule]] = Map()

  // fusion rules
  var fusion: Map[Fun, List[Rule]] = Map()

  // reverse normalization rules,
  // which recover expressions in terms of the original definitions
  var recovery: Map[Fun, List[Rule]] = Map()

  // promotion rules, these are not necessarily good rewrite rules
  var promotion: Map[Fun, Rule] = Map()

  // discovered lemmas, all in terms of the original functions
  // note, these may have to be subjected to rewriting
  var lemmas: List[Expr] = Nil

  def dump() {
    // println("definitions:")
    // for (
    //   (fun, df) <- definitions;
    //   rule <- df.rules
    // )
    //   println("  " + rule)
    // println()
    val candidates = normalization.toList ++ fusion.toList
    val reverted_ =
      for (
        (fun, rules) <- candidates;
        rule <- rules if rule.canFlip
      ) yield {
        rule.flip
      }

    val reverted = reverted_.groupBy(_.fun)

    /* println("fusion rules:")
    for (
      (_, rules) <- fusion;
      rule <- rules
    ) {
      val Rule(lhs, rhs, cond, avoid) = rule
      // println("  " + rule)
      val rhs_ = Rewrite.rewrite(rhs, normalization)
      val cond_ = Rewrite.rewrite(cond, normalization)
      val rule_ = Rule(lhs, rhs_, cond_, avoid)
      println("  " + rule)
    }
    // for(rhs__ <- Rewrite.rewriteAll(rhs_, reverted))
    // println("  ... = " + rhs__)
    println() */

    // println("normalization rules:")
    // for (
    //   (_, rules) <- normalization;
    //   rule <- rules
    // )
    //   println("  " + rule)
    // println()

    // println("reverted rules:")
    // for (
    //   (_, rules) <- reverted;
    //   rule <- rules
    // )
    //   println("  " + rule)
    // println()

    // println("normalization lemmas")
    // for (
    //   (f, rules) <- candidates
    //   if (original contains f) || (fusion contains f);
    //   Rule(lhs, rhs, cond, avoid) <- rules
    // ) {
    //   val rhs_ = Rewrite.rewrite(rhs, normalization)
    //   try {
    //     val results = Rewrite.rewriteAll(rhs_, reverted)
    //     for (rhs__ <- results.distinct if lhs != rhs__) {
    //       val rule__ = Rule(lhs, rhs__, cond, avoid)
    //       println("  " + rule__)
    //     }
    //   } catch {
    //     case _: StackOverflowError =>
    //       println("  " + lhs + " = ? (stack overflow)")
    //   }
    // }

    // println("conditional lemmas:")
    // for (expr <- lemmas) {
    //   val expr_ = Rewrite.rewrite(expr, normalization)
    //   println("  " + expr_)
    // }
    // println()

    println("promotion queries:")
    val dir = new File("queries/")
    dir.mkdirs()

    for ((f, df) <- definitions) {
      val (q, df_, eq) = Promote.results(df)

      val file = new File("queries/" + f.name + ".smt2")
      val wr = new BufferedWriter(new FileWriter(file))

      for (
        cmd <- q.cmds;
        line <- cmd.lines
      ) {
        wr.write(line)
        wr.newLine()
      }

      wr.close()
    }
  }

  def seed(cmds: List[Cmd]) {
    val eqs0 =
      for (
        Assert(expr) <- cmds;
        eq <- Def.rw(expr, st)
      )
        yield eq

    val eqs1 =
      for (
        DefineFun(name, formals, res, body, _) <- cmds;
        eq <- Def.rw(name, formals, res, body, st)
      )
        yield eq

    val eqs = eqs0 ++ eqs1

    val dfs =
      for ((fun, stuff) <- eqs.groupBy(_._1))
        yield {
          val (_, cases) = stuff.unzip
          Def(fun, cases)
        }

    todo ++= dfs

    for (df <- dfs) {
      original += df.fun
      fusion += df.fun -> Nil
    }
    val dhs =
      for (
        df <- dfs; dg <- dfs;
        (dh, eq) <- Fuse.fuse(df, dg, constrs)
      ) yield {
        original += df.fun
        fusion += df.fun -> (fusion(df.fun) ++ List(eq))
        dh
      }

    todo ++= dhs

    for ((name, dt) <- st.datatypes) {
      val typ = st.sort(name, dt.params)
      val (df, eq) = Cleanup.identityFor(typ, dt)
      normalization += df.fun -> List(eq)
      definitions += df.fun -> df
    }
    println()

    processAll()
  }

  def processAll() {
    while (todo.nonEmpty)
      process()
  }

  // look at all functions from todo
  def process() {
    val now = todo
    todo = Nil

    for (df0 <- now) {
      val df1 = rewrite(df0)

      normalize(df1) match {
        case None =>
          // df1 already in normal form
          cleanup(df1) match {
            case (Nil, Nil) =>
              val kept = internalize(df1)

              if (false && kept) {
                if (df1.fun.res == Sort.bool) {} else {
                  for ((dp, dg, eq) <- Variant.restricted(df1)) {
                    lemmas ++= List(eq)
                    todo ++= List(dp, dg)
                  }
                }
              }

            case (aux, eqs) =>
              todo ++= aux
              normalization += df1.fun -> eqs
          }
        case Some((aux, eq)) =>
          todo ++= aux
          normalization += df1.fun -> List(eq)
      }
    }
  }

  // returns
  // - None if the definition is already in normal form
  // - Some((defs, eq)) if df can be rewritten, using a *single* rule in terms of the new definitions
  def normalize(df: Def): Option[(List[Def], Rule)] = {
    Hoist.static(df) match {
      case None =>
        None
      case Some((df_, y)) =>
        // in the future, there will be multiple defs involved (forward args)
        Some((List(df_), y))
    }
  }

  // apply all rewrites to the body of df
  def rewrite(df: Def): Def = {
    df map { case C(args, guard, body) =>
      val guard_ = Rewrite.rewrites(guard, normalization)
      val body_ = Rewrite.rewrite(body, normalization)
      C(args, guard_, body_)
    }
  }

  // df must be normalized and rewritten
  // result indicates whether this definition is kept
  def internalize(df: Def) = {
    known(df) match {
      case Nil =>
        // no such definition is known yet
        // println("new definition: " + df.fun)
        definitions += df.fun -> df
        normalization += df.fun -> df.rules
        true

      /* case List(eq) if original contains df.fun =>
        val eq_ = eq.flip
        // println("known definition: " + eq_.fun)
        // println("keeping original definition: " + df.fun)
        // for original functions, prefer original name
        definitions += df.fun -> df
        definitions -= eq_.fun
        normalization += df.fun -> List(eq_) */

      case List(eq) =>
        // println("known definition: " + df.fun)
        // add the rule that replaces df
        normalization += df.fun -> List(eq)
        false

      case eqs =>
        // a prior opportunity for normalization has not been detected (bug)
        error(
          "should not happen: multiple representatives for " + df + ": " + eqs
        )
    }
  }

  def known(df: Def): List[Rule] = {
    val eqs =
      for (
        (_, dg) <- definitions;
        eq <- Known.known(df, dg)
      )
        yield eq

    eqs.toList
  }

  def promote(df: Def): (List[Def], List[Rule]) = {
    ???
  }

  // - remove unused parameters, possibly generating a new definition
  // - recognize constant functions
  def cleanup(df0: Def): (List[Def], List[Rule]) = {
    var df = df0
    var dfs: List[Def] = Nil
    var eqs: List[Rule] = Nil

    for ((df1, eq) <- Unused.unused(df)) {
      df = df1 // continue with simplified definition
      dfs ++= List(df)
      eqs ++= List(eq)
    }

    // this is done alternatively by including an identity function for each type
    // which is recognized during internalization
    // for (eq <- Cleanup.identity(df)) {
    //   eqs ++= List(eq)
    // }

    for (eq <- Cleanup.constant(df)) {
      eqs ++= List(eq)
    }

    (dfs, eqs)
  }
}
