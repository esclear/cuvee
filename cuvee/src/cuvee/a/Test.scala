package cuvee.a

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._

object debug extends Run(Test, "examples/debug.smt2")

object _0 extends Run(Test, "examples/0.smt2")
object _1 extends Run(Test, "examples/1.smt2")
object _2 extends Run(Test, "examples/2.smt2")
object _7 extends Run(Test, "examples/7.smt2")

object list_defs extends Run(Test, "examples/list-defs.smt2")

object Test extends Main {
  val out = log("log.txt")

  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (dfs, constrs, st) = read(file)

    val lemma = new Lemma()

    for (df <- dfs) {
      lemma.addOriginal(df)
    }

    for (
      df <- dfs; dg <- dfs;
      (dh, eq) <- Fuse.fuse(df, dg, constrs)
    ) yield {
      lemma.addFused(dh, eq)
    }

    lemma.generateLemmas()

    dump("normalization", lemma.normalization)
    dump("recovery", lemma.recovery)
    dump("lemmas", lemma.lemmas)
    // dump("recognized", lemma.recognized)
  }

  def dump(section: String, stuff: List[Any]) {
    out.println(section)
    for (item <- stuff)
      out.println("  " + item)
    out.println()
  }
}
