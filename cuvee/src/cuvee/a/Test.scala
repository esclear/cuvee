package cuvee.a

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._
import java.io.File
import java.io.PrintStream
import cuvee.sexpr.Syntax

object contains extends Run(Test, "examples/contains.smt2")

object debug extends Run(Test, "examples/debug.smt2")

object _0 extends Run(Test, "-fuse", "examples/0.smt2")
object _1 extends Run(Test, "-fuse", "examples/1.smt2")
object _2 extends Run(Test, "-fuse", "examples/2.smt2")
object _2_variants
    extends Run(Test, "-fuse", "-variants", "cases", "examples/2.smt2")
object _7 extends Run(Test, "-fuse", "-variants", "cases", "examples/7.smt2")
object _8 extends Run(Test, "examples/8.smt2")
object _8_cases
    extends Run(Test, "-fuse", "-variants", "cases", "examples/8.smt2")
object _8_cases_only extends Run(Test, "-variants", "cases", "examples/8.smt2")

object _9_negated extends Run(Test, "-variants", "negated", "examples/9.smt2")

object _9_variants extends Run(Test, "-variants", "cases", "examples/9.smt2")

object list_defs extends Run(Test, "-fuse", "examples/list-defs.smt2")

object _append extends Run(Test, "-promote", "examples/append.smt2")

object list_defs_variants
    extends Run(Test, "-fuse", "-variants", "cases", "examples/list-defs.smt2")

object Test extends Main {
  var out = log("log.txt")

  def configure(cfg: Config, args: List[String]): List[String] = args match {
    case Nil =>
      Nil

    case "-fuse" :: rest =>
      cfg.fuse = true
      configure(cfg, rest)

    case "-promote" :: rest =>
      cfg.promote = true
      configure(cfg, rest)

    case "-variants" :: which :: rest =>
      cfg.variants += which
      configure(cfg, rest)

    case "-out" :: "--" :: rest =>
      out = System.out
      configure(cfg, rest)

    case "-out" :: file :: rest =>
      out = log(file)
      configure(cfg, rest)

    case first :: rest =>
      first :: configure(cfg, rest)
  }

  def main(args: Array[String]): Unit = {
    val cfg = new Config()
    val files = configure(cfg, args.toList)

    for (file <- files) {
      val (dfs, cmds, st) = read(file)
      val lemma = new Lemma(cmds, dfs, st, cfg)
      println(file)

      val goals =
        for ((Assert(Not(phi))) <- cmds)
          yield phi

      println("normalizing definitions...")
      lemma.addOriginal(dfs)

      println("collecting promotion queries...")
      lemma.generatePromotions()

      println("generating variants...")
      lemma.generateVariants()

      println("synthesizing lemmas...")
      lemma.generateLemmas()

      dump(out, "goals", goals)
      dump(out, "lemmas", lemma.lemmas.reverse)
      // dump(out, "definitions", lemma.definitions.reverse.flatMap(_.rules))
      dump(out, "recovery", lemma.recovery)
      dump(out, "normalization", lemma.normalization)
      // queries(lemma.promotion, lemma.definitions, cmds)

      println("done")
    }
  }

  def queries(
      qs: List[(Fun, Query, Def, Rule)],
      defs: List[Def],
      cmds: List[Cmd]
  ) {
    println("dumping queries...")

    val dir = new File("queries/")
    dir.mkdirs()

    {
      val out = log("queries/definitions.smt2")

      for (cmd @ DeclareSort(_, _) <- cmds) {
        dump(out, cmd)
      }

      for (cmd @ DeclareDatatypes(_, _) <- cmds) {
        dump(out, cmd)
      }

      for (df <- defs) {
        for (cmd <- df.cmds)
          dump(out, cmd)
      }
    }

    for ((g, q, dg, eq) <- qs) {
      val name = dg.fun.name

      // println("  " + name)

      val out = log("queries/" + name + ".smt2")

      out.println("; auxiliary definition")
      for (cmd <- dg.cmds)
        dump(out, cmd, comment = true)

      out.println("; promotion lemma")
      dump(out, eq.cmd, comment = true)

      for (cmd <- q.cmds)
        dump(out, cmd)

      out.close()
    }
  }

}
