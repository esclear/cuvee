package cuvee.a

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._

object debug extends Run(Test, "examples/debug.smt2")

object _0 extends Run(Test, "-fuse", "examples/0.smt2")
object _1 extends Run(Test, "-fuse", "examples/1.smt2")
object _2 extends Run(Test, "-fuse", "-variants", "cases", "examples/2.smt2")
object _7 extends Run(Test, "-fuse", "-variants", "cases", "examples/7.smt2")
object _8 extends Run(Test, "-fuse", "-variants", "cases", "examples/8.smt2")

object list_defs extends Run(Test, "-fuse", "-variants", "cases", "examples/list-defs.smt2")

object Test extends Main {
  var out = log("log.txt")

  def configure(cfg: Config, args: List[String]): List[String] = args match {
    case Nil =>
      Nil

    case "-fuse" :: rest =>
      cfg.fuse = true
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
      val (dfs, st) = read(file)
      val lemma = new Lemma(st, cfg)

      lemma.addOriginal(dfs)
      lemma.generateVariants()
      lemma.generateLemmas()

      dump("lemmas", lemma.lemmas)
      dump("recovery", lemma.recovery)
      dump("normalization", lemma.normalization)
    }
  }

  def dump(section: String, stuff: List[Any]) {
    out.println(section)
    for (item <- stuff)
      out.println("  " + item)
    out.println()
  }
}
