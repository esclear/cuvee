package cuvee

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._
import java.io.PrintStream
import java.io.FileOutputStream
import cuvee.sexpr.Syntax

package object a {
  def fused(index: Int)(name1: Name, name2: Name) = name1.toLabel + "_" + index + "_" + name2.toLabel
  def hoisted(name: Name) = name.toLabel + "_"
  def removeunused(name: Name) = name.toLabel + "u"
  def promoted(index: Int)(name: Name) = name .toLabel+ "p" + index
  def precondition(index: Int)(name: Name) = name.toLabel + "_pre" + index
  def casevariant(index: Int)(name: Name) = name.toLabel + "_c" + index
  def indexed(index: Int)(name: Name) = name.toLabel + index

  def read(file: String): (List[Def], List[Cmd], State) = {
    val (cmds, st) = parse(file)

    for (
      DeclareDatatypes(arities, dts) <- cmds;
      ((name, arity), dt) <- arities zip dts
    ) {
      st.datatype(name, dt)
    }

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

    (dfs.toList, cmds, st)
  }

  def dump(out: PrintStream, syntax: Syntax, comment: Boolean = false) {
    for (line <- syntax.lines) {
      if (comment)
        out.print("; ")
      out.println(line)
    }
    out.println()
  }

  def dump(out: PrintStream, section: String, stuff: List[Any]) {
    out.println(section)
    for (item <- stuff)
      out.println("  " + item)
    out.println()
  }

  def log(file: String) = {
    new PrintStream(new FileOutputStream(file))
  }

  /** The default printer to use: Prints s-expressions */
  implicit val printer: cuvee.util.Printer = cuvee.sexpr.Printer
}
