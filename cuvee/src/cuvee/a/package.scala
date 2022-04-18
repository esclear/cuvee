package cuvee

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._
import java.io.PrintStream
import java.io.FileOutputStream

package object a {
  def fused(index: Int)(name1: String, name2: String) = name1 + "_" + index + "_" + name2
  def hoisted(name: String) = name + "_"
  def removeunused(name: String) = name + "u"
  def promoted(index: Int)(name: String) = name + "p" + index
  def precondition(index: Int)(name: String) = name + "_pre" + index
  def casevariant(index: Int)(name: String) = name + "_c" + index
  def indexed(index: Int)(name: String) = name + index

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

  def log(file: String) = {
    new PrintStream(new FileOutputStream(file))
  }
}
