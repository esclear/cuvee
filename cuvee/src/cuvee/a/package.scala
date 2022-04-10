package cuvee

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._
import java.io.PrintStream
import java.io.FileOutputStream

package object a {
  def read(file: String): (List[Def], Set[Fun], State) = {
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

    val constrs = {
      for (
        (_, dt) <- st.datatypes;
        (c, _) <- dt.constrs
      )
        yield c
    }

    (dfs.toList, constrs.toSet, st)
  }

  def log(file: String) = {
    new PrintStream(new FileOutputStream(file))
  }
}
