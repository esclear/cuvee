package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

import cuvee.pure._
import cuvee.smtlib._

object _test extends Run(Test, "test.bpl")

object Test extends Main {
  def run(cmds: List[Cmd], st: State) {
    for(Assert(Not(phi)) <- cmds)
        println("proving: " + phi)
  }

  def main(args: Array[String]): Unit = {
    for (arg <- args) {
      val (cmds, st) = cuvee.boogie.parse(arg)
      run(cmds, st)
    }
  }
}
