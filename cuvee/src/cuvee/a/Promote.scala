package cuvee.a

import cuvee.pure._

case class Query(funs: List[Fun], constraints: List[Expr])

object Promote {
  // note: Def must not have non-static base cases
  def results(df: Def) = {
    val Def(f, cases) = df
  }
}
