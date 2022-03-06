package cuvee.a

import cuvee.error
import cuvee.pure._

class Lemma(st: State) {
  val constrs = {
    for (
      (_, dt) <- st.datatypes;
      (c, _) <- dt.constrs
    )
      yield c
  }.toSet

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

  // reverse normalization rules,
  // which recover expressions in terms of the original definitions
  var recovery: Map[Fun, Rule] = Map()

  // promotion rules, these are not necessarily good rewrite rules
  var promotion: Map[Fun, Rule] = Map()

  // discovered lemmas, all in terms of the original functions
  // note, these may have to be subjected to rewriting
  var lemmas: List[Expr] = Nil

  // look at all functions from todo
  def processAll() {
    val now = todo
    todo = Nil

    for (df0 <- todo) {
      val df1 = rewrite(df0)

      normalize(df1) match {
        case None =>
          // df1 already in normal form
          internalize(df1)
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
    ???
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
  def internalize(df: Def): Boolean = {
    known(df) match {
      case Nil =>
        // no such definition is known yet
        definitions += df.fun -> df
        true

      case List(eq) if original contains df.fun =>
        // for original functions, prefer original version
        definitions += df.fun -> df
        definitions -= eq.fun
        normalization += df.fun -> List(eq.flip)
        true

      case List(eq) =>
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
  // - recognize identity/constant function
  def cleanup(df: Def): (List[Def], List[Rule]) = {
    ???
  }
}
