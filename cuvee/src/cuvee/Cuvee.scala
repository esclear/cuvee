package cuvee

import cuvee.backend.Tactic
import cuvee.pure._
import cuvee.smtlib._
import cuvee.backend.Prove
import cuvee.imp.Eval
import cuvee.imp.WP

class Cuvee {
  var state: Option[State] = None
  var cmds: List[Cmd] = Nil

  def configure(args: List[String]) {
    args match {
      case Nil =>

      case "-debug:solver" :: rest =>
        cuvee.smtlib.solver.debug = true
        configure(rest)

      case path :: rest if state.isDefined =>
        cuvee.error(
          "A file was already loaded. At the moment only a single input file is supported."
        )

      case path :: rest if path.endsWith(".bpl") =>
        val (cmds_, state_) = cuvee.boogie.parse(path)
        state = Some(state_)
        cmds = cmds_
        configure(rest)

      case path :: rest if path.endsWith(".smt2") =>
        val (cmds_, state_) = cuvee.smtlib.parse(path)
        state = Some(state_)
        cmds = cmds_
        configure(rest)

      case path :: rest =>
        error(
          f"Could not parse file at path ${path}: Format could not be determined as the path does't end in .bpl or .smt2."
        )
    }
  }

  def run() {
    assert(state.isDefined, "No file was parsed")

    val st = state.get

    val slv = z3(st)
    val prover = new Prove(slv)

    for (cmd ← cmds) {
      cmd match {
        case DeclareProc(name, in, out) =>

        case DefineProc(name, in, out, body) =>
          val xs = in ++ out
          val st = Expr.id(xs)
          val post = True
          val phi = Forall(xs, Eval.wp(WP, body, st, post))
          
          val status = slv.check(!phi)
          println("procedure " + name + ": " + status)

        case decl: Decl => slv.declare(decl)

        case Assert(phi) => slv.assert(phi)

        case Lemma(expr, tactic) => {
          println()
          println("================  LEMMA  ================")
          println("show:  " + expr)

          val normalized = Disj.from(expr)

          rec(normalized, tactic, 1)(state.get, slv, prover) match {
            case Atom(True) =>
              println("\u001b[92m✔\u001b[0m Lemma proved successfully!")
            case Atom(False) =>
              println(
                "\u001b[91m✘\u001b[0m The lemma is false and cannot be proven!"
              )
            case remaining =>
              println(
                "\u001b[91m⚠\u001b[0m Some subgoals could not be proven! Remaining combined goal: " + remaining.toExpr
              )
          }

          // In any case, assert the lemma, so that its statement is available in later proofs
          slv.assert(expr)
        }
        case _ =>
      }
    }
  }

  def rec(prop: Prop, tactic: Option[Tactic], depth: Int = 0)(implicit
      state: State,
      slv: solver,
      prover: Prove
  ): Prop = {
    def indent(depth: Int, indentStr: String = "  "): String = {
      if (depth <= 0) return "";
      indentStr + indent(depth - 1, indentStr)
    }

    println(indent(depth) + "---  PROOF OBLIGATION ---")
    println(indent(depth) + "prop:     " + prop.toExpr)

    val simp = Simplifier.simplify(prop)
    println(indent(depth) + "simp:     " + simp)

    (simp, tactic) match {
      case (Atom(True), _) =>
        println(
          indent(
            depth + 1
          ) + "\u001b[92m✔\u001b[0m Goal confimed true by simplifier"
        )
        simp // Atom(True)
      case (Atom(False), _) =>
        println(
          indent(
            depth + 1
          ) + "\u001b[91m✘\u001b[0m Goal was reduced to `false` by simplifier"
        )
        simp // Atom(False)

      case (_, Some(tactic_)) =>
        println(indent(depth) + "tactic:   " + tactic)
        // Apply the tactic and get the remaining subgoals that we need to prove
        val goals = tactic_.apply(state, prop)

        // TODO: What do we return, if not all of the subgoals can be proven?
        //       Do we return /\ {unprovable subgoals} ?
        (goals map ({ case (prop_, tactic_) =>
          rec(prop_, tactic_, depth + 1)
        }) filter (_ != Atom(True))) match {
          case Nil             => Atom(True)
          case remaining_goals => Conj.from(And(remaining_goals map (_.toExpr)))
        }

      case (_, _) =>
        println(
          indent(
            depth
          ) + "tactic:   none given, trying to solve goal automatically"
        )

        var components: List[String] = Nil

        // Try a simplification first, without calling the prover
        components :+= "simplifier"
        val simp = (Simplifier.simplify(prop) match {
          // Should this yield a boolean atom, no need to call the prover.
          case res @ (Atom(True) | Atom(False)) =>
            res
          // Otherwise, call the prover …
          case simp_prop =>
            val res = prover.prove(prop)
            components :+= "prover"

            println(indent(depth + 1) + "new goal: " + res.toExpr)
            // … and simplify the result
            Simplifier.simplify(res)
        })

        println(indent(depth + 1) + "simp:     " + simp.toExpr)

        simp match {
          case Atom(True) =>
            println(
              indent(
                depth + 1
              ) + f"\u001b[92m✔\u001b[0m Goal transformed to `true` by ${components.mkString(", ")}"
            )

          case Atom(False) =>
            println(
              indent(
                depth + 1
              ) + f"\u001b[91m✘\u001b[0m Goal transformed to `false` by ${components.mkString(", ")}"
            )

          case goal =>
            println(
              indent(
                depth + 2
              ) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically"
            )
        }

        // Return whatever remained
        simp
    }
  }
}

object Cuvee {
  def main(args: Array[String]) {
    val c = new Cuvee
    c.configure(args.toList)
    c.run()
  }
}
