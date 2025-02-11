package cuvee

import cuvee.backend._
import cuvee.pure._
import cuvee.smtlib._
import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.util.Main
import cuvee.util.Run
import cuvee.util.Proving
import cuvee.util.Printer
import cuvee.imp.Spec

object fastexp extends Run(Cuvee, "examples/fastexp.smt2")
object list extends Run(Cuvee, "examples/case_studies/list.bpl")
object debug extends Run(Cuvee, "-rewrite", "debug.bpl")

object Cuvee extends Main {
  def main(args: Array[String]) {
    val c = new Cuvee
    c.configure(args.toList)
    c.run(c.cmds, c.state, z3(c.state))
  }
}

class Cuvee {
  var state = State.default
  var cmds: List[Cmd] = Nil
  var prove: String = "default"
  var rewrite: Boolean = false

  implicit var printer: Printer = cuvee.smtlib.printer

  val options = Map(
    "-help" ->
      ("show help text", () => { help() }),
    "-debug:solver" ->
      ("show information on the interaction with the backend", () => {
        cuvee.smtlib.solver.debug = true
      }),
    "-debug:scanner" -> ("show list of parsed tokens (SMT-LIB only)", () => {
      cuvee.sexpr.debug = true
    }),
    "-debug:prover" -> ("show details about proof steps and tactic applications", () => {
      cuvee.util.Proving.debug = true
    }),
    "-print:smtlib" -> ("override printer to output SMT-LIB format", () => {
      this.printer = cuvee.smtlib.printer
    }),
    "-print:boogie" -> ("override printer to output Boogie format", () => {
      this.printer = cuvee.boogie.printer
    }),
    "-rewrite" -> ("apply structurally recursive axioms as rewrite rules", () => {
      this.rewrite = true
    }),
    "-prove" -> ("prove goals using default prover", () => {
      this.prove = "default"
    }),
    "-prove:none" -> ("do not attempt to prove goals", () => {
      this.prove = "none"
    }),
    "-prove:simple" -> ("prove goals using simple structural prover", () => {
      this.prove = "simple"
    }),
    "-prove:bimodal" -> ("prove goals using the bimodal prover", () => {
      this.prove = "bimodal"
    }),
    "-tactics:suggest" -> ("suggest tactics applicable to the current goal", () => {
      cuvee.util.Proving.suggestTactics = true
    }),
    "-tactics:apply" -> ("apply a suggested tactic if no tactic was specified by the user ", () => {
      cuvee.util.Proving.applyTactics = true
    })
  )

  def help() {
    println("cuvee [options] <file>")
    for ((flag, (description, _)) <- options) {
      println("  " + flag)
      println("      " + description)
      println()
    }
  }

  def configure(args: List[String]) {
    args match {
      case Nil =>

      case first :: rest if options contains first =>
        val (_, action) = options(first)
        action()
        configure(rest)

      case path :: rest if cmds.nonEmpty =>
        cuvee.error(
          "A file was already loaded. At the moment only a single input file is supported."
        )

      case path :: rest if path.endsWith(".bpl") =>
        try {
          val (cmds_, state_) = cuvee.boogie.parse(path)
          printer = cuvee.boogie.printer
          state = state_
          cmds = cmds_
        } catch {
          case error: easyparse.Error =>
            println(error)
        }
        configure(rest)

      case path :: rest if path.endsWith(".smt2") =>
        try {
          val (cmds_, state_) = cuvee.smtlib.parse(path)
          printer = cuvee.smtlib.printer
          state = state_
          cmds = cmds_
        } catch {
          case error: easyparse.Error =>
            println(error)
        }
        configure(rest)

      case path :: rest =>
        error(
          f"Could not parse file at path ${path}: Format could not be determined as the path does't end in .bpl or .smt2."
        )
    }
  }

  // TODO: Figure out, whether or how to integrate these commands
  // def old_run(cmds: List[Cmd], state: State, solver: Solver) {
  //   cmds match {
  //     case Assert(Not(phi)) :: rest =>
  //       println("lemma")
  //       for (line <- phi.lines)
  //         println(line)
  //       val phi_ = show(phi, state, solver)
  //       solver.assert(Not(phi))
  //       run(rest, state, solver)

  //     case (cmd @ Lemma(phi, None)) :: rest if false =>
  //       val phi_ = show(phi, state, solver)
  //       run(rest, state, solver)

  //     case (cmd @ Lemma(phi, None)) :: rest =>
  //       val prove = new ProveSimple(solver)
  //       val phi_ = prove.prove(phi)

  //       if (!solver.isTrue(phi_)) {
  //         for (line <- phi_.lines)
  //           println(line)
  //       }

  //       run(rest, state, solver)

  //   }
  // }

  def run(cmds: List[Cmd], state: State, solver: Solver) {
    // assert(cmds.nonEmpty, "No file was parsed")

    solver.exec(SetOption("produce-models", true))

    val rules = Rewrite.from(cmds, state)
    val safe = Rewrite.safe(rules, state) groupBy (_.fun)

    def maybeProve(phi: Expr, tactic: Option[Tactic]): Boolean = prove match {
      case "bimodal" =>
        val prover = new BimodalProver(solver)
        val result = Proving.show(Disj.from(phi), tactic)(
          state,
          solver,
          prover,
          printer,
          safe
        )

        result == Atom.t

      case "default" =>
        val prover = new MonomodalProver(solver)
        val result = Proving.show(Disj.from(phi), tactic)(
          state,
          solver,
          prover,
          printer,
          safe
        )

        result == Atom.t

      case "simple" =>
        if (!solver.isTrue(phi)) {
          val prover = new SimpleProver(solver)
          val phi_ = Simplify.simplify(prover.prove(phi), safe)
          val cmd = Lemma(phi_, None)
          for (line <- cmd.lines)
            println(line)
          false
        } else {
          true
        }

      case "none" =>
        val cmd = Lemma(phi, None)
        for (line <- cmd.lines)
          println(line)

        false

    }

    def exec(cmd: Cmd) = cmd match {
      case DeclareProc(name, in, out) =>

      case DefineProc(name, in, out, spec, body) =>
        val (ys, pre, post) = spec match {
          case None                      => (Nil, True, True)
          case Some(Spec(xs, pre, post)) => (xs, pre, post)
        }

        val su = Expr.subst(in, Old(in))

        val xs = in ++ out ++ ys
        val post_ = post subst su
        val st = Expr.id(xs)

        val eval = new Eval(state)
        val phi = Forall(xs, pre ==> eval.wp_proc(WP, body, st, post_))

        val ok = maybeProve(phi, tactic = None)
        if (ok)
          println("verified: " + name)

      case ctrl: Ctrl =>
      // solver.control(ctrl)

      case decl: Decl =>
        solver.declare(decl)

      case Assert(phi) =>
        // println("axiom " + phi)
        solver.assert(phi)

      case Lemma(phi, tactic) =>
        // println()
        // println("================  LEMMA  ================")
        // println("show:  " + expr)
        maybeProve(phi, tactic)

        // In any case, assert the lemma, so that its statement is available in later proofs
        solver.assert(phi)

      case Labels =>
      // val result = solver.labels()

      case CheckSat =>
        val result = solver.check()
        println(result)
    }

    for (cmd ← cmds) {
      try {
        exec(cmd)
      } catch {
        case bad: smtlib.Error =>
          for (line <- bad.lines)
            println(line)
      }
    }
  }
}
