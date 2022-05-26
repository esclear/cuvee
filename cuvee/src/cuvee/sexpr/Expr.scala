package cuvee.sexpr

import arse._

sealed trait Expr {
  def apply(index: Int) =
    this match {
      case App(args @ _*) => args(index)
    }

  def lines: List[String]
}

sealed trait Atom extends Expr with Token {}

object Tok {
  val lp = KW("(")
  val rp = KW(")")
  def kw(n: String) = KW(n) // parser

  val eof = new Token {}
}

object Lit {
  val zero = num("0")

  case class bin(digits: String) extends Atom {
    def lines = List("#%b" + digits)
  }
  case class dec(digits: String) extends Atom {
    def lines = List(digits)
  }
  case class num(digits: String) extends Atom {
    def lines = List(digits)
  }
  case class hex(digits: String) extends Atom {
    def lines = List("0x" + digits)
  }
  case class str(digits: String) extends Atom {
    def lines = List("\"" + digits + "\"")
  }
}

case class Id(name: String) extends Atom {
  def lines = List(mangle(name))
}

case class Kw(name: String) extends Atom {
  def lines = List(":" + name)
}

object App {
  val from = (args: List[Expr]) => App(args: _*)
}

case class App(args: Expr*) extends Expr {
  def lines = if (args.isEmpty) {
    List("()")
  } else {
    val strings =
      args.toList flatMap (_.lines)

    val max = strings.maxBy(_.length)
    val sum = strings.foldLeft(0)(_ + _.length)

    val break =
      strings.length >= 2 && (max.length > 20 || sum >= 80)

    if (break) {
      val first :: rest = strings
      ("(" + first) :: indent(rest)
    } else {
      List(strings.mkString("(", " ", ")"))
    }
  }

  def indent(lines: List[String]): List[String] = lines match {
    case List(last) =>
      List("  " + last + ")")

    case first :: rest =>
      ("  " + first) :: indent(rest)
  }
}
