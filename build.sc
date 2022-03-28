import mill._
import mill.scalalib._


object arse extends ScalaModule {
  def scalaVersion = "2.13.7"
  def ivyDeps = Agg(
    ivy"com.lihaoyi::sourcecode:0.2.7")
}

object cuvee extends ScalaModule {
  def forkArgs = Seq("-Xms4m")
  def scalaVersion = "2.13.7"
  def forkArgs = Seq("-Xss32m")

  def moduleDeps = Seq(arse)

  def mainClass = Some("cuvee.Cuvee")
}
