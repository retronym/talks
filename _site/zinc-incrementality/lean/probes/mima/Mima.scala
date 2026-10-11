//> using scala 2.13.18
//> using dep com.typesafe::mima-core:1.2.1

import java.io.File
import com.typesafe.tools.mima.lib.MiMaLib
import com.typesafe.tools.mima.core.util.log.Logging

/** Runs MiMa on each case directory under `out` (as `probes/jvm/probe.sh` leaves them with
  * `OUT=dir`, or `probes/mima/scala.sh` for Scala cases): `v0` is the old library, `v1` the new.
  * Prints one JSON line per case: its name and MiMa's problems, each as its class name and
  * description.
  *
  * Usage: scala-cli run probes/mima/Mima.scala -- out case...
  */
object Mima {
  object Quiet extends Logging {
    def verbose(str: String): Unit = ()
    def debug(str: String): Unit = ()
    def warn(str: String): Unit = System.err.println(str)
    def error(str: String): Unit = System.err.println(str)
  }

  def q(s: String) = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""

  def main(args: Array[String]): Unit = {
    val out = new File(args(0))
    for (name <- args.iterator.drop(1)) {
      val dir = new File(out, name)
      val lib = new MiMaLib(Nil, Quiet)
      val problems = lib.collectProblems(new File(dir, "v0"), new File(dir, "v1"), Nil)
      val ps = problems.map(p => "{\"problem\":" + q(p.getClass.getSimpleName) + ",\"description\":" + q(p.description("new")) + "}")
      println("{\"name\":" + q(name) + ",\"problems\":[" + ps.mkString(",") + "]}")
    }
  }
}
