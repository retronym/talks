/*
 * Zinc - The incremental compiler for Scala.
 * Copyright Scala Center, Lightbend, and Mark Harrah
 *
 * Licensed under Apache License 2.0
 * SPDX-License-Identifier: Apache-2.0
 *
 * See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.
 */

package sbt.internal.inc
package bench

import java.nio.file.{ Files, Path, Paths }
import java.security.MessageDigest

import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal

import sbt.internal.inc.FileAnalysisStore
import sbt.io.IO
import sbt.util.Level
import xsbt.api.APIUtil
import xsbti.api.{ Companions, SafeLazyProxy }
import xsbti.compile.AnalysisContents

/**
 * Measures incremental compilation of edit scenarios on a multi-module build, driving Zinc
 * through the scripted [[IncHandler]] so that it uses this checkout's Zinc and compiler bridge.
 *
 * For each edit: apply it, compile the last module (and so every module), record per module the
 * rounds, the classes recompiled and the wall time, then revert it and compile again. Finally a
 * `clean-build` step rebuilds everything from scratch in the warm JVM, as a reference.
 *
 * Timed runs turn `apiDebug` off: with it, Zinc diffs and logs every changed API, which costs
 * more than the compile and grows with API size. The definitions the bridge extracts are counted
 * in a separate untimed `extract` pass over a copy of the build, with `apiDebug` on. Results go
 * to stdout and `--out` as JSON lines, so two checkouts compare by diffing their output.
 *
 * `--verify` checks each incremental result against a clean build, as the conformance harness
 * does for generated programs: a mirror of the build gets the same edit and is compiled from
 * scratch, and the two compare by classfile digest, or by whether they fail. A revert compares
 * with the initial clean build. scalac's output depends on whether a Java class is a source in
 * its batch, which it is in a clean build and often isn't in an incremental one, so in a build
 * with Java sources a differing classfile is also compared with clean builds that see the Java
 * classes as classfiles, or as the incremental compile's rounds did (see [[verdict]]). After a
 * revert that still differs, or that needed the rounds to explain it, the build is rebuilt
 * clean, so the next edit starts from the clean build's classfiles. Verification is untimed and
 * runs on the first repetition only. Classfiles that differ are copied, from both sides, to a
 * `-diffs` directory beside the build; `--only REGEX` runs just the edits it matches.
 *
 * {{{
 * sbt "publishBridges; zincScripted3/Test/runMain sbt.internal.inc.bench.IncBench \
 *   --dir /tmp/bench --modules 4 --depth 5 --fan-out 2 --reps 3 --out /tmp/bench.jsonl"
 * }}}
 */
object IncBench:
  final case class Options(
      dir: Path = Paths.get("target/incbench"),
      modules: Int = 4,
      depth: Int = 5,
      fanOut: Int = 2,
      padding: Int = 20,
      rootIsTrait: Boolean = false,
      scalaVersion: String = "2.13.x",
      reps: Int = 3,
      incOptions: Map[String, String] = Map.empty,
      out: Option[Path] = None,
      label: String = "",
      build: Option[Path] = None,
      edits: Option[Path] = None,
      logLevel: Level.Value = Level.Warn,
      verify: Boolean = false,
      only: Option[scala.util.matching.Regex] = None,
  )

  def parse(args: List[String], o: Options = Options()): Options = args match
    case Nil                            => o
    case "--dir" :: v :: rest           => parse(rest, o.copy(dir = Paths.get(v)))
    case "--modules" :: v :: rest       => parse(rest, o.copy(modules = v.toInt))
    case "--depth" :: v :: rest         => parse(rest, o.copy(depth = v.toInt))
    case "--fan-out" :: v :: rest       => parse(rest, o.copy(fanOut = v.toInt))
    case "--padding" :: v :: rest       => parse(rest, o.copy(padding = v.toInt))
    case "--trait" :: rest              => parse(rest, o.copy(rootIsTrait = true))
    case "--scala" :: v :: rest         => parse(rest, o.copy(scalaVersion = v))
    case "--reps" :: v :: rest          => parse(rest, o.copy(reps = v.toInt))
    case "--build" :: v :: rest         => parse(rest, o.copy(build = Some(Paths.get(v))))
    case "--edits" :: v :: rest         => parse(rest, o.copy(edits = Some(Paths.get(v))))
    case "--debug" :: rest              => parse(rest, o.copy(logLevel = Level.Debug))
    case "--verify" :: rest             => parse(rest, o.copy(verify = true))
    case "--only" :: v :: rest          => parse(rest, o.copy(only = Some(v.r)))
    case "--scalac-option" :: v :: rest =>
      val all = (o.incOptions.get("scalac.options").toList :+ v).mkString(" ")
      parse(rest, o.copy(incOptions = o.incOptions + ("scalac.options" -> all)))
    case "--out" :: v :: rest         => parse(rest, o.copy(out = Some(Paths.get(v))))
    case "--label" :: v :: rest       => parse(rest, o.copy(label = v))
    case "--inc-option" :: kv :: rest =>
      val Array(k, v) = kv.split("=", 2)
      parse(rest, o.copy(incOptions = o.incOptions + (k -> v)))
    case other :: _ => sys.error(s"Unknown argument $other")

  def main(args: Array[String]): Unit =
    val o = parse(args.toList)
    o.build match
      case Some(build) => existing(o, build.toAbsolutePath, o.edits.get.toAbsolutePath)
      case None        => synthetic(o)

  /**
   * Runs the edits on an existing build: a `build.json` as scripted reads it, whose projects
   * point (`in`) at real source trees with their dependency jars in `lib/`. Edits come from a
   * tab-separated file of name, file (relative to the build), text to find and its replacement,
   * with `\\n` for a newline. Lines with the same name make one edit, applied in
   * order. Each project's `target` is deleted first, so both checkouts start
   * from a clean build. There is no extraction pass.
   */
  def existing(o: Options, build: Path, editsFile: Path): Unit =
    val json = Files.readString(build.resolve("build.json"))
    val projects = "\\{[^{}]*\\}".r.findAllIn(json).toVector.map { obj =>
      def field(k: String) = s""""$k"\\s*:\\s*"([^"]+)"""".r.findFirstMatchIn(obj).map(_.group(1))
      val name = field("name").get
      name -> field("in").map(Paths.get(_)).getOrElse(build.resolve(name))
    }
    val props = (Map("apiDebug" -> "false") ++ o.incOptions)
      .map((k, v) => s"$k = $v")
      .mkString("", "\n", "\n")
    for (_, base) <- projects do
      IO.delete(base.resolve("target").toFile)
      Files.writeString(base.resolve("incOptions.properties"), props)
    def unescape(t: String) = t.replace("\\n", "\n")
    val lines = Files.readAllLines(editsFile).toArray(Array.empty[String]).toVector
      .filter(l => l.trim.nonEmpty && !l.startsWith("#"))
      .map(_.split("\t", 4))
    val edits = lines.map(_(0)).distinct.map { name =>
      val parts = lines.filter(_(0) == name)
      val file = parts.head(1)
      require(parts.forall(_(1) == file), s"$name: edits more than one file")
      val content = parts.foldLeft(Files.readString(build.resolve(file))) {
        case (text, Array(_, _, find, replace)) =>
          require(text.contains(unescape(find)), s"$name: text not found in $file")
          text.replace(unescape(find), unescape(replace))
      }
      Edit(name, file, content)
    }.filter(e => o.only.forall(_.findFirstIn(e.name).isDefined))
    val shape = s""""label":"${o.label}","build":"${build.getFileName}""""
    def copy(suffix: String, keep: Path => Boolean): Path =
      val m = build.resolveSibling(build.getFileName.toString + suffix)
      copyBuild(build, m, keep)
      m
    val mirror = Option.when(o.verify)(copy("-verify", _ => true))
    val binaryJava = Option.when(o.verify)(copy("-verify-bin", !_.toString.endsWith(".java")))
    run(o, build, projects.map(_._1), edits, shape, mirror = mirror, binaryJava = binaryJava)
  end existing

  /** Copies a build without its outputs, pointing its `build.json` at the copy. */
  def copyBuild(from: Path, to: Path, keep: Path => Boolean): Unit =
    IO.delete(to.toFile)
    Files.walk(from).iterator.asScala
      .filter(f => !from.relativize(f).iterator.asScala.exists(_.toString == "target"))
      .filter(keep)
      .foreach { f =>
        val t = to.resolve(from.relativize(f).toString)
        if Files.isDirectory(f) then Files.createDirectories(t)
        else Files.copy(f, t)
      }
    val json = Files.readString(from.resolve("build.json"))
    Files.writeString(to.resolve("build.json"), json.replace(from.toString, to.toString))

  def synthetic(o: Options): Unit =
    val corpus =
      SyntheticCorpus(o.modules, o.depth, o.fanOut, o.padding, o.rootIsTrait, o.scalaVersion)
    val moduleNames = (0 until o.modules).map(i => s"m$i")
    def setUp(dir: Path, incOptions: Map[String, String]): Unit =
      IO.delete(dir.toFile)
      corpus.write(dir)
      val props = incOptions.map((k, v) => s"$k = $v").mkString("", "\n", "\n")
      moduleNames.foreach(m =>
        Files.writeString(dir.resolve(m).resolve("incOptions.properties"), props)
      )
    val shape =
      s""""label":"${o.label}","modules":${o.modules},"depth":${o.depth},"fanOut":${o.fanOut},""" +
        s""""padding":${o.padding},"trait":${o.rootIsTrait},"classes":${corpus.classes.size}"""
    val extractDir = o.dir.toAbsolutePath.resolveSibling(o.dir.getFileName.toString + "-extract")
    setUp(extractDir, o.incOptions + ("apiDebug" -> "true"))
    val extracted =
      val runner = new Runner(extractDir, moduleNames, o.scalaVersion)
      try runner.compileAll().total
      finally runner.finish()
    val dir = o.dir.toAbsolutePath
    setUp(dir, Map("apiDebug" -> "false") ++ o.incOptions)
    val extract =
      s"""{$shape,"step":"extract","declared":${extracted.declared},""" +
        s""""inherited":${extracted.inherited},"nameHashes":${extracted.nameHashes}}"""
    val mirror = Option.when(o.verify) {
      val m = dir.resolveSibling(dir.getFileName.toString + "-verify")
      setUp(m, Map("apiDebug" -> "false") ++ o.incOptions)
      m
    }
    run(o, dir, moduleNames, corpus.edits, shape, Some(extract), mirror)
  end synthetic

  private def run(
      o: Options,
      dir: Path,
      moduleNames: Seq[String],
      edits: Seq[Edit],
      shape: String,
      extract: Option[String] = None,
      mirror: Option[Path] = None,
      binaryJava: Option[Path] = None,
  ): Unit =
    var runner = new Runner(dir, moduleNames, o.scalaVersion, o.logLevel)
    val lines = Vector.newBuilder[String]
    def emit(line: String): Unit =
      println(line)
      lines += line
    extract.foreach(emit)
    emit(s"""{$shape,"step":"clean",${runner.compileAll().json}}""")
    val base: Outcome = Right(runner.classes())
    val baseCopy = dir.resolveSibling(dir.getFileName.toString + "-base")
    val diffs = dir.resolveSibling(dir.getFileName.toString + "-diffs")
    if mirror.isDefined then
      IO.delete(baseCopy.toFile)
      IO.delete(diffs.toFile)
      moduleNames.foreach(n =>
        IO.copyDirectory(runner.classesDir(n).toFile, baseCopy.resolve(n).toFile)
      )
    val baseJava = runner.javaProducts().map((n, fs) =>
      n -> fs.map((rel, _) => rel -> baseCopy.resolve(n).resolve(rel))
    )
    lazy val mirrorClasses = mirror.map(new Runner(_, moduleNames, o.scalaVersion)).map { r =>
      try moduleNames.map(n => n -> r.classesDir(n)).toMap
      finally r.finish()
    }

    /** Builds `m` from scratch, against `java`'s classfiles by module, and its Java classfiles. */
    def cleanBuild(m: Path, java: JavaProducts = Map.empty): (Outcome, JavaProducts) =
      val r = new Runner(m, moduleNames, o.scalaVersion, o.logLevel)
      try
        moduleNames.foreach { n =>
          IO.delete(r.classesDir(n).getParent.toFile)
          r.writeLibJar(n, java.getOrElse(n, Nil))
        }
        val out = r.tryCompileAll().map(_ => r.classes())
        (out, if out.isRight then r.javaProducts() else Map.empty)
      finally r.finish()
    def withEdit[A](m: Path, edit: Edit, original: String)(body: => A): A =
      val f = m.resolve(edit.file)
      Files.writeString(f, edit.content)
      try body
      finally Files.writeString(f, original)
    lazy val baseBin = binaryJava.map(b => cleanBuild(b, baseJava)._1)
    mirror.foreach(m =>
      emit(s"""{$shape,"step":"verify-base",${verdict(cleanBuild(m)._1, base)}}""")
    )
    for edit <- edits; rep <- 1 to o.reps do
      val file = dir.resolve(edit.file)
      val original = Files.readString(file)
      val verifying = mirror.filter(_ => rep == 1)
      def step(
          name: String,
          expected: => (Outcome, () => Option[Outcome], JavaProducts),
          expectedRoot: String => Path,
          edited: Boolean
      ): Boolean =
        val start = System.currentTimeMillis()
        val r = runner.tryCompileAll()
        val v = verifying.fold("") { _ =>
          val inc = r.map(_ => runner.classes())
          lazy val (clean, bin, java) = expected

          /**
           * Rebuilds, for each round of this compile, the Scala sources with the Java sources
           * of that round, and the other Java classes as classfiles, as that round's batch had
           * them, and returns the classfiles that round wrote.
           */
          def byRound(keys: Seq[String]): Map[String, Digest] =
            binaryJava.toSeq.flatMap { b =>
              val roundDir = dir.resolveSibling(dir.getFileName.toString + "-verify-round")
              runner.rounds(start).filter(r => keys.exists(r.products)).flatMap { round =>
                copyBuild(b, roundDir, _ => true)
                for src <- round.javaSources do
                  val rel = dir.relativize(src).toString
                  Files.copy(dir.resolve(rel), roundDir.resolve(rel))
                val others =
                  java.map((n, fs) => n -> fs.filterNot((rel, _) => round.javaProducts(s"$n/$rel")))
                val built =
                  if edited then withEdit(roundDir, edit, original)(cleanBuild(roundDir, others)._1)
                  else cleanBuild(roundDir, others)._1
                built.toOption.toSeq.flatMap(_.filter((k, _) => round.products(k)))
              }
            }.toMap
          for k <- differing(inc, clean) do
            val Array(n, rel) = k.split("/", 2)
            for (side, root) <- Seq("inc" -> runner.classesDir(n), "clean" -> expectedRoot(n)) do
              val from = root.resolve(rel)
              val to = diffs.resolve(name).resolve(side).resolve(k)
              if Files.exists(from) then
                Files.createDirectories(to.getParent)
                Files.copy(from, to)
          "," + verdict(inc, clean, bin(), runner.writtenSince(start), byRound)
        }
        val json = r.fold(e => s""""ok":false,"errors":${jsonArray(e)}""", _.json)
        emit(s"""{$shape,"step":"$name","rep":$rep,$json$v}""")
        Seq("same", "signature", "java-context").exists(w => v.contains(s""""verify":"$w"""")) &&
        !v.contains(" java-round")
      end step
      Files.writeString(file, edit.content)
      step(
        edit.name,
        verifying.fold((base, () => baseBin, baseJava)) { m =>
          val (clean, java) = withEdit(m, edit, original)(cleanBuild(m))
          def bin = binaryJava.filter(_ => clean.isRight && !edit.file.endsWith(".java")).map { b =>
            withEdit(b, edit, original)(cleanBuild(b, java)._1)
          }
          (clean, () => bin, java)
        },
        n => mirrorClasses.get(n),
        edited = true
      )
      Files.writeString(file, original)
      val reverted =
        step(s"${edit.name}-revert", (base, () => baseBin, baseJava), baseCopy.resolve, false)
      if verifying.isDefined && !reverted then
        val targets = moduleNames.map(runner.classesDir(_).getParent)
        runner.finish()
        targets.foreach(t => IO.delete(t.toFile))
        runner = new Runner(dir, moduleNames, o.scalaVersion, o.logLevel)
        val reset = runner.tryCompileAll().map(_ => runner.classes())
        emit(s"""{$shape,"step":"${edit.name}-reset",${verdict(reset, base)}}""")
    end for
    for rep <- 1 to o.reps do
      runner.cleanAll()
      emit(s"""{$shape,"step":"clean-build","rep":$rep,${runner.compileAll().json}}""")
    o.out.foreach(p => Files.write(p, lines.result().mkString("", "\n", "\n").getBytes("UTF-8")))
    runner.finish()
  end run

  /**
   * What a module stores. `declared` and `inherited` count the definitions in the stored APIs,
   * summed over every class and object: the full extraction when `apiDebug` is on, as in the
   * untimed `extract` pass, and only what minimization keeps otherwise. `minimizedBytes`
   * re-serialises the analysis with the APIs minimized, as Zinc stores them by default.
   */
  final case class Stored(
      classes: Int,
      declared: Int,
      inherited: Int,
      nameHashes: Int,
      analysisBytes: Long,
      minimizedBytes: Long,
  ):
    def +(o: Stored): Stored =
      Stored(
        classes + o.classes,
        declared + o.declared,
        inherited + o.inherited,
        nameHashes + o.nameHashes,
        analysisBytes + o.analysisBytes,
        minimizedBytes + o.minimizedBytes,
      )
    def json: String =
      s""""classes":$classes,"declared":$declared,"inherited":$inherited,""" +
        s""""nameHashes":$nameHashes,"analysisBytes":$analysisBytes,""" +
        s""""minimizedBytes":$minimizedBytes"""
  end Stored

  final case class ModuleResult(name: String, rounds: Int, recompiled: Int, stored: Stored)

  final case class StepResult(wallMillis: Long, modules: Seq[ModuleResult]):
    def total: Stored = modules.map(_.stored).reduce(_ + _)
    def json: String =
      val ms = modules.map(m =>
        s"""{"module":"${m.name}","rounds":${m.rounds},"recompiled":${m.recompiled},""" +
          s"""${m.stored.json}}"""
      )
      s""""wallMillis":$wallMillis,"rounds":${modules.map(_.rounds).sum},""" +
        s""""recompiled":${modules.map(_.recompiled).sum},${total.json},""" +
        s""""modules":[${ms.mkString(",")}]"""

  /**
   * A classfile's digest, and the digest of it with the type variables of its generic signatures
   * renamed canonically. scalac names a cloned type variable `A` or `A$` depending on what else
   * the run compiles, so a static forwarder's signature can differ between an incremental and a
   * clean build of the same source.
   */
  final case class Digest(raw: String, normalized: String)

  object Digest:
    private def sha(bytes: Array[Byte]): String =
      MessageDigest.getInstance("SHA-256").digest(bytes).map("%02x".format(_)).mkString.take(16)

    private val typeVarDecl = "(?<=[<;])([\\w]+?)\\$+:".r
    private val typeVarUse = "(?<=[(;<>:^)\\[*+-]|^)T([\\w]+?)\\$+;".r

    def apply(bytes: Array[Byte]): Digest = Digest(sha(bytes), sha(normalize(bytes)))

    /** The classfile with `$` suffixes dropped from type variables in its constant pool. */
    def normalize(bytes: Array[Byte]): Array[Byte] =
      val in = java.nio.ByteBuffer.wrap(bytes)
      val out = new java.io.ByteArrayOutputStream(bytes.length)
      val data = new java.io.DataOutputStream(out)
      out.write(bytes, 0, 10)
      in.position(8)
      val count = in.getShort() & 0xffff
      var i = 1
      while i < count do
        val tag = in.get()
        val start = in.position() - 1
        tag match
          case 1 =>
            val len = in.getShort() & 0xffff
            val s = new java.io.DataInputStream(
              new java.io.ByteArrayInputStream(bytes, start + 1, len + 2)
            ).readUTF()
            in.position(in.position() + len)
            val n = typeVarUse.replaceAllIn(typeVarDecl.replaceAllIn(s, "$1:"), "T$1;")
            data.writeByte(1)
            data.writeUTF(n)
          case 3 | 4 | 9 | 10 | 11 | 12 | 17 | 18 => in.position(in.position() + 4)
          case 5 | 6                              => in.position(in.position() + 8); i += 1
          case 7 | 8 | 16 | 19 | 20               => in.position(in.position() + 2)
          case 15                                 => in.position(in.position() + 3)
          case t                                  => sys.error(s"constant pool tag $t")
        if tag != 1 then out.write(bytes, start, in.position() - start)
        i += 1
      out.write(bytes, in.position(), bytes.length - in.position())
      out.toByteArray
    end normalize
  end Digest

  final case class Round(javaSources: Seq[Path], javaProducts: Set[String], products: Set[String])

  /** The classfiles compiled from Java sources, by module: their path and file. */
  type JavaProducts = Map[String, Seq[(String, Path)]]

  /** A build's classfile digests, by module and path, or its compile errors. */
  type Outcome = Either[Seq[String], Map[String, Digest]]

  /**
   * Compares an incremental build with a clean one, with the conformance harness's verdicts and
   * two more. `signature` means the classfiles differ only in generic signatures' type variable
   * names. `java-context` means each differing classfile equals, up to those names, either the
   * clean build's or that of `bin`, a clean build that saw the Java classes as classfiles. Its
   * Scala classfiles then match a clean build, as scalac compiles them in a batch without those
   * Java sources. `bin` is only built when needed. A classfile this compile wrote
   * (`fresh`) may come from a batch that held some Java sources and not others, so it is also
   * compared with `byRound`, a clean build per round with that round's Java sources and the
   * others as classfiles; if one still differs, the verdict is `fresh-mismatch`. A stale, missing or extra classfile is
   * `bytecode`. Each differing classfile is listed, marked `fresh` if `fresh` has it.
   */
  def verdict(
      inc: Outcome,
      clean: Outcome,
      bin: => Option[Outcome] = None,
      fresh: Set[String] = Set.empty,
      byRound: Seq[String] => Map[String, Digest] = _ => Map.empty
  ): String =
    lazy val binClasses = bin.flatMap(_.toOption).getOrElse(Map.empty)
    var roundClasses = Map.empty[String, Digest]
    def sig(a: Map[String, Digest], b: Map[String, Digest], k: String) =
      a.get(k).map(_.normalized) == b.get(k).map(_.normalized)
    val v = (inc, clean) match
      case (Right(a), Right(b)) =>
        val ks = differing(inc, clean)
        if ks.isEmpty then "same"
        else if !ks.forall(k => a.contains(k) && b.contains(k)) then "bytecode"
        else if ks.forall(sig(a, b, _)) then "signature"
        else if ks.forall(k => sig(a, b, k) || sig(a, binClasses, k)) then "java-context"
        else
          val rest = ks.filterNot(k => sig(a, b, k) || sig(a, binClasses, k))
          if !rest.forall(fresh) then "bytecode"
          else
            roundClasses = byRound(rest)
            if rest.forall(sig(a, roundClasses, _)) then "java-context" else "fresh-mismatch"
      case (Right(_), Left(_)) => "missed-error"
      case (Left(_), Right(_)) => "spurious-error"
      case (Left(a), Left(b))  => if a == b then "same" else "same-fail"
    val diff = (inc, clean) match
      case (Right(a), Right(b)) =>
        differing(inc, clean).map { k =>
          val how =
            if sig(a, b, k) then " signature"
            else if sig(a, binClasses, k) then " java-context"
            else if sig(a, roundClasses, k) then " java-round"
            else ""
          s"$k ${a.contains(k)}/${b.contains(k)}$how${if fresh(k) then " fresh" else ""}"
        }
      case _ => Nil
    val errors = Seq("incErrors" -> inc, "cleanErrors" -> clean).collect {
      case (k, Left(e)) => s""","$k":${jsonArray(e)}"""
    }
    s""""verify":"$v","diff":${jsonArray(diff)}${errors.mkString}"""
  end verdict

  /** The classfiles whose digests differ, when both builds succeeded. */
  def differing(inc: Outcome, clean: Outcome): Seq[String] = (inc, clean) match
    case (Right(a), Right(b)) =>
      (a.keySet ++ b.keySet).toSeq.sorted.filter(k => a.get(k) != b.get(k))
    case _ => Nil

  private def jsonArray(xs: Seq[String]): String =
    xs.map(s => "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n") + "\"")
      .mkString("[", ",", "]")

  /** Shared by every runner: IncHandler caches the compiled bridge's path in it per JVM. */
  private lazy val cacheDir = Files.createTempDirectory("incbench-cache")

  final class Runner(
      dir: Path,
      moduleNames: Seq[String],
      scalaVersion: String,
      logLevel: Level.Value = Level.Warn
  ):
    private val handler =
      new IncHandler(dir, cacheDir, UnitSpec.newLogger(logLevel), compileToJar = false)
    private var state: handler.State = handler.initialState

    /** Deletes every module's outputs and analysis, for a full rebuild in a warm JVM. */
    def cleanAll(): Unit =
      moduleNames.foreach(m => state = handler.apply(s"$m/clean", Nil, state))

    /** Compiles like [[compileAll]], or returns the compile errors. */
    def tryCompileAll(): Either[Seq[String], StepResult] =
      try Right(compileAll())
      catch
        case NonFatal(e) =>
          def problems(t: Throwable): Seq[String] = t match
            case null                   => Seq(String.valueOf(e))
            case f: xsbti.CompileFailed =>
              f.problems.toSeq.map { p =>
                val src = p.position.sourceFile
                s"${if src.isPresent then src.get.getName else ""}: ${p.message}"
              }
            case other => problems(other.getCause)
          Left(problems(e).sorted)

    def classesDir(module: String): Path = handler.lookupProject(module).classesDir

    def javaProducts(): JavaProducts =
      moduleNames.map { m =>
        val a = handler.lookupProject(m).prev().analysis.get.asInstanceOf[Analysis]
        val root = classesDir(m)
        m ->
          a.relations.allSources.toSeq
            .filter(_.id.endsWith(".java"))
            .flatMap(a.relations.products)
            .map(handler.converter.toPath)
            .map(p => root.relativize(p).toString -> p)
      }.toMap

    /**
     * The rounds of the compiles since `since`: the Java sources whose classes each compiled
     * last, their classfiles, and all the classfiles it wrote, by module and path.
     */
    def rounds(since: Long): Seq[Round] =
      val perModule = moduleNames.flatMap { m =>
        val a = handler.lookupProject(m).prev().analysis.get.asInstanceOf[Analysis]
        val root = classesDir(m)
        def keys(srcs: Iterable[xsbti.VirtualFileRef]) = srcs
          .flatMap(a.relations.products)
          .map(p => s"$m/${root.relativize(handler.converter.toPath(p))}")
          .toSet
        a.compilations.allCompilations.map(_.getStartTime).filter(_ >= since).map { t =>
          val srcs = a.apis.internal
            .collect { case (n, c) if c.compilationTimestamp == t => n }
            .flatMap(a.relations.definesClass)
            .toSet
          val java = srcs.filter(_.id.endsWith(".java"))
          t -> Round(java.toSeq.map(handler.converter.toPath), keys(java), keys(srcs))
        }
      }
      perModule.groupBy(_._1).toSeq.sortBy(_._1).map { (_, rs) =>
        val all = rs.map(_._2)
        Round(
          all.flatMap(_.javaSources),
          all.flatMap(_.javaProducts).toSet,
          all.flatMap(_.products).toSet
        )
      }
    end rounds

    /** Puts `files` on a module's classpath as `lib/incbench-java.jar`, or removes that jar. */
    def writeLibJar(module: String, files: Seq[(String, Path)]): Unit =
      val jar = handler.lookupProject(module).baseDirectory.resolve("lib/incbench-java.jar")
      Files.deleteIfExists(jar)
      if files.nonEmpty then
        val out = new java.util.zip.ZipOutputStream(Files.newOutputStream(jar))
        try
          for (rel, f) <- files.sortBy(_._1) do
            out.putNextEntry(new java.util.zip.ZipEntry(rel))
            out.write(Files.readAllBytes(f))
            out.closeEntry()
        finally out.close()

    /** Every module's classfiles, by module and path, as a digest of their bytes. */
    def classes(): Map[String, Digest] =
      moduleNames.flatMap { m =>
        val root = classesDir(m)
        if !Files.exists(root) then Nil
        else
          Files.walk(root).iterator.asScala.filter(_.toString.endsWith(".class")).map { f =>
            s"$m/${root.relativize(f)}" -> Digest(Files.readAllBytes(f))
          }.toSeq
      }.toMap

    /** The classfiles, by module and path, that were written at or after `time`. */
    def writtenSince(time: Long): Set[String] =
      moduleNames.flatMap { m =>
        val root = classesDir(m)
        if !Files.exists(root) then Nil
        else
          Files.walk(root).iterator.asScala
            .filter(f =>
              f.toString.endsWith(".class") && Files.getLastModifiedTime(f).toMillis >= time
            )
            .map(f => s"$m/${root.relativize(f)}")
            .toSeq
      }.toSet

    def compileAll(): StepResult =
      val start = System.currentTimeMillis()
      state = handler.apply(s"${moduleNames.last}/compile", Nil, state)
      val wall = System.currentTimeMillis() - start
      StepResult(wall, moduleNames.map(result(_, start)))

    private def result(module: String, since: Long): ModuleResult =
      val p = handler.lookupProject(module)
      val analysis = p.prev().analysis.get.asInstanceOf[Analysis]
      val rounds = analysis.compilations.allCompilations.filter(_.getStartTime >= since)
      val starts = rounds.map(_.getStartTime).toSet
      val recompiled = analysis.apis.internal.count((_, c) => starts(c.compilationTimestamp))
      ModuleResult(module, rounds.size, recompiled, stored(p, analysis))

    private def stored(p: ProjectStructure, analysis: Analysis): Stored =
      val classes = analysis.apis.internal.values.toSeq
      val sides = classes.flatMap(c => Seq(c.api().classApi(), c.api().objectApi()))
      val minimizedApis = analysis.apis.internal.map { (name, c) =>
        val companions = Companions.of(
          APIUtil.minimize(c.api().classApi()),
          APIUtil.minimize(c.api().objectApi())
        )
        name -> c.withApi(SafeLazyProxy.strict(companions))
      }
      val minimized = analysis.copy(apis = APIs(minimizedApis, analysis.apis.external))
      val tmp = Files.createTempFile("incbench", ".zip")
      try
        val contents = AnalysisContents.create(minimized, p.prev().setup.get)
        FileAnalysisStore.binary(tmp.toFile).set(contents)
        Stored(
          classes.size,
          sides.map(_.structure.declared.length).sum,
          sides.map(_.structure.inherited.length).sum,
          classes.map(_.nameHashes.length).sum,
          Files.size(p.cacheFile),
          Files.size(tmp),
        )
      finally Files.deleteIfExists(tmp)
    end stored

    def finish(): Unit = handler.finish(state)
  end Runner
end IncBench
