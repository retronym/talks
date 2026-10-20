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

package sbt.internal.inc.bench

import java.nio.file.{ Files, Path }

/**
 * A generated multi-module build with one inheritance tree spread across its modules.
 *
 * The root `R` (an abstract class or a trait) is in module `m0`; each class at depth `d` has
 * `fanOut` subclasses at depth `d + 1`, placed in module `d * modules / (depth + 1)`, so the tree
 * crosses every module boundary on the way down. Every class has a client object in the same
 * module that selects the inherited `used`, and every leaf has one in the last module. Classes
 * carry `padding` methods of their own, with bodies that exercise inference and collections, so
 * that recompiling one costs something.
 */
final case class SyntheticCorpus(
    modules: Int,
    depth: Int,
    fanOut: Int,
    padding: Int,
    rootIsTrait: Boolean,
    scalaVersion: String,
):
  require(modules >= 1 && depth >= 1 && fanOut >= 1)

  case class Cls(name: String, level: Int, parent: Option[String]):
    def module: Int = math.min(level * modules / (depth + 1), modules - 1)

  val classes: Vector[Cls] =
    val root = Cls("R", 0, None)
    Iterator
      .iterate(Vector(root)) { level =>
        for
          parent <- level
          i <- 0 until fanOut
        yield Cls(s"${parent.name}_$i", parent.level + 1, Some(parent.name))
      }
      .take(depth + 1)
      .flatten
      .toVector

  private val leaves = classes.filter(_.level == depth)
  private def moduleName(i: Int) = s"m$i"
  private val pkg = "bench"

  /** The edits, as a file of the build and the content it gets, by name. */
  val edits: Vector[Edit] =
    val rootFile = s"${moduleName(0)}/R.scala"
    val mid = classes.find(_.level == math.max(1, depth / 2)).get
    val midFile = s"${moduleName(mid.module)}/${mid.name}.scala"
    Vector(
      Edit("root-body", rootFile, rootSource(other = "1")),
      Edit("root-add-member", rootFile, rootSource(extra = "  def bench1: Int = 1\n")),
      Edit(
        "root-add-used-overload",
        rootFile,
        rootSource(extra = "  def used(x: BenchMarker): Int = 0\n")
      ),
      Edit("mid-add-member", midFile, classSource(mid, extra = "  def bench1: Int = 1\n")),
    )

  def write(dir: Path): Unit =
    val projects = (0 until modules).map { i =>
      val upstream = (0 until i).map(j => s""""${moduleName(j)}"""").mkString(", ")
      val deps = if i == 0 then "" else s""", "dependsOn": [$upstream]"""
      s"""    { "name": "${moduleName(i)}", "scalaVersion": "$scalaVersion"$deps }"""
    }
    write(
      dir.resolve("build.json"),
      projects.mkString("{\n  \"projects\": [\n", ",\n", "\n  ]\n}\n")
    )
    write(dir.resolve(s"${moduleName(0)}/BenchMarker.scala"), s"package $pkg\nclass BenchMarker\n")
    for c <- classes do
      val src = if c.parent.isEmpty then rootSource() else classSource(c)
      write(dir.resolve(s"${moduleName(c.module)}/${c.name}.scala"), src)
      write(dir.resolve(s"${moduleName(c.module)}/Use_${c.name}.scala"), clientSource(c, "Use"))
    for c <- leaves do
      write(dir.resolve(s"${moduleName(modules - 1)}/Far_${c.name}.scala"), clientSource(c, "Far"))

  private def pad(prefix: String): String = (0 until padding)
    .map(i =>
      s"  def ${prefix}_pad$i(x: Int): Int =\n" +
        s"    List.tabulate(x % 8 + 1)(j => (j, j * $i)).collect { case (a, b) if a < b => a + b }" +
        s".groupBy(_ % 3).map { case (k, v) => k -> v.sum }.values.foldLeft(${i % 7})(_ + _)\n"
    )
    .mkString

  def rootSource(other: String = "0", extra: String = ""): String =
    val kw = if rootIsTrait then "trait" else "abstract class"
    s"""package $pkg
       |$kw R {
       |  def used: Int = 0
       |  def other: Int = $other
       |$extra${pad("R")}}
       |""".stripMargin

  def classSource(c: Cls, extra: String = ""): String =
    val parent = c.parent.get
    val kw = if c.level == depth then "class" else "abstract class"
    s"""package $pkg
       |$kw ${c.name} extends $parent {
       |$extra${pad(c.name)}}
       |""".stripMargin

  private def clientSource(c: Cls, prefix: String): String =
    s"""package $pkg
       |object ${prefix}_${c.name} {
       |  def f(x: ${c.name}): Int = x.used + 1
       |}
       |""".stripMargin

  private def write(p: Path, s: String): Unit =
    Files.createDirectories(p.getParent)
    Files.writeString(p, s)
end SyntheticCorpus

final case class Edit(name: String, file: String, content: String)
