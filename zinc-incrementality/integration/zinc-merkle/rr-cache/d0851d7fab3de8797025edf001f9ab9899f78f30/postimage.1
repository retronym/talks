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

package sbt
package internal
package inc

import sbt.util.Logger
import xsbti.compile.IncOptions
import xsbti.api.{ AnalyzedClass, DefinitionType }
import xsbt.api.SameAPI

import scala.collection.mutable
import scala.util.Try

/**
 * Implement the name hashing heuristics to invalidate classes.
 *
 * It's defined `private[inc]` to allow other libraries to extend this class to their discretion.
 * Note that the rest of the Zinc public API will default on the use of the private and final
 * `IncrementalNameHashing`.
 *
 * See [[MemberRefInvalidator]] for more information on how the name heuristics work to invalidate
 * member references.
 */
private[inc] class IncrementalNameHashingCommon(
    log: Logger,
    options: IncOptions,
    profiler: RunProfiler,
    packagePrefixImplicits: Boolean = true,
) extends IncrementalCommon(log, options, profiler):
  import IncrementalCommon.transitiveDeps

  private val memberRefInvalidator =
    new MemberRefInvalidator(log, invalidationLog, options.logRecompileOnMacro())

  private val descendantRules = DescendantRules.fromOptions(options)

  /**
   * The APIs a [[DescendantRule]] reads: this subproject's current ones, then those of upstream
   * classes as last recorded. Members inherited from upstream subprojects are no longer
   * materialised, so an upstream ancestor's declarations are only visible here.
   */
  private var currentAPI: String => Option[AnalyzedClass] = _ => None
  private val ancestorChanges = mutable.HashMap.empty[String, AncestorChange]

  override def detectAPIChanges(
      recompiledClasses: collection.Set[String],
      oldAPI: String => AnalyzedClass,
      newAPI: String => AnalyzedClass
  ): APIChanges =
    currentAPI = name =>
      Try(newAPI(name)).toOption
        .filter(_ ne APIs.emptyAnalyzedClass)
        .orElse(previousAPIs.external.get(name))
    ancestorChanges.clear()
    super.detectAPIChanges(recompiledClasses, oldAPI, newAPI)

  override protected def libraryDescendants(relations: Relations): Set[String] =
    if !LibraryAncestors.invalidates(options) then Set.empty
    else LibraryAncestors.descendants(changedLibraryClasses, previousAPIs)

  private def sameSource(relations: Relations)(className: String): Set[String] =
    relations.definesClass(className).flatMap(relations.classNames)

  private def addedNames(className: String): Set[String] =
    ancestorChanges.get(className).fold(Set.empty[String]) { c =>
      c.after.nameHashes.iterator.map(_.name).toSet -- c.before.nameHashes.iterator.map(_.name)
    }

  override protected def invalidateByPackageScope(
      relations: Relations,
      compiled: Set[String]
  ): Set[String] =
    if ancestorChanges.isEmpty then Set.empty
    else
      val api =
        if compiled.isEmpty then
          (name: String) => previousAPIs.internal.get(name).orElse(currentAPI(name))
        else currentAPI
      val packageObjects = relations.classes._2s.filter(PackageScope.isPackageObject)
      val changes = PackageScope.changes(ancestorChanges, api, packageObjects)
      val reach = PackageScope.Reach(
        relations,
        IncrementalCommon.comesFromScalaSource(relations),
        PackageScope.global(options)
      )
      val reached =
        PackageScope.invalidated(changes, relations, reach, packagePrefixImplicits) -- compiled
      val clashes = PackageScope.clashes(changes, relations, compiled) ++
        PackageScope.addedClassClashes(ancestorChanges, api, packageObjects, relations, compiled)
      val invalidated = reached ++ clashes
      if changes.nonEmpty || clashes.nonEmpty then
        invalidationLog.debug(
          InvalidationLog.section(
            "Package members",
            Seq(
              "added names" ->
                changes.map(c => s"${c.packageObject}: ${c.added.toList.sorted.mkString(", ")}"),
              "changed implicits" -> changes.filter(_.implicitsChanged).map(_.packageObject),
              "invalidated classes" -> reached,
              "clashing classes, with their package objects" -> clashes
            )
          )
        )
      invalidated

  /** @inheritdoc */
  protected def invalidatedPackageObjects(
      invalidatedClasses: Set[String],
      relations: Relations,
      apis: APIs
  ): Set[String] =
    val findSubclasses = relations.inheritance.internal.reverse
    val invalidatedClassesAndCodefinedClasses =
      for
        cls <- invalidatedClasses.iterator
        file <- relations.definesClass(cls).iterator
        cls1 <- relations.classNames(file)
      yield cls1

    val invalidatedPackageObjects =
      transitiveDeps(invalidatedClassesAndCodefinedClasses.toSet, invalidationLog.detailLogger)(
        findSubclasses
      )
        .filter(_.endsWith(".package"))
    debug(
      InvalidationLog.section(
        "Package-object invalidations",
        Seq("classes" -> invalidatedPackageObjects),
        Some("no classes")
      )
    )
    invalidatedPackageObjects
  end invalidatedPackageObjects

  /** @inheritdoc */
  override protected def findAPIChange(
      className: String,
      a: AnalyzedClass,
      b: AnalyzedClass
  ): Option[APIChange] =
    val headerChanged = AncestorChange(className, a, b, ModifiedNames(Set.empty)).headerChanged
    if SameAPI(a, b) && !headerChanged then
      if SameAPI.hasSameExtraHash(a, b) then None
      else
        val isATrait = a.api().classApi().definitionType() == DefinitionType.Trait
        val isBTrait = b.api().classApi().definitionType() == DefinitionType.Trait
        if isATrait && isBTrait then
          Some(TraitPrivateMembersModified(className))
        else
          // if the extra hash does not match up, but the API is "same" we can ignore it.
          // see also https://github.com/sbt/sbt/issues/4441
          debug(s"""different extra api hashes for non-traits:
               |  `${a.name}`: ${a.extraHash()}
               |  `${b.name}`: ${b.extraHash()}
             """.stripMargin)
          None
    else
      val aNameHashes = a.nameHashes
      val bNameHashes = b.nameHashes
      val modifiedNames = ModifiedNames.compareTwoNameHashes(aNameHashes, bNameHashes)
      ancestorChanges(className) = AncestorChange(className, a, b, modifiedNames)
      val apiChange = NamesChange(className, modifiedNames)
      Some(apiChange)
    end if
  end findAPIChange

  /** @inheritdoc */
  override protected def invalidateClassesExternally(
      relations: Relations,
      externalAPIChange: APIChange,
      isScalaClass: String => Boolean
  ): Set[String] =
    val modifiedBinaryClassName = externalAPIChange.modifiedClass
    invalidationLog.detail(memberRefInvalidator.invalidationReason(externalAPIChange))
    invalidationLog.detail(
      "All member reference dependencies will be considered within this context."
    )
    val memberRefInv = memberRefInvalidator.get(
      _,
      relations.names,
      externalAPIChange,
      isScalaClass,
      sameSource(relations),
      addedNames(modifiedBinaryClassName)
    )

    // Propagate inheritance dependencies transitively.
    // This differs from normal because we need the initial crossing from externals to classes in this project.
    val byExternalInheritance = relations.inheritance.external.reverse(modifiedBinaryClassName)
    invalidationLog.detail(
      InvalidationLog.section(
        s"Direct inheritance from external class $modifiedBinaryClassName",
        Seq("invalidated classes" -> byExternalInheritance),
        Some("no classes")
      )
    )
    invalidationLog.detail("Now invalidating by inheritance (internally).")
    val descendants = byExternalInheritance.flatMap(invalidateByInheritance(relations, _))
    val ancestorChange = ancestorChanges.get(modifiedBinaryClassName)
    val transitiveInheritance =
      filterExternalDescendants(
        relations,
        modifiedBinaryClassName,
        ancestorChange,
        descendants,
        isScalaClass
      )

    val localInheritance = relations.localInheritance.external.reverse(modifiedBinaryClassName) ++
      descendants.flatMap(invalidateByLocalInheritance(relations, _))

    // Get the member reference dependencies of all classes transitively invalidated by inheritance
    invalidationLog.detail(
      "Getting direct dependencies of all classes transitively invalidated by inheritance."
    )
    val byName = descendants.flatMap(memberRefInv(relations.memberRef.internal))
    val memberRefA =
      if ancestorChange.exists(_.headerChanged) then
        byName ++ descendants.flatMap(relations.memberRef.internal.reverse)
      else byName

    // Get the classes that depend on externals by member reference.
    // This includes non-inheritance dependencies and is not transitive.
    invalidationLog.detail(
      s"Getting classes that directly depend on (external) $modifiedBinaryClassName."
    )
    val memberRefB =
      val byName = memberRefInv(relations.memberRef.external)(modifiedBinaryClassName)
      if ancestorChange.exists(_.headerChanged) then
        byName ++ relations.memberRef.external.reverse(modifiedBinaryClassName)
      else byName

    val macroExpansion = relations.macroExpansion.external.reverse(modifiedBinaryClassName) ++
      descendants.flatMap(invalidateByMacroExpansion(relations, _))

    val invalidated =
      transitiveInheritance ++ localInheritance ++ memberRefA ++ memberRefB ++ macroExpansion
    invalidationLog.debug(
      InvalidationLog.section(
        s"External API change: ${InvalidationLog.formatApiChange(externalAPIChange)}",
        Seq(
          "transitive inheritance" -> transitiveInheritance,
          "local inheritance" -> localInheritance,
          "member reference" -> (memberRefA ++ memberRefB),
          "macro expansion" -> macroExpansion,
        ),
        Some("no classes invalidated")
      )
    )
    invalidated
  end invalidateClassesExternally

  private def invalidateByInheritance(relations: Relations, modified: String): Set[String] =
    val inheritanceDeps = relations.inheritance.internal.reverse
    invalidationLog.detail(s"Invalidating transitively by inheritance from $modified.")
    val transitiveInheritance =
      transitiveDeps(Set(modified), invalidationLog.detailLogger)(inheritanceDeps)
    invalidationLog.detail(
      InvalidationLog.section(
        s"Inheritance invalidation from $modified",
        Seq("invalidated classes" -> transitiveInheritance),
        Some("no classes")
      )
    )
    transitiveInheritance

  private def invalidateByLocalInheritance(relations: Relations, modified: String): Set[String] =
    val localInheritanceDeps = relations.localInheritance.internal.reverse(modified)
    if localInheritanceDeps.nonEmpty then
      invalidationLog.detail(
        InvalidationLog.section(
          s"Local-inheritance invalidation from $modified",
          Seq("invalidated classes" -> localInheritanceDeps)
        )
      )
    localInheritanceDeps

  private def invalidateByMacroExpansion(relations: Relations, modified: String): Set[String] =
    val macroExpansionDeps = relations.macroExpansion.internal.reverse(modified)
    if macroExpansionDeps.nonEmpty then
      invalidationLog.detail(
        InvalidationLog.section(
          s"Macro-expansion invalidation from $modified",
          Seq("invalidated classes" -> macroExpansionDeps)
        )
      )
    macroExpansionDeps

  /** @inheritdoc */
  override protected def invalidateClassesInternally(
      relations: Relations,
      change: APIChange,
      isScalaClass: String => Boolean
  ): Set[String] =
    val modifiedClass = change.modifiedClass
    val memberRefInv = memberRefInvalidator.get(
      _,
      relations.names,
      change,
      isScalaClass,
      sameSource(relations),
      addedNames(modifiedClass)
    )

    val descendants = invalidateByInheritance(relations, modifiedClass)
    val ancestorChange = ancestorChanges.get(modifiedClass)
    val transitiveInheritance =
      filterDescendants(relations, modifiedClass, ancestorChange, descendants, isScalaClass)
    val reason1 = s"The invalidated class names inherit directly or transitively on $modifiedClass."
    profiler.registerEvent(InheritanceKind, List(modifiedClass), transitiveInheritance, reason1)

    val localInheritance = descendants.flatMap(invalidateByLocalInheritance(relations, _))
    val reason2 =
      s"The invalidated class names inherit (via local inheritance) directly or transitively on $modifiedClass."
    profiler.registerEvent(LocalInheritanceKind, descendants, localInheritance, reason2)

    val byName = descendants.flatMap(memberRefInv(relations.memberRef.internal))
    val memberRef =
      if ancestorChange.exists(_.headerChanged) then
        byName ++ descendants.flatMap(relations.memberRef.internal.reverse)
      else byName
    val reason3 = s"The invalidated class names refer directly or transitively to $modifiedClass."
    profiler.registerEvent(MemberReferenceKind, transitiveInheritance, memberRef, reason3)

    val macroExpansion = descendants.flatMap(invalidateByMacroExpansion(relations, _))
    val reason4 = s"The invalidated class is touched by macro expansion in ${modifiedClass}"
    profiler.registerEvent(MacroExpansionKind, descendants, macroExpansion, reason4)

    val all = transitiveInheritance ++ localInheritance ++ memberRef ++ macroExpansion
    invalidationLog.debug(
      InvalidationLog.section(
        s"API change: ${InvalidationLog.formatApiChange(change)}",
        Seq(
          "transitive inheritance" -> transitiveInheritance,
          "local inheritance" -> localInheritance,
          "member reference" -> memberRef,
          "macro expansion" -> macroExpansion,
        ),
        Some("no classes invalidated")
      )
    )
    all
  end invalidateClassesInternally

  /**
   * The descendants of `modifiedClass` that must recompile. Without Merkle hashing every
   * descendant had to, to refresh its materialised members; now only those whose own
   * compilation reads the change do, as decided by the [[DescendantRule]]s.
   */
  private def filterDescendants(
      relations: Relations,
      modifiedClass: String,
      change: Option[AncestorChange],
      descendants: Set[String],
      isScalaClass: String => Boolean,
      api: String => Option[AnalyzedClass] = currentAPI,
      external: Boolean = false
  ): Set[String] =
    (descendantRules, change) match
      case (Some(rules), Some(change)) if external || isScalaClass(modifiedClass) =>
        val view = new HierarchyView(relations, api)
        descendants.filter { d =>
          d == modifiedClass || !isScalaClass(d) || {
            val reasons = rules.flatMap(r => r(view, d, change).map(why => s"${r.name}: $why"))
            if reasons.isEmpty then
              invalidationLog.debug(s"Descendant $d of $modifiedClass does not read the change.")
            else
              invalidationLog.debug(
                s"Descendant $d of $modifiedClass recompiles (${reasons.mkString("; ")})."
              )
            reasons.nonEmpty
          }
        }
      case _ => descendants

  /**
   * [[filterDescendants]] for an upstream class: the descendants are this subproject's classes,
   * read from the previous analysis, and their ancestors may be in upstream subprojects.
   */
  private def filterExternalDescendants(
      relations: Relations,
      modifiedClass: String,
      change: Option[AncestorChange],
      descendants: Set[String],
      isScalaClass: String => Boolean
  ): Set[String] =
    val api = (name: String) =>
      previousAPIs.internal.get(
        name
      ).orElse(currentAPI(name)).orElse(previousAPIs.external.get(name))
    filterDescendants(relations, modifiedClass, change, descendants, isScalaClass, api, true)

  /** @inheritdoc */
  override protected def findClassDependencies(
      className: String,
      relations: Relations
  ): Set[String] = relations.memberRef.internal.reverse(className)
end IncrementalNameHashingCommon

private final class IncrementalNameHashing(
    log: Logger,
    options: IncOptions,
    profiler: RunProfiler,
    packagePrefixImplicits: Boolean = true,
) extends IncrementalNameHashingCommon(log, options, profiler, packagePrefixImplicits)
