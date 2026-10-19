package dotty.tools.dotc
package sbt

import ExtractDependencies.internalError
import ast.{Positioned, Trees, tpd}
import core.*
import core.Decorators.*
import Annotations.*
import Contexts.*
import Flags.*
import Phases.*
import Trees.*
import Types.*
import Symbols.*
import Names.*
import StdNames.str
import NameOps.*
import inlines.Inlines
import transform.ValueClasses
import transform.Pickler
import dotty.tools.io.{File, FileExtension}
import util.{Property, SourceFile}
import java.io.PrintWriter

import ExtractAPI.{HashCachesInRun, NonLocalClassSymbolsInCurrentUnits}

import scala.collection.mutable
import scala.util.hashing.MurmurHash3
import dotty.tools.dotc.util.chaining.*

/** This phase sends a representation of the API of classes to sbt via callbacks.
 *
 *  This is used by sbt for incremental recompilation.
 *
 *  See the documentation of `ExtractAPICollector`, `ExtractDependencies`,
 *  `ExtractDependenciesCollector` and
 *  http://www.scala-sbt.org/1.x/docs/Understanding-Recompilation.html for more
 *  information on incremental recompilation.
 *
 *  The following flags affect this phase:
 *   -Yforce-sbt-phases
 *   -Ydump-sbt-inc
 *
 *  @see ExtractDependencies
 */
class ExtractAPI extends Phase {

  override def phaseName: String = ExtractAPI.name

  override def description: String = ExtractAPI.description

  override def isRunnable(using Context): Boolean = {
    super.isRunnable && (ctx.runZincPhases || ctx.settings.XjavaTasty.value)
  }

  // Check no needed. Does not transform trees
  override def isCheckable: Boolean = false

  // when `-Xjava-tasty` is set we actually want to run this phase on Java sources
  override def skipIfJava(using Context): Boolean = false

  // SuperAccessors need to be part of the API (see the scripted test
  // `trait-super` for an example where this matters), this is only the case
  // after `PostTyper` (unlike `ExtractDependencies`, the simplication to trees
  // done by `PostTyper` do not affect this phase because it only cares about
  // definitions, and `PostTyper` does not change definitions).
  override def runsAfter: Set[String] = Set(transform.Pickler.name)

  override def runOn(units: List[CompilationUnit])(using Context): List[CompilationUnit] =
    val doZincCallback = ctx.runZincPhases
    val nonLocalClassSymbols = new mutable.HashSet[Symbol]
    val units0 =
      if doZincCallback then
        val ctx0 = ctx.withProperty(NonLocalClassSymbolsInCurrentUnits, Some(nonLocalClassSymbols))
          .withProperty(HashCachesInRun, Some(APIHashCaches()))
        super.runOn(units)(using ctx0)
      else
        units // still run the phase for the side effects (writing TASTy files to -Yearly-tasty-output)
    if doZincCallback then
      ctx.withIncCallback(recordNonLocalClasses(nonLocalClassSymbols, _))
    if ctx.settings.XjavaTasty.value then
      units0.filterNot(_.typedAsJava) // remove java sources, this is the terminal phase when `-Xjava-tasty` is set
    else
      units0
  end runOn

  private def recordNonLocalClasses(nonLocalClassSymbols: mutable.HashSet[Symbol], cb: interfaces.IncrementalCallback)(using Context): Unit =
    for cls <- nonLocalClassSymbols do
      val sourceFile = cls.source
      if sourceFile.exists && cls.isDefinedInCurrentRun then
        recordNonLocalClass(cls, sourceFile, cb)
    ctx.run.nn.asyncTasty.foreach(_.signalAPISent())

  private def recordNonLocalClass(cls: Symbol, sourceFile: SourceFile, cb: interfaces.IncrementalCallback)(using Context): Unit =
    def registerProductNames(fullClassName: String, binaryClassName: String) =
      val pathToClassFile = s"${binaryClassName.replace('.', java.io.File.separatorChar)}.class"

      val outDir = ctx.settings.outputDir.value
      val classFile = {
        if outDir.ext.isJar then
            // important detail here, even on Windows, Zinc expects the separator within the jar
            // to be the system default, (even if in the actual jar file the entry always uses '/').
            // see https://github.com/sbt/zinc/blob/dcddc1f9cfe542d738582c43f4840e17c053ce81/internal/compiler-bridge/src/main/scala/xsbt/JarUtils.scala#L47
            new java.io.File(s"${outDir.path}!$pathToClassFile")
        else
            new java.io.File(outDir.file, pathToClassFile)
      }

      cb.generatedNonLocalClass(sourceFile, classFile.toPath(), binaryClassName, fullClassName)
    end registerProductNames

    val fullClassName = atPhase(sbtExtractDependenciesPhase) {
      ExtractDependencies.classNameAsString(cls)
    }
    val binaryClassName = cls.binaryClassName
    registerProductNames(fullClassName, binaryClassName)

    // Register the names of top-level module symbols that emit two class files
    val isTopLevelUniqueModule =
      cls.owner.is(PackageClass) && cls.is(ModuleClass) && cls.companionClass == NoSymbol
    if isTopLevelUniqueModule then
      registerProductNames(fullClassName, binaryClassName.stripSuffix(str.MODULE_SUFFIX))
  end recordNonLocalClass

  protected def run(using Context): Unit = {
    val unit = ctx.compilationUnit
    val sourceFile = unit.source
    ctx.withIncCallback: cb =>
      cb.startSource(sourceFile)

    val nonLocalClassSymbols = ctx.property(NonLocalClassSymbolsInCurrentUnits).get
    val apiTraverser = ExtractAPICollector(nonLocalClassSymbols, ctx.property(HashCachesInRun).get)
    var mode = interfaces.ApiMode.TREE
    var optimizedSealed = false
    ctx.withIncCallback: cb =>
      mode = cb.apiMode
      optimizedSealed = cb.useOptimizedSealed
    // Under HASHES the xsbti.api tree is not built at all.
    val classes =
      if mode != interfaces.ApiMode.HASHES || ctx.settings.YdumpSbtInc.value then apiTraverser.apiSource(unit.tpdTree)
      else Nil
    val hashed =
      if mode == interfaces.ApiMode.TREE then Nil
      else apiTraverser.hashSource(unit.tpdTree, optimizedSealed)
    val mainClasses = apiTraverser.mainClasses

    if (ctx.settings.YdumpSbtInc.value) {
      // Append to existing file that should have been created by ExtractDependencies
      val sourceFileJPath = sourceFile.jfile
      assert(sourceFileJPath.isPresent, s"unexpected null jpath for $sourceFile")
      val pw = new PrintWriter(File(sourceFileJPath.get().toPath).changeExtension(FileExtension.Inc).toFile
        .bufferedWriter(append = true), true)
      try {
        classes.foreach(source => pw.println(DefaultShowAPI(source)))
      } finally pw.close()
    }

    ctx.withIncCallback: cb =>
      if !ctx.compilationUnit.suspendedAtInliningPhase then // already registered before this unit was suspended
        cb.apiMode match
          case interfaces.ApiMode.TREE =>
            classes.foreach(cb.api(sourceFile, _))
          case interfaces.ApiMode.HASHES =>
            hashed.foreach((thin, hashes) => cb.api(sourceFile, thin, hashes))
          case interfaces.ApiMode.CHECK =>
            val full = classes.iterator.map(c => (c.name, c.definitionType) -> c).toMap
            hashed.foreach((thin, hashes) => cb.apiCheck(sourceFile, full((thin.name, thin.definitionType)), thin, hashes))
        mainClasses.foreach(cb.mainClass(sourceFile, _))
  }
}

object ExtractAPI:
  val name: String = "sbt-api"
  val description: String = "sends a representation of the API of classes to sbt"

  private val NonLocalClassSymbolsInCurrentUnits: Property.Key[mutable.HashSet[Symbol]] = Property.Key()

  /** Hashes of types and members, which depend on nothing else, shared by the units of a run. */
  private val HashCachesInRun: Property.Key[APIHashCaches] = Property.Key()

/** The hash of a type in a class's API, as `ExtractAPICollector.typeH` computes it. */
private final class TypeH(val h: Int, val noDefs: Int, val refs: List[(String, Int)]):
  def withRefs(more: List[(String, Int)]): TypeH = if more.isEmpty then this else TypeH(h, noDefs, more)

/** A member of a class's API, hashed as `apiDefinition` (or `stub`) would record it. */
private final class MemberH(val sym: Symbol, val name: String, val access: xsbti.api.Access,
    val mods: xsbti.api.Modifiers, val isDef: Boolean, val hash: Int, val refs: List[(String, Int)],
    val isStub: Boolean, val isTraitBreaker: Boolean, val extrasMarker: Option[String] = None):
  def isNonPrivate: Boolean = APIHashing.isNonPrivate(access)

private final class APIHashCaches:
  val types = new mutable.HashMap[Type, TypeH]
  val members = new mutable.HashMap[Symbol, MemberH]
  val stubs = new mutable.HashMap[Symbol, Option[MemberH]]

/** Extracts full (including private members) API representation out of Symbols and Types.
 *
 *  The exact representation used for each type is not important: the only thing
 *  that matters is that a binary-incompatible or source-incompatible change to
 *  the API (for example, changing the signature of a method, or adding a parent
 *  to a class) should result in a change to the API representation so that sbt
 *  can recompile files that depend on this API.
 *
 *  Note that we only records types as they are defined and never "as seen from"
 *  some other prefix because `Types#asSeenFrom` is a complex operation and
 *  doing it for every inherited member would be slow, and because the number
 *  of prefixes can be enormous in some cases:
 *
 *    class Outer {
 *      type T <: S
 *      type S
 *      class A extends Outer { /*...*/ }
 *      class B extends Outer { /*...*/ }
 *      class C extends Outer { /*...*/ }
 *      class D extends Outer { /*...*/ }
 *      class E extends Outer { /*...*/ }
 *    }
 *
 *  `S` might be refined in an arbitrary way inside `A` for example, this
 *  affects the type of `T` as seen from `Outer#A`, so we could record that, but
 *  the class `A` also contains itself as a member, so `Outer#A#A#A#...` is a
 *  valid prefix for `T`. Even if we avoid loops, we still have a combinatorial
 *  explosion of possible prefixes, like `Outer#A#B#C#D#E`.
 *
 *  It is much simpler to record `T` once where it is defined, but that means
 *  that the API representation of `T` may not change even though `T` as seen
 *  from some prefix has changed. This is why in `ExtractDependencies` we need
 *  to traverse used types to not miss dependencies, see the documentation of
 *  `ExtractDependencies#usedTypeTraverser`.
 *
 *  TODO: sbt does not store the full representation that we compute, instead it
 *  hashes parts of it to reduce memory usage, then to see if something changed,
 *  it compares the hashes instead of comparing the representations. We should
 *  investigate whether we can just directly compute hashes in this phase
 *  without going through an intermediate representation, see
 *  http://www.scala-sbt.org/0.13/docs/Understanding-Recompilation.html#Hashing+an+API+representation
 */
private class ExtractAPICollector(nonLocalClassSymbols: mutable.HashSet[Symbol],
    hashCaches: APIHashCaches = APIHashCaches())(using Context) extends ThunkHolder {
  import tpd.*
  import xsbti.api

  /** This cache is necessary for correctness, see the comment about inherited
   *  members in `apiClassStructure`
   */
  private val classLikeCache = new mutable.HashMap[ClassSymbol, api.ClassLikeDef]
  /** This cache is optional, it avoids recomputing representations */
  private val typeCache = new mutable.HashMap[Type, api.Type]
  /** This cache is necessary to avoid unstable name hashing when `typeCache` is present,
   *  see the comment in the `RefinedType` case in `computeType`
   *  The cache key is (api of RefinedType#parent, api of RefinedType#refinedInfo).
   */
  private val refinedTypeCache = new mutable.HashMap[(api.Type, api.Definition | Null), api.Structure]

  /** This cache is necessary to avoid infinite loops when hashing an inline "Body" annotation.
   *  Its values are transitively seen inline references within a call chain starting from a single "origin" inline
   *  definition. Avoid hashing an inline "Body" annotation if its associated definition is already in the cache.
   *  Precondition: the cache is empty whenever we hash a new "origin" inline "Body" annotation.
   */
  private val seenInlineCache = mutable.HashSet.empty[Symbol]

  /** This cache is optional, it avoids recomputing hashes of inline "Body" annotations,
   *  e.g. when a concrete inline method is inherited by a subclass.
   */
  private val inlineBodyCache = mutable.HashMap.empty[Symbol, Int]

  private val allNonLocalClassesInSrc = new mutable.HashSet[xsbti.api.ClassLike]
  private val _mainClasses = new mutable.HashSet[String]

  private object Constants {
    val emptyStringArray = Array[String]()
    val local: api.ThisQualifier = api.ThisQualifier.create()
    val public: api.Public = api.Public.create()
    val privateLocal: api.Private = api.Private.create(local)
    val protectedLocal: api.Protected = api.Protected.create(local)
    val unqualified: api.Unqualified = api.Unqualified.create()
    val thisPath: api.This = api.This.create()
    val emptyType: api.EmptyType = api.EmptyType.create()
    val emptyModifiers   =
      new api.Modifiers(false, false, false, false, false,false, false, false)
  }

  /** Some Dotty types do not have a corresponding type in xsbti.api.* that
   *  represents them. Until this is fixed we can workaround this by using
   *  special annotations that can never appear in the source code to
   *  represent these types.
   *
   *  @param tp      An approximation of the type we're trying to represent
   *  @param marker  A special annotation to differentiate our type
   */
  private def withMarker(tp: api.Type, marker: api.Annotation) =
    api.Annotated.of(tp, Array(marker))
  private def marker(name: String) =
    api.Annotation.of(api.Constant.of(Constants.emptyType, name), Array())
  private val orMarker = marker("Or")
  private val byNameMarker = marker("ByName")
  private val matchMarker = marker("Match")
  private val superMarker = marker("Super")

  /** Marks the primary constructor of a class whose instantiation has no side
   *  effects, see `hasPureInit`.
   */
  private val pureInitMarker = marker("<pure-init>")

  /** Can creating an instance of `cls` be elided when the instance is unused?
   *
   *  Clients compile against this: `TreeInfo.isPureApply` treats `new C` as pure if
   *  the primary constructor of `C` is `StableRealizable`, and `refPurity` treats a
   *  reference to object `O` as pure if `O`'s module class is `isNoInitsRealClass`.
   *  Pure expressions are elided (e.g. an argument to an unused parameter of an inline method) or
   *  warned about in statement position. Both facts hold iff no base class has
   *  initialization code, which can change without any change to the signatures of
   *  `C` or its ancestors (adding a statement or a private val to a template), so we
   *  add a marker to the primary constructor to make the change visible to Zinc.
   *
   *  For a trait, `StableRealizable` only reflects the trait's own body, but an
   *  anonymous class `new T {}` is pure iff all base classes of `T` are `NoInits`,
   *  so we use that for traits.
   */
  private def hasPureInit(cls: Symbol): Boolean =
    if cls.is(Trait) then cls.asClass.baseClasses.forall(_.is(NoInits))
    else cls.primaryConstructor.is(StableRealizable)

  /** Extract the API representation of a source file */
  def apiSource(tree: Tree): Seq[api.ClassLike] = {
    def apiClasses(tree: Tree): Unit = tree match {
      case PackageDef(_, stats) =>
        stats.foreach(apiClasses)
      case tree: TypeDef =>
        apiClass(tree.symbol.asClass)
      case _ =>
    }

    apiClasses(tree)
    forceThunks()

    allNonLocalClassesInSrc.toSeq
  }

  def apiClass(sym: ClassSymbol): api.ClassLikeDef =
    classLikeCache.getOrElseUpdate(sym, computeClass(sym))

  def mainClasses: Set[String] = {
    forceThunks()
    _mainClasses.toSet
  }

  private def computeClass(sym: ClassSymbol): api.ClassLikeDef = {
    import xsbti.api.{DefinitionType => dt}
    val defType =
      if (sym.is(Trait)) dt.Trait
      else if (sym.is(ModuleClass)) {
        if (sym.is(PackageClass)) dt.PackageModule
        else dt.Module
      } else dt.ClassDef

    val selfType = apiType(sym.givenSelfType)

    val name = ExtractDependencies.classNameAsString(sym)
      // We strip module class suffix. Zinc relies on a class and its companion having the same name

    val tparams = sym.typeParams.map(apiTypeParameter).toArray

    val structure = apiClassStructure(sym)
    val acc = apiAccess(sym)
    val modifiers = apiModifiers(sym)
    val anns = apiAnnotations(sym, inlineOrigin = NoSymbol).toArray
    val topLevel = sym.isTopLevelClass
    val childrenOfSealedClass = sym.sealedDescendants.sorted(using classFirstSort).map(c =>
      if (c.isClass)
        apiType(c.typeRef)
      else
        apiType(c.termRef)
    ).toArray

    val cl = api.ClassLike.of(
      name, acc, modifiers, anns, defType, api.SafeLazy.strict(selfType), api.SafeLazy.strict(structure), Constants.emptyStringArray,
      childrenOfSealedClass, topLevel, tparams)

    allNonLocalClassesInSrc += cl
    if !sym.isLocal then
      nonLocalClassSymbols += sym

    if ctx.platform.isMainClass(sym) then
      _mainClasses += name

    api.ClassLikeDef.of(name, acc, modifiers, anns, tparams, defType)
  }

  def apiClassStructure(csym: ClassSymbol): api.Structure = {
    val bases = classBases(csym)
    val apiBases = bases.map(apiType)

    val (decls, inherited, stubbed) = classMembers(csym)
    val apiDecls = apiDefinitions(decls)
    // Inherited members need to be computed lazily because a class might contain
    // itself as an inherited member, like in `class A { class B extends A }`,
    // this works because of `classLikeCache`
    val apiInherited = lzy((apiDefinitions(inherited) ++ stubbed.flatMap(stub)).toArray)

    api.Structure.of(api.SafeLazy.strict(apiBases.toArray), api.SafeLazy.strict(apiDecls.toArray), apiInherited)
  }

  /** The linearised ancestors of a class, as seen from it. */
  private def classBases(csym: ClassSymbol): List[Type] =
    val ancestorTypes0 =
      try linearizedAncestorTypes(csym.classInfo)
      catch {
        case ex: TypeError =>
          // See neg/i1750a for an example where a cyclic error can arise.
          // The root cause in this example is an illegal "override" of an inner trait
          report.error(ex, csym.sourcePos)
          defn.ObjectType :: Nil
      }
    if (csym.isDerivedValueClass) {
      val underlying = ValueClasses.valueClassUnbox(csym).info.finalResultType
      // The underlying type of a value class should be part of the name hash
      // of the value class (see the test `value-class-underlying`), this is accomplished
      // by adding the underlying type to the list of parent types.
      underlying :: ancestorTypes0
    } else
      ancestorTypes0

  /** A class's declarations, the inherited members recorded in full, and those recorded as stubs. */
  private def classMembers(csym: ClassSymbol): (List[Symbol], List[Symbol], List[Symbol]) =
    val cinfo = csym.classInfo
    // The constructor of an object carries the `pureInitMarker`, so keep it.
    val decls = cinfo.decls.toList
    val declSet = decls.toSet
    val inherited = new mutable.ListBuffer[Symbol]
    val stubbed = new mutable.ListBuffer[Symbol]
    for bc <- cinfo.baseClasses if bc ne csym do
      val internal = isInternal(bc)
      for s <- bc.classInfo.decls.toList if !(s.is(Private) || declSet.contains(s)) do
        if internal then
          if discoveryReads(s) && !bc.is(Scala2x) then inherited += s
        else if bc.is(Scala2x) || ((isPlatform(bc) || !materialiseLibraryMembers(bc)) && !discoveryReads(s)) then
          stubbed += s
        else inherited += s
    (decls, inherited.toList, stubbed.toList)

  /** Is `owner` defined in this subproject, or in another one that Zinc has analysed? Zinc
   *  composes the name hashes of members inherited from such classes from their own decls, so
   *  they are not materialised here, except those that test and main-class discovery read.
   *  Members of library classes still are, unless Zinc asks for stubs (`materialiseLibraryMembers`).
   */
  private def isInternal(owner: Symbol): Boolean =
    internalCache.getOrElseUpdate(owner, owner.isDefinedInCurrentRun || isSubprojectClass(owner) || isInOutput(owner))

  private val internalCache = new mutable.HashMap[Symbol, Boolean]

  /** Whether Zinc wants the members of this library class in full. Otherwise they are stubs, and
   *  Zinc invalidates the class's descendants by the stamp of its jar when it changes.
   */
  private def materialiseLibraryMembers(owner: Symbol): Boolean =
    materialiseCache.getOrElseUpdate(owner, {
      var result = true
      ctx.withIncCallback(cb => result = cb.materialiseLibraryMembers(owner.binaryClassName))
      result
    })

  private val materialiseCache = new mutable.HashMap[Symbol, Boolean]

  private def isSubprojectClass(owner: Symbol): Boolean =
    var result = false
    ctx.withIncCallback(cb => result = cb.isSubprojectClass(owner.binaryClassName))
    result

  /** The archive a classfile was read from, if it was read from one. */
  private def archiveOf(f: dotty.tools.io.AbstractFile): Option[dotty.tools.io.AbstractFile] =
    f.enclosing.map {
      case jar: dotty.tools.io.JarArchive => jar.underlyingSource
      case archive => archive
    }

  private def isInOutput(owner: Symbol): Boolean =
    val out = ctx.settings.outputDir.value
    val f = owner.associatedFile
    f != null && {
      val fp = archiveOf(f).getOrElse(f).jpath
      val op = out.jpath
      fp != null && op != null && fp.toAbsolutePath.startsWith(op.toAbsolutePath)
    }

  /** Is `owner` part of the platform: `Any`, `AnyRef`/`Object`, or a class of the Scala standard
   *  library? Those change only with the Scala version, which recompiles everything, or (for
   *  `Object`) not at all, so their members are recorded as stubs without types (`==`,
   *  `hashCode`, `Product`'s members in each case class). Other JDK classes are not included: a
   *  JDK upgrade need not recompile, and it can add inherited members.
   */
  private def isPlatform(owner: Symbol): Boolean =
    platformCache.getOrElseUpdate(owner,
      owner == defn.AnyClass || owner == defn.AnyRefAlias || owner == defn.ObjectClass ||
        owner == defn.MatchableClass || {
          val f = owner.associatedFile
          f != null && archiveOf(f).exists { jar =>
            val n = jar.name
            n.startsWith("scala-library") || n.startsWith("scala3-library")
          }
        })

  private val platformCache = new mutable.HashMap[Symbol, Boolean]

  /** Test and main-class discovery read inherited annotations and `main` signatures. */
  private def discoveryReads(s: Symbol): Boolean =
    s.name == StdNames.nme.main || s.annotations.exists { a =>
      val as = a.symbol
      as.exists && as != defn.BodyAnnot && !as.showFullName.startsWith("scala.annotation.internal.")
    }

  /** A library member as a name with its access and modifiers, but no types: descendant
   *  invalidation still sees which names a class inherits, and which are abstract, without
   *  paying for their signatures. Type members and classes count too, except the platform's.
   */
  private def stub(s: Symbol): Option[api.ClassDefinition] =
    stubName(s).map(api.Def.of(_, apiAccess(s), apiModifiers(s), Array(), Array(), Array(), Constants.emptyType))

  private def stubName(s: Symbol): Option[String] =
    if (s.isClass || s.isType) && isPlatform(s.owner) then None
    else if s.isTerm && s.name.isSetterName then None
    else Some(if s.isTerm && s.is(Method) then s.zincMangledName.toString else s.name.toString)

  def linearizedAncestorTypes(info: ClassInfo): List[Type] = {
    val ref = info.appliedRef
    // Note that the ordering of classes in `baseClasses` is important.
    info.baseClasses.tail.map(ref.baseType)
  }

  // The hash generated by sbt for definitions is supposed to be symmetric so
  // we shouldn't have to sort them, but it actually isn't symmetric for
  // definitions which are classes, therefore we need to sort classes to
  // ensure a stable hash.
  // Modules and classes come first and are sorted by name, all other
  // definitions come later and are not sorted.
  private object classFirstSort extends Ordering[Symbol] {
    override def compare(a: Symbol, b: Symbol) = {
      val aIsClass = a.isClass
      val bIsClass = b.isClass
      if (aIsClass == bIsClass) {
        if (aIsClass) {
          if (a.is(Module) == b.is(Module))
            a.fullName.toString.compareTo(b.fullName.toString)
          else if (a.is(Module))
            -1
          else
            1
        } else
          0
      } else if (aIsClass)
      -1
    else
      1
    }
  }

  def apiDefinitions(defs: List[Symbol]): List[api.ClassDefinition] =
    defs.sorted(using classFirstSort).map(apiDefinition(_, inlineOrigin = NoSymbol))

  /** `inlineOrigin` denotes an optional inline method that we are
   *  currently hashing the body of. If it exists, include extra information
   *  that is missing after erasure
   */
  def apiDefinition(sym: Symbol, inlineOrigin: Symbol): api.ClassDefinition = {
    if (sym.isClass) {
      apiClass(sym.asClass)
    } else if (sym.isType) {
      apiTypeMember(sym.asType)
    } else if (sym.isMutableVar) {
      api.Var.of(sym.name.toString, apiAccess(sym), apiModifiers(sym),
        apiAnnotations(sym, inlineOrigin).toArray, apiType(sym.info))
    } else if (sym.isStableMember && !sym.isRealMethod) {
      api.Val.of(sym.name.toString, apiAccess(sym), apiModifiers(sym),
        apiAnnotations(sym, inlineOrigin).toArray, apiType(sym.info))
    } else {
      apiDef(sym.asTerm, inlineOrigin)
    }
  }

  /** `inlineOrigin` denotes an optional inline method that we are
   *  currently hashing the body of. If it exists, include extra information
   *  that is missing after erasure
   */
  def apiDef(sym: TermSymbol, inlineOrigin: Symbol): api.Def = {

    var seenInlineExtras = false
    var inlineExtras = 41

    def mixInlineParam(p: Symbol): Unit =
      if inlineOrigin.exists && p.is(Inline) then
        seenInlineExtras = true
        inlineExtras = hashInlineParam(p, inlineExtras)

    def inlineExtrasAnnot: Option[api.Annotation] =
      val h = inlineExtras
      Option.when(seenInlineExtras) {
        marker(s"${MurmurHash3.finalizeHash(h, "inlineExtras".hashCode)}")
      }

    def tparamList(pt: TypeLambda): List[api.TypeParameter] =
      pt.paramNames.lazyZip(pt.paramInfos).map((pname, pbounds) =>
        apiTypeParameter(pname.toString, 0, pbounds.lo, pbounds.hi)
      )

    def paramList(mt: MethodType, params: List[Symbol]): api.ParameterList =
      val apiParams = params.lazyZip(mt.paramInfos).map((param, ptype) =>
        mixInlineParam(param)
        api.MethodParameter.of(
          param.name.toString, apiType(ptype), param.is(HasDefault), api.ParameterModifier.Plain))
      api.ParameterList.of(apiParams.toArray, mt.isImplicitMethod)

    def paramLists(t: Type, paramss: List[List[Symbol]]): List[api.ParameterList] = t match {
      case pt: TypeLambda =>
        paramLists(pt.resultType, paramss.drop(1))
      case mt @ MethodTpe(pnames, ptypes, restpe) =>
        assert(paramss.nonEmpty && paramss.head.hasSameLengthAs(pnames),
          i"mismatch for $sym, ${sym.info}, ${sym.paramSymss}")
        paramList(mt, paramss.head) :: paramLists(restpe, paramss.tail)
      case _ =>
        Nil
    }

    /** returns list of pairs of 1: the position in all parameter lists, and 2: a type parameter list */
    def tparamLists(t: Type, index: Int): List[(Int, List[api.TypeParameter])] = t match
      case pt: TypeLambda =>
        (index, tparamList(pt)) :: tparamLists(pt.resultType, index + 1)
      case mt: MethodType =>
        tparamLists(mt.resultType, index + 1)
      case _ =>
        Nil

    val (tparams, tparamsExtras) = sym.info match
      case pt: TypeLambda =>
        (tparamList(pt), tparamLists(pt.resultType, index = 1))
      case mt: MethodType =>
        (Nil, tparamLists(mt.resultType, index = 1))
      case _ =>
        (Nil, Nil)

    val vparamss = paramLists(sym.info, sym.paramSymss)
    val retTp = sym.info.finalResultType.widenExpr

    val tparamsExtraAnnot = Option.when(tparamsExtras.nonEmpty) {
      marker(s"${hashTparamsExtras(tparamsExtras)("tparamsExtra".hashCode)}")
    }

    val annotations = inlineExtrasAnnot ++: tparamsExtraAnnot ++: apiAnnotations(sym, inlineOrigin)

    api.Def.of(sym.zincMangledName.toString, apiAccess(sym), apiModifiers(sym),
      annotations.toArray, tparams.toArray, vparamss.toArray, apiType(retTp))
  }

  def apiTypeMember(sym: TypeSymbol): api.TypeMember = {
    val typeParams = Array[api.TypeParameter]()
    val name = sym.name.toString
    val access = apiAccess(sym)
    val modifiers = apiModifiers(sym)
    val as = apiAnnotations(sym, inlineOrigin = NoSymbol)
    val tpe = sym.info

    if (sym.isAliasType)
      api.TypeAlias.of(name, access, modifiers, as.toArray, typeParams, apiType(tpe.bounds.hi))
    else {
      assert(sym.isAbstractOrParamType)
      api.TypeDeclaration.of(name, access, modifiers, as.toArray, typeParams, apiType(tpe.bounds.lo), apiType(tpe.bounds.hi))
    }
  }

  // Hack to represent dotty types which don't have an equivalent in xsbti
  def combineApiTypes(apiTps: api.Type*): api.Type = {
    api.Structure.of(api.SafeLazy.strict(apiTps.toArray),
      api.SafeLazy.strict(Array()), api.SafeLazy.strict(Array()))
  }

  def apiType(tp: Type): api.Type = {
    typeCache.getOrElseUpdate(tp, computeType(tp))
  }

  private def computeType(tp: Type): api.Type = {
    // TODO: Never dealias. We currently have to dealias because
    // sbt main class discovery relies on the signature of the main
    // method being fully dealiased. See https://github.com/sbt/zinc/issues/102
    val tp2 = if (!tp.isLambdaSub) tp.dealiasKeepAnnots else tp
    tp2 match {
      case NoPrefix | NoType =>
        Constants.emptyType
      case tp: NamedType =>
        val sym = tp.symbol
        // A type can sometimes be represented by multiple different NamedTypes
        // (they will be `=:=` to each other, but not `==`), and the compiler
        // may choose to use any of these representation, there is no stability
        // guarantee. We avoid this instability by always normalizing the
        // prefix: if it's a package, if we didn't do this sbt might conclude
        // that some API changed when it didn't, leading to overcompilation
        // (recompiling more things than what is needed for incremental
        // compilation to be correct).
        val prefix = if (sym.maybeOwner.is(Package)) // { type T } here T does not have an owner
          sym.owner.thisType
        else
          tp.prefix
        api.Projection.of(apiType(prefix), sym.name.toString)
      case FlexibleType(hi) =>
        apiType(hi)
      case AppliedType(tycon, args) =>
        def processArg(arg: Type): api.Type = arg match {
          case arg @ TypeBounds(lo, hi) => // Handle wildcard parameters
            if (lo.isDirectRef(defn.NothingClass) && hi.isDirectRef(defn.AnyClass))
              Constants.emptyType
            else {
              val name = "_"
              val ref = api.ParameterRef.of(name)
              api.Existential.of(ref,
                Array(apiTypeParameter(name, 0, lo, hi)))
            }
          case _ =>
            apiType(arg)
        }

        val apiTycon = apiType(tycon)
        val apiArgs = args.map(processArg)
        api.Parameterized.of(apiTycon, apiArgs.toArray)
      case tl: TypeLambda =>
        val apiTparams = tl.typeParams.map(apiTypeParameter)
        val apiRes = apiType(tl.resType)
        api.Polymorphic.of(apiRes, apiTparams.toArray)
      case rt: RefinedType =>
        val name = rt.refinedName.toString
        val parent = apiType(rt.parent)

        def typeRefinement(name: String, tp: TypeBounds): api.TypeMember = tp match {
          case TypeAlias(alias) =>
            api.TypeAlias.of(name,
              Constants.public, Constants.emptyModifiers, Array(), Array(), apiType(alias))
          case TypeBounds(lo, hi) =>
            api.TypeDeclaration.of(name,
              Constants.public, Constants.emptyModifiers, Array(), Array(), apiType(lo), apiType(hi))
        }
        val decl = rt.refinedInfo match {
          case rinfo: TypeBounds =>
            typeRefinement(name, rinfo)
          case _ =>
            report.debuglog(i"sbt-api: skipped structural refinement in $rt")
            null
        }

        // Aggressive caching for RefinedTypes: `typeCache` is enough as long as two
        // RefinedType are `==`, but this is only the case when their `refinedInfo`
        // are `==` and this is not always the case, consider:
        //
        //     val foo: { type Bla = a.b.T }
        //     val bar: { type Bla = a.b.T }
        //
        // The sbt API representations of `foo` and `bar` (let's call them `apiFoo`
        // and `apiBar`) will both be instances of `Structure`. If `typeCache` was
        // the only cache, then in some cases we would have `apiFoo eq apiBar` and
        // in other cases we would just have `apiFoo == apiBar` (this happens
        // because the dotty representation of `a.b.T` is unstable, see the comment
        // in the `NamedType` case above).
        //
        // The fact that we may or may not have `apiFoo eq apiBar` is more than
        // an optimisation issue: it will determine whether the sbt name hash for
        // `Bla` contains one or two entries (because sbt `NameHashing` will not
        // traverse both `apiFoo` and `apiBar` if they are `eq`), therefore the
        // name hash of `Bla` will be unstable, unless we make sure that
        // `apiFoo == apiBar` always imply `apiFoo eq apiBar`. This is what
        // `refinedTypeCache` is for.
        refinedTypeCache.getOrElseUpdate((parent, decl), {
          val adecl: Array[api.ClassDefinition] = if (decl == null) Array() else Array(decl)
          api.Structure.of(api.SafeLazy.strict(Array(parent)), api.SafeLazy.strict(adecl), api.SafeLazy.strict(Array()))
        })
      case tp: RecType =>
        apiType(tp.parent)
      case RecThis(recType) =>
        // `tp` must be present inside `recType`, so calling `apiType` on
        // `recType` would lead to an infinite recursion, we avoid this by
        //  computing the representation of `recType` lazily.
        apiLazy(recType)
      case tp: AndType =>
        combineApiTypes(apiType(tp.tp1), apiType(tp.tp2))
      case tp: OrType =>
        val s = combineApiTypes(apiType(tp.tp1), apiType(tp.tp2))
        withMarker(s, orMarker)
      case ExprType(resultType) =>
        withMarker(apiType(resultType), byNameMarker)
      case MatchType(bound, scrut, cases) =>
        val s = combineApiTypes(apiType(bound) :: apiType(scrut) :: cases.map(apiType)*)
        withMarker(s, matchMarker)
      case ConstantType(constant) =>
        api.Constant.of(apiType(constant.tpe), constant.stringValue)
      case AnnotatedType(tpe, annot) =>
        api.Annotated.of(apiType(tpe), Array(apiAnnotation(annot)))
      case tp: ThisType =>
        apiThis(tp.cls)
      case tp: ParamRef =>
        // TODO: Distinguishing parameters based on their names alone is not enough,
        // the binder is also needed (at least for type lambdas).
        api.ParameterRef.of(tp.paramName.toString)
      case tp: LazyRef =>
        apiType(tp.ref)
      case tp: TypeVar =>
        apiType(tp.underlying)
      case SuperType(thistpe, supertpe) =>
        val s = combineApiTypes(apiType(thistpe), apiType(supertpe))
        withMarker(s, superMarker)
      case _ => {
        internalError(i"Unhandled type $tp of class ${tp.getClass}")
        Constants.emptyType
      }
    }
  }

  def apiLazy(tp: => Type): api.Type = {
    // TODO: The sbt api needs a convenient way to make a lazy type.
    // For now, we repurpose Structure for this.
    val apiTp = lzy(Array(apiType(tp)))
    api.Structure.of(apiTp, api.SafeLazy.strict(Array()), api.SafeLazy.strict(Array()))
  }

  def apiThis(sym: Symbol): api.Singleton = {
    val pathComponents = sym.ownersIterator.takeWhile(!_.isEffectiveRoot)
      .map(s => api.Id.of(s.name.toString))
    api.Singleton.of(api.Path.of(pathComponents.toArray.reverse ++ Array(Constants.thisPath)))
  }

  def apiTypeParameter(tparam: ParamInfo): api.TypeParameter =
    apiTypeParameter(tparam.paramName.toString, tparam.paramVarianceSign,
      tparam.paramInfo.bounds.lo, tparam.paramInfo.bounds.hi)

  def apiTypeParameter(name: String, variance: Int, lo: Type, hi: Type): api.TypeParameter =
    api.TypeParameter.of(name, Array(), Array(), apiVariance(variance),
      apiType(lo), apiType(hi))

  def apiVariance(v: Int): api.Variance = {
    import api.Variance.*
    if (v < 0) Contravariant
    else if (v > 0) Covariant
    else Invariant
  }

  def apiAccess(sym: Symbol): api.Access = {
    // Symbols which are private[foo] do not have the flag Private set,
    // but their `privateWithin` exists, see `Parsers#ParserCommon#normalize`.
    if (!sym.isOneOf(Protected | Private) && !sym.privateWithin.exists)
      Constants.public
    else if (sym.isAllOf(PrivateLocal))
      Constants.privateLocal
    else if (sym.isAllOf(ProtectedLocal))
      Constants.protectedLocal
    else {
      val qualifier =
        if (sym.privateWithin eq NoSymbol)
          Constants.unqualified
        else
          api.IdQualifier.of(sym.privateWithin.fullName.toString)
      if (sym.is(Protected))
        api.Protected.of(qualifier)
      else
        api.Private.of(qualifier)
    }
  }

  def apiModifiers(sym: Symbol): api.Modifiers = {
    val absOver = sym.is(AbsOverride)
    // `Trait | Abstract | Deferred` would be a type-only flag set, missing deferred terms
    val abs = absOver || sym.isOneOf(Trait | Abstract) || sym.is(Deferred)
    val over = absOver || sym.is(Override)
    new api.Modifiers(abs, over, sym.is(Final), sym.is(Sealed),
      sym.isOneOf(GivenOrImplicit), sym.is(Lazy), sym.is(Macro), sym.isSuperAccessor)
  }

  /** `inlineOrigin` denotes an optional inline method that we are
   *  currently hashing the body of.
   */
  /** If the body of an inline def changes, all the reverse dependencies of this method need to be
   *  recompiled. sbt has no way of tracking method bodies, so we include the hash of the body of
   *  the method as part of the signature we send to sbt.
   */
  private def inlineBodyHash(s: Symbol, inlineOrigin: Symbol): Option[Int] =
    val inlineBody = Inlines.bodyToInline(s)
    Option.when(!inlineBody.isEmpty) {
      def hash[U](inlineOrigin: Symbol): Int =
        assert(seenInlineCache.add(s)) // will fail if already seen, guarded by treeHash
        treeHash(inlineBody, inlineOrigin)
      if inlineOrigin.exists then hash(inlineOrigin)
      else inlineBodyCache.getOrElseUpdate(s, hash(inlineOrigin = s).tap(_ => seenInlineCache.clear()))
    }

  /** The annotations `apiAnnotations` records, apart from the inline body's hash. */
  private def recordedAnnotations(s: Symbol): List[Annotation] =
    // Ignore annotations of type Any, this means we couldn't actually load it,
    // because it's no longer on the classpath compared to when the code we're loading was compiled.
    // See the i25722 special test in explicitNullsPos for an example.
    s.annotations.filter { annot =>
      val sym = annot.symbol
      sym.exists && sym != defn.BodyAnnot && sym != defn.ChildAnnot && !sym.typeRef.isAny
    }

  def apiAnnotations(s: Symbol, inlineOrigin: Symbol): List[api.Annotation] = {
    val annots = new mutable.ListBuffer[api.Annotation]
    inlineBodyHash(s, inlineOrigin).foreach(h => annots += marker(h.toString))

    if s.isConstructor && s == s.owner.primaryConstructor && hasPureInit(s.owner) then
      annots += pureInitMarker

    // In the Scala2 ExtractAPI phase we only extract annotations that extend
    // StaticAnnotation, but in Dotty we currently pickle all annotations so we
    // extract everything, except:
    // - annotations missing from the classpath which we simply skip over
    // - inline body annotations which are handled above
    // - the Child annotation since we already extract children via
    //   `api.ClassLike#childrenOfSealedClass` and adding this annotation would
    //   lead to overcompilation when using zinc's
    //   `IncOptions#useOptimizedSealed`.
    recordedAnnotations(s).foreach(annot => annots += apiAnnotation(annot))

    annots.toList
  }

  /** Produce a hash for a tree that is as stable as possible:
   *  it should stay the same across compiler runs, compiler instances,
   *  JVMs, etc.
   *
   * `inlineOrigin` denotes an optional inline method that we are hashing the body of, where `tree` could be
   * its body, or the body of another method referenced in a call chain leading to `inlineOrigin`.
   *
   * If `inlineOrigin` is NoSymbol, then tree is the tree of an annotation.
   */
  def treeHash(tree: Tree, inlineOrigin: Symbol): Int =
    import core.Constants.*

    def nameHash(n: Name, initHash: Int): Int =
      val h =
        if n.isTermName then
          MurmurHash3.mix(initHash, TermNameHash)
        else
          MurmurHash3.mix(initHash, TypeNameHash)

      // The hashCode of the name itself is not stable across compiler instances
      MurmurHash3.mix(h, n.toString.hashCode)
    end nameHash

    def constantHash(c: Constant, initHash: Int): Int =
      var h = MurmurHash3.mix(initHash, c.tag)
      c.tag match
        case NullTag =>
          // No value to hash, the tag is enough.
        case ClazzTag =>
          h = APIHash.tpe(apiType(c.typeValue), h)
        case _ =>
          h = MurmurHash3.mix(h, java.util.Objects.hashCode(c.value))
      h
    end constantHash

    def cannotHash(what: String, elem: Any, pos: Positioned): Unit =
      internalError(i"Don't know how to produce a stable hash for $what", pos.sourcePos)

    def positionedHash(p: ast.Positioned, initHash: Int): Int =
      var h = initHash

      p match
        case p: WithLazyFields => p.forceFields()
        case _ =>

      if inlineOrigin.exists then
        p match
          case ref: RefTree @unchecked =>
            val sym = ref.symbol
            if sym.is(Inline, butNot = Param) && !sym.is(Trait) && !seenInlineCache.contains(sym) then
              // An inline method that calls another inline method will eventually inline the call
              // at a non-inline callsite, in this case if the implementation of the nested call
              // changes, then the callsite will have a different API, we should hash the definition
              // In contrast, if an inline trait A extends an inline trait B, B's body is inlined into
              // A, so a change to B will cause a change to A directly, so we can skip this, and if 
              // an inline method accesses a parameter of an inline trait it doesn't care about the definition
              // of the trait.
              h = APIHash.definition(apiDefinition(sym, inlineOrigin), h)
          case _ =>

      // FIXME: If `p` is a tree we should probably take its type into account
      // when hashing it, but producing a stable hash for a type is not trivial
      // since the same type might have multiple representations, for method
      // signatures this is already handled by `computeType` and the machinery
      // in Zinc that generates hashes from that, if we can reliably produce
      // stable hashes for types ourselves then we could bypass all that and
      // send Zinc hashes directly.
      h = MurmurHash3.mix(h, p.productPrefix.hashCode)
      iteratorHash(p.productIterator, h)
    end positionedHash

    def iteratorHash(it: Iterator[Any], initHash: Int): Int =
      var h = initHash
      while it.hasNext do
        it.next() match
          case p: Positioned =>
            h = positionedHash(p, h)
          case xs: List[?] =>
            h = iteratorHash(xs.iterator, h)
          case c: Constant =>
            h = constantHash(c, h)
          case n: Name =>
            h = nameHash(n, h)
          case elem =>
            cannotHash(what = i"`${elem.tryToShow}` of unknown class ${elem.getClass}", elem, tree)
      h
    end iteratorHash

    val seed = 4 // https://xkcd.com/221
    val h = positionedHash(tree, seed)
    MurmurHash3.finalizeHash(h, 0)
  end treeHash

  /** Hash secondary type parameters in separate marker annotation.
   *  We hash them separately because the position of type parameters is important.
   */
  private def hashTparamsExtras(tparamsExtras: List[(Int, List[api.TypeParameter])])(initHash: Int): Int =

    def mixTparams(tparams: List[api.TypeParameter])(initHash: Int) =
      var h = initHash
      var elems = tparams
      while elems.nonEmpty do
        h = APIHash.typeParameter(elems.head, h)
        elems = elems.tail
      h

    def mixIndexAndTparams(index: Int, tparams: List[api.TypeParameter])(initHash: Int) =
      mixTparams(tparams)(MurmurHash3.mix(initHash, index))

    var h = initHash
    var extras = tparamsExtras
    var len = 0
    while extras.nonEmpty do
      h = mixIndexAndTparams(index = extras.head(0), tparams = extras.head(1))(h)
      extras = extras.tail
      len += 1
    MurmurHash3.finalizeHash(h, len)
  end hashTparamsExtras

  /** Mix in the name hash also because otherwise switching which
   *  parameter is inline will not affect the hash.
   */
  private def hashInlineParam(p: Symbol, h: Int) =
    MurmurHash3.mix(p.name.toString.hashCode, MurmurHash3.mix(h, InlineParamHash))

  // --- Hashing without the tree (ApiMode.HASHES) ----------------------------------------------

  /** The classes of a source as Zinc keeps them (`APIHashing.thin`) with their hashes, computed
   *  from symbols and types without building the `xsbti.api` tree that `apiSource` builds. Every
   *  node of that tree gets a hash composed from those of its children, so two versions of a class
   *  hash alike exactly when their trees, hashed by `APIHashing`, do; the values differ. CHECK mode
   *  sends both, and Zinc compares them.
   */
  def hashSource(tree: Tree, optimizedSealed: Boolean): Seq[(api.ClassLike, interfaces.ClassHashes)] =
    val result = mutable.ArrayBuffer.empty[(api.ClassLike, interfaces.ClassHashes)]
    val seen = mutable.HashSet.empty[Symbol]
    def visitClass(sym: ClassSymbol): Unit =
      if seen.add(sym) then result += hashClass(sym, optimizedSealed, visitClass)
    def visit(tree: Tree): Unit = tree match
      case PackageDef(_, stats) => stats.foreach(visit)
      case tree: TypeDef => visitClass(tree.symbol.asClass)
      case _ =>
    visit(tree)
    result.toSeq

  import MurmurHash3.{mix, finalizeHash, stringHash}

  private object HTag:
    final val Empty = 1; final val Projection = 2; final val Parameterized = 3; final val Existential = 4
    final val Polymorphic = 5; final val Structure = 6; final val Annotated = 7; final val Constant = 8
    final val Singleton = 9; final val ParamRef = 10; final val RecThis = 11; final val This = 12
    final val TypeParam = 13; final val Annotation = 14; final val Val = 15; final val Var = 16
    final val Def = 17; final val ClassDef = 18; final val TypeDecl = 19; final val TypeAlias = 20
    final val Params = 21; final val Class = 22; final val Trait = 23; final val Definition = 24

  /** A running hash of a node's tag and parts, finalised by the number of parts. */
  private final class Hasher(tag: Int):
    private var h = tag
    private var n = 0
    def int(i: Int): this.type = { h = mix(h, i); n += 1; this }
    def string(s: String): this.type = int(stringHash(s))
    def bool(b: Boolean): this.type = int(if b then 1 else 0)
    def ints(is: Iterable[Int]): this.type = { int(is.size); is.foreach(int); this }
    /** Order-insensitive, as `APIHashing`'s symmetric hashing of definitions. */
    def set(is: Iterable[Int]): this.type =
      val acc = SetH()
      is.foreach(acc.add)
      int(acc.done)
    def done: Int = finalizeHash(h, n)

  /** An order-insensitive hash of a multiset of hashes. */
  private final class SetH:
    private var a, b, k = 0
    private var c = 1
    def add(i: Int): Unit = { a += i; b ^= i; c *= i | 1; k += 1 }
    def done: Int = finalizeHash(mix(mix(mix(MurmurHash3.setSeed, a), b), c), k)

  /** A type's hash; `noDefs` omits the definitions of structural types, as `HashAPI` does with
   *  `includeDefinitions = false`, and `refs` are the refinement members it contains, which
   *  `NameHashing` hashes as definitions of their own.
   */
  private def leafH(h: Int) = TypeH(h, h, Nil)

  private def typeHCache = hashCaches.types
  private var openRecTypes: List[RecType] = Nil

  private def typeH(tp: Type): TypeH =
    if openRecTypes.isEmpty then typeHCache.getOrElseUpdate(tp, computeTypeH(tp))
    else computeTypeH(tp) // a `RecThis` hashes by its depth

  private def structH(parents: List[TypeH], decl: Option[(String, Int)]): TypeH =
    TypeH(
      Hasher(HTag.Structure).ints(parents.map(_.h)).ints(decl.map(_._2)).done,
      Hasher(HTag.Structure).ints(parents.map(_.noDefs)).done,
      decl.toList ++ parents.flatMap(_.refs))

  private def annotatedH(base: TypeH, annots: List[(Int, List[(String, Int)])]): TypeH =
    leafH(Hasher(HTag.Annotated).int(base.h).ints(annots.map(_._1)).done)
      .withRefs(base.refs ++ annots.flatMap(_._2))

  private def markerH(name: String): (Int, List[(String, Int)]) =
    (Hasher(HTag.Annotation).int(Hasher(HTag.Constant).string(name).int(HTag.Empty).done).ints(Nil).done, Nil)

  private def annotationH(annot: Annotation): (Int, List[(String, Int)]) =
    val base = typeH(annot.tree.tpe)
    val arg = Hasher(HTag.Definition).string("TREE_HASH").string(treeHash(annot.tree, inlineOrigin = NoSymbol).toString).done
    (Hasher(HTag.Annotation).int(base.h).ints(arg :: Nil).done, base.refs)

  private def tparamH(name: String, variance: Int, lo: Type, hi: Type): TypeH =
    val l = typeH(lo)
    val u = typeH(hi)
    leafH(Hasher(HTag.TypeParam).string(name).int(apiVariance(variance).ordinal).int(l.h).int(u.h).done)
      .withRefs(l.refs ++ u.refs)

  /** Mirrors `computeType`. */
  private def computeTypeH(tp: Type): TypeH =
    val tp2 = if (!tp.isLambdaSub) tp.dealiasKeepAnnots else tp
    tp2 match
      case NoPrefix | NoType => leafH(HTag.Empty)
      case tp: NamedType =>
        val sym = tp.symbol
        val prefix = if sym.maybeOwner.is(Package) then sym.owner.thisType else tp.prefix
        val p = typeH(prefix)
        leafH(Hasher(HTag.Projection).string(sym.name.toString).int(p.h).done).withRefs(p.refs)
      case FlexibleType(hi) => typeH(hi)
      case AppliedType(tycon, args) =>
        val parts = typeH(tycon) :: args.map {
          case TypeBounds(lo, hi) if lo.isDirectRef(defn.NothingClass) && hi.isDirectRef(defn.AnyClass) =>
            leafH(HTag.Empty)
          case TypeBounds(lo, hi) =>
            val p = tparamH("_", 0, lo, hi)
            leafH(Hasher(HTag.Existential).int(p.h).int(Hasher(HTag.ParamRef).string("_").done).done).withRefs(p.refs)
          case arg => typeH(arg)
        }
        leafH(Hasher(HTag.Parameterized).ints(parts.map(_.h)).done).withRefs(parts.flatMap(_.refs))
      case tl: TypeLambda =>
        val tps = tl.typeParams.map(p => tparamH(p.paramName.toString, p.paramVarianceSign, p.paramInfo.bounds.lo, p.paramInfo.bounds.hi))
        val res = typeH(tl.resType)
        leafH(Hasher(HTag.Polymorphic).ints(tps.map(_.h)).int(res.h).done).withRefs(tps.flatMap(_.refs) ++ res.refs)
      case rt: RefinedType =>
        val name = rt.refinedName.toString
        val decl = rt.refinedInfo match
          case TypeAlias(alias) =>
            val a = typeH(alias)
            Some((name, memberDefH(name, Nil, Constants.emptyModifiers, Constants.public,
              Hasher(HTag.TypeAlias).int(0).int(a.h).done)), a.refs)
          case TypeBounds(lo, hi) =>
            val l = typeH(lo)
            val u = typeH(hi)
            Some((name, memberDefH(name, Nil, Constants.emptyModifiers, Constants.public,
              Hasher(HTag.TypeDecl).int(0).int(l.h).int(u.h).done)), l.refs ++ u.refs)
          case _ => None
        val s = structH(typeH(rt.parent) :: Nil, decl.map(_._1))
        s.withRefs(s.refs ++ decl.toList.flatMap(_._2))
      case tp: RecType =>
        openRecTypes = tp :: openRecTypes
        try typeH(tp.parent) finally openRecTypes = openRecTypes.tail
      case RecThis(recType) =>
        val depth = openRecTypes.indexOf(recType)
        if depth >= 0 then leafH(Hasher(HTag.RecThis).int(depth).done)
        else structH(typeH(recType) :: Nil, None)
      case tp: AndType => structH(typeH(tp.tp1) :: typeH(tp.tp2) :: Nil, None)
      case tp: OrType => annotatedH(structH(typeH(tp.tp1) :: typeH(tp.tp2) :: Nil, None), markerH("Or") :: Nil)
      case ExprType(resultType) => annotatedH(typeH(resultType), markerH("ByName") :: Nil)
      case MatchType(bound, scrut, cases) =>
        annotatedH(structH((bound :: scrut :: cases).map(typeH), None), markerH("Match") :: Nil)
      case ConstantType(constant) =>
        val t = typeH(constant.tpe)
        leafH(Hasher(HTag.Constant).string(constant.stringValue).int(t.h).done).withRefs(t.refs)
      case AnnotatedType(tpe, annot) => annotatedH(typeH(tpe), annotationH(annot) :: Nil)
      case tp: ThisType => leafH(thisH(tp.cls))
      case tp: ParamRef => leafH(Hasher(HTag.ParamRef).string(tp.paramName.toString).done)
      case tp: LazyRef => typeH(tp.ref)
      case tp: TypeVar => typeH(tp.underlying)
      case SuperType(thistpe, supertpe) =>
        annotatedH(structH(typeH(thistpe) :: typeH(supertpe) :: Nil, None), markerH("Super") :: Nil)
      case _ =>
        internalError(i"Unhandled type $tp of class ${tp.getClass}")
        leafH(HTag.Empty)

  /** Mirrors `apiThis`. */
  private def thisH(sym: Symbol): Int =
    val ids = sym.ownersIterator.takeWhile(!_.isEffectiveRoot).map(_.name.toString).toList.reverse
    Hasher(HTag.Singleton).ints(ids.map(stringHash)).int(HTag.This).done

  private def accessH(a: api.Access): Int = a match
    case _: api.Public => 1
    case q: api.Qualified =>
      val kind = if q.isInstanceOf[api.Protected] then 2 else 3
      q.qualifier match
        case _: api.Unqualified => Hasher(kind).int(1).done
        case _: api.ThisQualifier => Hasher(kind).int(2).done
        case id: api.IdQualifier => Hasher(kind).string(id.value).done

  /** `HashAPI.hashDefinition` of a definition with these parts. */
  private def memberDefH(name: String, annots: List[Int], mods: api.Modifiers, access: api.Access, payload: Int): Int =
    Hasher(HTag.Definition).string(name).ints(annots).int(mods.raw.toInt).int(accessH(access)).int(payload).done

  private def memberHCache = hashCaches.members

  private def isTraitBreaker(sym: Symbol, access: api.Access, isField: Boolean, isDef: Boolean, mods: api.Modifiers) =
    access.isInstanceOf[api.Private] &&
      (isField || (sym.isClass && sym.is(ModuleClass)) || (isDef && mods.isSuperAccessor))

  private def memberH(sym: Symbol): MemberH = memberHCache.getOrElseUpdate(sym, computeMemberH(sym))

  private def stubHCache = hashCaches.stubs

  private def stubH(sym: Symbol): Option[MemberH] = stubHCache.getOrElseUpdate(sym, stubName(sym).map { name =>
    val acc = apiAccess(sym)
    val mods = apiModifiers(sym)
    val payload = Hasher(HTag.Def).ints(Nil).ints(Nil).int(HTag.Empty).done
    MemberH(sym, name, acc, mods, isDef = true, memberDefH(name, Nil, mods, acc, payload), Nil, isStub = true,
      isTraitBreaker(sym, acc, isField = false, isDef = true, mods))
  })

  private def annotationsH(sym: Symbol): List[(Int, List[(String, Int)])] =
    inlineBodyHash(sym, inlineOrigin = NoSymbol).map(h => markerH(h.toString)).toList ++
      recordedAnnotations(sym).map(annotationH)

  /** Mirrors `apiDefinition` with no inline origin. */
  private def computeMemberH(sym: Symbol): MemberH =
    val acc = apiAccess(sym)
    val mods = apiModifiers(sym)
    def make(name: String, annots: List[(Int, List[(String, Int)])], payload: Int, refs: List[(String, Int)],
        isDef: Boolean = false, isField: Boolean = false, extrasMarker: Option[String] = None) =
      MemberH(sym, name, acc, mods, isDef, memberDefH(name, annots.map(_._1), mods, acc, payload),
        refs ++ annots.flatMap(_._2), isStub = false, isTraitBreaker(sym, acc, isField, isDef, mods), extrasMarker)
    if sym.isClass then
      val tps = sym.typeParams.map(p => tparamH(p.paramName.toString, p.paramVarianceSign, p.paramInfo.bounds.lo, p.paramInfo.bounds.hi))
      make(ExtractDependencies.classNameAsString(sym), annotationsH(sym),
        Hasher(HTag.ClassDef).ints(tps.map(_.h)).done, tps.flatMap(_.refs))
    else if sym.isType then
      val info = sym.info
      if sym.isAliasType then
        val a = typeH(info.bounds.hi)
        make(sym.name.toString, annotationsH(sym), Hasher(HTag.TypeAlias).int(0).int(a.h).done, a.refs)
      else
        val l = typeH(info.bounds.lo)
        val u = typeH(info.bounds.hi)
        make(sym.name.toString, annotationsH(sym), Hasher(HTag.TypeDecl).int(0).int(l.h).int(u.h).done, l.refs ++ u.refs)
    else if sym.isMutableVar || (sym.isStableMember && !sym.isRealMethod) then
      val t = typeH(sym.info)
      val tag = if sym.isMutableVar then HTag.Var else HTag.Val
      make(sym.name.toString, annotationsH(sym), Hasher(tag).int(t.h).done, t.refs, isField = true)
    else defH(sym.asTerm, (n, as, p, rs, em) => make(n, as, p, rs, isDef = true, extrasMarker = em))

  /** Mirrors `apiDef` with no inline origin. */
  private def defH(sym: TermSymbol,
      make: (String, List[(Int, List[(String, Int)])], Int, List[(String, Int)], Option[String]) => MemberH): MemberH =
    def tparamHs(pt: TypeLambda): List[TypeH] =
      pt.paramNames.lazyZip(pt.paramInfos).map((n, b) => tparamH(n.toString, 0, b.lo, b.hi))
    def paramListHs(t: Type, paramss: List[List[Symbol]]): List[(Int, List[(String, Int)])] = t match
      case pt: TypeLambda => paramListHs(pt.resultType, paramss.drop(1))
      case mt @ MethodTpe(pnames, _, restpe) =>
        val ps = paramss.head.lazyZip(mt.paramInfos).map { (p, ptype) =>
          val t = typeH(ptype)
          (Hasher(HTag.Params).string(p.name.toString).int(t.h).int(api.ParameterModifier.Plain.ordinal).bool(p.is(HasDefault)).done, t.refs)
        }
        (Hasher(HTag.Params).bool(mt.isImplicitMethod).ints(ps.map(_._1)).done, ps.flatMap(_._2)) :: paramListHs(restpe, paramss.tail)
      case _ => Nil
    def hasExtras(t: Type): Boolean = t match
      case _: TypeLambda => true
      case mt: MethodType => hasExtras(mt.resultType)
      case _ => false
    val (tps, extras) = sym.info match
      case pt: TypeLambda => (tparamHs(pt), hasExtras(pt.resultType))
      case mt: MethodType => (Nil, hasExtras(mt.resultType))
      case _ => (Nil, false)
    // Rare: methods with more than one type parameter clause. `apiDef` hashes the extra clauses
    // into a leading marker annotation, so build that once as it does.
    val extrasMarker: Option[String] =
      if extras then
        apiDef(sym, inlineOrigin = NoSymbol).annotations.head.base match
          case c: api.Constant => Some(c.value)
          case _ => None
      else None
    val vps = paramListHs(sym.info, sym.paramSymss)
    val ret = typeH(sym.info.finalResultType.widenExpr)
    val payload = Hasher(HTag.Def).ints(tps.map(_.h)).ints(vps.map(_._1)).int(ret.h).done
    make(sym.zincMangledName.toString, extrasMarker.map(markerH).toList ++ annotationsH(sym), payload,
      tps.flatMap(_.refs) ++ vps.flatMap(_._2) ++ ret.refs, extrasMarker)

  /** One class's thin API and hashes; nested classes reach `visitClass`, as `apiDefinition` reports them. */
  private def hashClass(sym: ClassSymbol, optimizedSealed: Boolean,
      visitClass: ClassSymbol => Unit): (api.ClassLike, interfaces.ClassHashes) =
    import xsbti.api.{DefinitionType => dt}
    val defType =
      if sym.is(Trait) then dt.Trait
      else if sym.is(ModuleClass) then (if sym.is(PackageClass) then dt.PackageModule else dt.Module)
      else dt.ClassDef
    val name = ExtractDependencies.classNameAsString(sym)
    if !sym.isLocal then nonLocalClassSymbols += sym
    if sym.isStatic && !sym.is(Trait) && ctx.platform.hasMainMethod(sym) then _mainClasses += name

    val (declSyms, inheritedSyms, stubbedSyms) = classMembers(sym)
    val decls = declSyms.sorted(using classFirstSort).map(memberH)
    val inherited = inheritedSyms.sorted(using classFirstSort).map(memberH) ++ stubbedSyms.flatMap(stubH)
    for m <- decls.iterator ++ inherited.iterator if m.sym.isClass && !m.isStub do visitClass(m.sym.asClass)

    val bases = classBases(sym)
    val baseHs = bases.map(typeH)
    val tparamHs = sym.typeParams.map(p => tparamH(p.paramName.toString, p.paramVarianceSign, p.paramInfo.bounds.lo, p.paramInfo.bounds.hi))
    val self = typeH(sym.givenSelfType)
    val childTypes = sym.sealedDescendants.sorted(using classFirstSort).map(c => if c.isClass then c.typeRef else c.termRef)
    val children = childTypes.map(typeH)
    val isTrait = defType == dt.Trait
    val classAnnots = annotationsH(sym)
    val acc = apiAccess(sym)
    val mods = apiModifiers(sym)

    def classH(includeDefinitions: Boolean, includeSealedChildren: Boolean, traitBreakers: Boolean): Int =
      val struct = Hasher(HTag.Structure).ints(baseHs.map(b => if includeDefinitions then b.h else b.noDefs))
      if includeDefinitions || traitBreakers then
        def defs(ms: List[MemberH]) =
          val nonPrivate = ms.filter(_.isNonPrivate)
          if traitBreakers then nonPrivate ++ ms.filter(_.isTraitBreaker) else nonPrivate
        struct.set(defs(decls).map(_.hash)).set(defs(inherited).map(_.hash))
      val h = Hasher(HTag.Class).ints(tparamHs.map(_.h)).int(self.h)
      if includeSealedChildren then h.set(children.map(c => if includeDefinitions then c.h else c.noDefs))
      h.bool(isTrait).int(struct.done).done

    val apiHash = classH(includeDefinitions = true, includeSealedChildren = true, traitBreakers = false)
    val extraHash = if isTrait then classH(true, true, traitBreakers = true) else apiHash

    // NameHashing: the class itself, its non-private members and the members of the refinements
    // they mention, grouped by simple name.
    def classEntry(includeSealedChildren: Boolean) =
      memberDefH(name, classAnnots.map(_._1), mods, acc, classH(false, includeSealedChildren, false))
    val members = (decls ++ inherited).filter(_.isNonPrivate)
    val refs = (members.flatMap(_.refs) ++ classAnnots.flatMap(_._2) ++ tparamHs.flatMap(_.refs) ++
      self.refs ++ baseHs.flatMap(_.refs)).distinct
    val location = Hasher(HTag.Class).string(name).bool(defType == dt.Module || defType == dt.PackageModule).done
    def localName(n: String) = n.substring(n.lastIndexOf('.') + 1)
    val regular = new java.util.HashMap[String, SetH]
    val implicits = new java.util.HashMap[String, SetH]
    def add(n: String, isImplicit: Boolean, h: Int): Unit =
      (if isImplicit then implicits else regular).computeIfAbsent(localName(n), _ => SetH()).add(h)
    add(name, mods.isImplicit, classEntry(!optimizedSealed))
    members.foreach(m => add(m.name, m.mods.isImplicit, m.hash))
    refs.foreach((n, h) => add(n, isImplicit = false, h))
    val nameHashes = mutable.ArrayBuilder.make[xsbti.api.NameHash]
    def emit(groups: java.util.HashMap[String, SetH], scope: xsbti.UseScope): Unit =
      groups.forEach((n, acc) => nameHashes += xsbti.api.NameHash.of(n, scope, mix(location, acc.done)))
    emit(regular, xsbti.UseScope.Default)
    emit(implicits, xsbti.UseScope.Implicit)
    if optimizedSealed && mods.isSealed then
      val acc = SetH()
      acc.add(classEntry(true))
      nameHashes += xsbti.api.NameHash.of(localName(name), xsbti.UseScope.PatMatTarget, mix(location, acc.done))
    val hasMacro = mods.isMacro || declSyms.exists(_.is(Macro))

    // The thin class: what `APIUtil.minimize` keeps of the tree.
    def isMain(m: MemberH) = m.isDef && !m.isStub && m.name == "main" &&
      APIHashing.isMainMethod(apiDefinition(m.sym, inlineOrigin = NoSymbol))
    def stubOf(m: MemberH): api.ClassDefinition =
      val annots = if m.isStub then Array.empty[api.Annotation] else memberAnnotations(m)
      api.Def.of(m.name, m.access, m.mods, annots, Array(), Array(), Constants.emptyType)
    val isModule = defType == dt.Module
    val declMains = if isModule then decls.filter(isMain) else Nil
    val inheritedMains = if isModule then inherited.filter(isMain) else Nil
    val thinStructure = api.Structure.of(
      api.SafeLazy.strict(bases.map(apiType).toArray),
      api.SafeLazy.strict((declMains.map(m => apiDefinition(m.sym, NoSymbol)) ++ decls.filterNot(declMains.contains).map(stubOf)).toArray),
      api.SafeLazy.strict((inheritedMains.map(m => apiDefinition(m.sym, NoSymbol)) ++
        inherited.filter(m => m.mods.isAbstract && !inheritedMains.contains(m)).map(stubOf)).toArray))
    val savedAnnotations =
      val names = mutable.LinkedHashSet.empty[String]
      for m <- decls ++ inherited if m.isDef && !m.isStub && m.access.isInstanceOf[api.Public]; a <- recordedAnnotations(m.sym) do
        APIHashing.simpleName(apiType(a.tree.tpe)).foreach(names += _)
      names.toArray
    val thin = api.ClassLike.of(name, acc, mods, apiAnnotations(sym, inlineOrigin = NoSymbol).toArray, defType,
      api.SafeLazy.strict(apiType(sym.givenSelfType)), api.SafeLazy.strict(thinStructure), savedAnnotations,
      childTypes.map(apiType).toArray, sym.isTopLevelClass, sym.typeParams.map(apiTypeParameter).toArray)
    (thin, interfaces.ClassHashes(apiHash, extraHash, nameHashes.result(), hasMacro))

  /** The annotations `apiDefinition` records for a member, as a stub keeps them. */
  private def memberAnnotations(m: MemberH): Array[api.Annotation] =
    (m.extrasMarker.map(marker).toList ++ apiAnnotations(m.sym, inlineOrigin = NoSymbol)).toArray

  def apiAnnotation(annot: Annotation): api.Annotation = {
    // Like with inline defs, the whole body of the annotation and not just its
    // type is part of its API so we need to store its hash, but Zinc wants us
    // to extract the annotation type and its arguments, so we use a dummy
    // annotation argument to store the hash of the tree. We still need to
    // extract the annotation type in the way Zinc expects because sbt uses this
    // information to find tests to run (for example junit tests are
    // annotated @org.junit.Test).
    api.Annotation.of(
      apiType(annot.tree.tpe), // Used by sbt to find tests to run
      Array(api.AnnotationArgument.of("TREE_HASH", treeHash(annot.tree, inlineOrigin = NoSymbol).toString)))
  }
}
