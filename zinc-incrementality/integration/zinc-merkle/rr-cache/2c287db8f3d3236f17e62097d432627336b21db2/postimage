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

package xsbt

import java.util.{ Arrays, Comparator }
import scala.tools.nsc.symtab.Flags
import xsbti.api._

import scala.annotation.tailrec
import scala.tools.nsc.Global
import scala.PartialFunction.cond
import ExtractAPI.ConstructorWithDefaultArgument

/**
 * Extracts full (including private members) API representation out of Symbols and Types.
 *
 * API for each class is extracted separately. Inner classes are represented as an empty (without members)
 * member of the outer class and as a separate class with full API representation. For example:
 *
 * class A {
 *   class B {
 *     def foo: Int = 123
 *   }
 * }
 *
 * Is represented as:
 *
 * // className = A
 * class A {
 *   class B
 * }
 * // className = A.B
 * class A.B {
 *   def foo: Int
 * }
 *
 * One instance serves a run: call `startUnit` before each compilation unit. What a unit registers
 * (its classes, main classes and the tree path's caches) is per unit. Hashing caches that depend only
 * on symbols and types are shared by all units of the run; see "Direct hashing" below.
 *
 * NOTE: This class extract *full* API representation. In most of other places in the incremental compiler,
 * only non-private (accessible from other compilation units) members are relevant. Other parts of the
 * incremental compiler filter out private definitions before processing API structures. Check SameAPI for
 * an example.
 *
 */
class ExtractAPI[GlobalType <: Global](
    val global: GlobalType,
    outputDirs: Iterable[java.nio.file.Path] = Nil,
    isSubprojectClass: String => Boolean = _ => false,
    materialiseLibraryMembers: String => Boolean = _ => true,
    merkle: Boolean = true,
    buildTree: Boolean = true,
    buildHashes: Boolean = false,
    optimizedSealed: Boolean = false
) extends Compat
    with ClassName
    with GlobalHelpers {

  import global._

  private def error(msg: String) = throw new RuntimeException(msg)

  // this cache reduces duplicate work both here and when persisting
  //   caches on other structures had minimal effect on time and cache size
  //   (tried: Definition, Modifier, Path, Id, String)
  private[this] val typeCache = perRunCaches.newMap[(Symbol, Type), xsbti.api.Type]()
  // types that `isPlain` admits, which convert the same in any owner, shared by all units
  private[this] val plainTypeCache = new java.util.HashMap[Type, xsbti.api.Type]()
  // these caches are necessary for correctness
  private[this] val structureCache = perRunCaches.newMap[Symbol, xsbti.api.Structure]()
  private[this] val erasedSignatureCache = perRunCaches.newMap[Symbol, xsbti.api.Annotation]()
  private[this] val classLikeCache =
    perRunCaches.newMap[(Symbol, Symbol), xsbti.api.ClassLikeDef]()
  private[this] val pending = perRunCaches.newSet[xsbti.api.Lazy[_]]()

  private[this] val emptyStringArray = Array.empty[String]

  // `<refinement>`, matched by refinementRelativeName below.
  private[this] val refineClassName = tpnme.REFINE_CLASS_NAME.toString

  private[this] val allNonLocalClassSymbols = perRunCaches.newSet[Symbol]()
  private[this] val allNonLocalClassesInSrc = perRunCaches.newSet[xsbti.api.ClassLike]()
  private[this] val _mainClasses = perRunCaches.newSet[String]()

  private[this] var unitId = 0

  /** Forget what the previous compilation unit extracted and registered. */
  def startUnit(): Unit = {
    unitId += 1
    typeCache.clear()
    structureCache.clear()
    classLikeCache.clear()
    pending.clear()
    allNonLocalClassSymbols.clear()
    allNonLocalClassesInSrc.clear()
    _mainClasses.clear()
    fullClasses.clear()
    pendingHashes.clear()
    extracted.clear()
    unitTypeHashes.clear()
    unitDefHs.clear()
    unitStructureHashes.clear()
  }

  private[this] val javaVersion: Int =
    try {
      val version = sys.props("java.specification.version").split("\\.").toList.map(_.toInt)
      version match {
        case 1 :: minor :: _ => minor
        case major :: _      => major
        case _               => 0
      }
    } catch {
      case _: Throwable => 0
    }
  private[this] def isJava25Plus: Boolean = javaVersion >= 25

  /**
   * Implements a work-around for https://github.com/sbt/sbt/issues/823
   *
   * The strategy is to rename all type variables bound by existential type to stable
   * names by assigning to each type variable a De Bruijn-like index. As a result, each
   * type variable gets name of this shape:
   *
   *   "existential_${nestingLevel}_${i}"
   *
   * where `nestingLevel` indicates nesting level of existential types and `i` variable
   * indicates position of type variable in given existential type.
   *
   * For example, let's assume we have the following classes declared:
   *
   *   class A[T]; class B[T,U]
   *
   * and we have type A[_] that is expanded by Scala compiler into
   *
   *   A[_$1] forSome { type _$1 }
   *
   * After applying our renaming strategy we get
   *
   *   A[existential_0_0] forSome { type existential_0_0 }
   *
   * Let's consider a bit more complicated example which shows how our strategy deals with
   * nested existential types:
   *
   *   A[_ <: B[_, _]]
   *
   * which gets expanded into:
   *
   *   A[_$1] forSome {
   *     type _$1 <: B[_$2, _$3] forSome { type _$2; type _$3 }
   *   }
   *
   * After applying our renaming strategy we get
   *
   *   A[existential_0_0] forSome {
   *     type existential_0_0 <: B[existential_1_0, existential_1_1] forSome {
   *       type existential_1_0; type existential_1_1
   *     }
   *   }
   *
   * Note how the first index (nesting level) is bumped for both existential types.
   *
   * This way, all names of existential type variables depend only on the structure of
   * existential types and are kept stable.
   *
   * Both examples presented above used placeholder syntax for existential types but our
   * strategy is applied uniformly to all existential types no matter if they are written
   * using placeholder syntax or explicitly.
   */
  private[this] object existentialRenamings {
    private var nestingLevel: Int = 0
    import scala.collection.mutable.Map
    private val renameTo: Map[Symbol, String] = Map.empty

    def leaveExistentialTypeVariables(typeVariables: Seq[Symbol]): Unit = {
      nestingLevel -= 1
      assert(nestingLevel >= 0, s"nestingLevel = $nestingLevel")
      typeVariables.foreach(renameTo.remove)
    }
    def enterExistentialTypeVariables(typeVariables: Seq[Symbol]): Unit = {
      nestingLevel += 1
      typeVariables.zipWithIndex foreach {
        case (tv, i) =>
          val newName = "existential_" + nestingLevel + "_" + i
          renameTo(tv) = newName
      }
    }
    def renaming(symbol: Symbol): Option[String] =
      if (nestingLevel == 0) None else renameTo.get(symbol)
    def isEmpty: Boolean = nestingLevel == 0
  }

  /**
   * Construct a lazy instance from a by-name parameter that will null out references to once
   * the value is forced and therefore references to thunk's classes will be garbage collected.
   */
  private def lzy[S <: AnyRef](s: => S): xsbti.api.Lazy[S] = {
    val lazyImpl = xsbti.api.SafeLazy.apply(Message(s))
    pending += lazyImpl
    lazyImpl
  }

  /**
   * Force all lazy structures.  This is necessary so that we see the symbols/types at this phase and
   * so that we don't hold on to compiler objects and classes
   */
  @tailrec final def forceStructures(): Unit =
    if (pending.isEmpty)
      structureCache.clear()
    else {
      val toProcess = pending.toList
      pending.clear()
      toProcess foreach { _.get() }
      forceStructures()
    }

  private def thisPath(sym: Symbol) = path(pathComponents(sym, Constants.thisPath :: Nil))
  private def path(components: List[PathComponent]) =
    xsbti.api.Path.of(components.toArray[PathComponent])
  @tailrec
  private def pathComponents(sym: Symbol, postfix: List[PathComponent]): List[PathComponent] = {
    if (sym == NoSymbol || sym.isRoot || sym.isEmptyPackageClass || sym.isRootPackage) postfix
    else pathComponents(sym.owner, xsbti.api.Id.of(simpleName(sym)) :: postfix)
  }
  private def types(in: Symbol, t: List[Type]): Array[xsbti.api.Type] =
    t.toArray[Type].map(processType(in, _))
  private def projectionType(in: Symbol, pre: Type, sym: Symbol) = {
    if (pre == NoPrefix) {
      if (sym.isLocalClass || sym.isRoot || sym.isRootPackage) Constants.emptyType
      else if (sym.isTypeParameterOrSkolem || sym.isExistentiallyBound) reference(sym)
      else {
        // this appears to come from an existential type in an inherited member- not sure why isExistential is false here
        /*println("Warning: Unknown prefixless type: " + sym + " in " + sym.owner + " in " + sym.enclClass)
      println("\tFlags: " + sym.flags + ", istype: " + sym.isType + ", absT: " + sym.isAbstractType + ", alias: " + sym.isAliasType + ", nonclass: " + isNonClassType(sym))*/
        reference(sym)
      }
    } else if (sym.isRoot || sym.isRootPackage) Constants.emptyType
    else xsbti.api.Projection.of(processType(in, pre), simpleName(sym))
  }
  private def reference(sym: Symbol): xsbti.api.ParameterRef =
    xsbti.api.ParameterRef.of(tparamID(sym))

  // Constructing PrintWriters can cause lock contention in highly parallel code,
  // it's constructor looks up the "line.separator" system property which locks
  // on JDK 8.
  //
  // We can safely reuse a single instance, avoiding the lock contention and
  // also reducing allocations a little.
  private object ReusableTreePrinter {
    import java.io._
    private val buffer = new StringWriter()
    private val printWriter = new PrintWriter(buffer)
    private val treePrinter = newTreePrinter(printWriter)

    /** More efficient version of trees.mkString(start, sep, end) */
    def mkString(trees: List[Tree], start: String, sep: String, end: String): String = {
      var rest: List[Tree] = trees
      printWriter.append(start)
      while (rest != Nil) {
        treePrinter.printTree(rest.head)
        rest = rest.tail
        if (rest != Nil) {
          printWriter.append(sep)
        }
      }
      printWriter.append(end)
      getAndResetBuffer()
    }
    private def getAndResetBuffer(): String = {
      printWriter.flush()
      try buffer.getBuffer.toString
      finally buffer.getBuffer.setLength(0)
    }
  }

  private[this] val printedArgsCache = new java.util.IdentityHashMap[AnnotationInfo, String]()
  private def printedArgs(a: AnnotationInfo): String = {
    val cached = printedArgsCache.get(a)
    if (cached ne null) cached
    else {
      val printed = ReusableTreePrinter.mkString(a.args, "(", ",", ")")
      printedArgsCache.put(a, printed)
      printed
    }
  }

  // The compiler only pickles static annotations, so only include these in the API.
  // This way, the API is not sensitive to whether we compiled from source or loaded from classfile.
  // (When looking at the sources we see all annotations, but when loading from classes we only see the pickled (static) ones.)
  private def mkAnnotations(in: Symbol, as: List[AnnotationInfo]): Array[xsbti.api.Annotation] = {
    if (in == NoSymbol) ExtractAPI.emptyAnnotationArray
    else
      staticAnnotations(as) match {
        case Nil      => ExtractAPI.emptyAnnotationArray
        case staticAs =>
          staticAs.map { a =>
            xsbti.api.Annotation.of(
              processType(in, a.atp),
              if (a.assocs.isEmpty)
                Array(
                  xsbti.api.AnnotationArgument
                    .of("", printedArgs(a))
                ) // what else to do with a Tree?
              else
                a.assocs
                  .map {
                    case (name, value) =>
                      xsbti.api.AnnotationArgument.of(name.toString, value.toString)
                  }
                  .toArray[xsbti.api.AnnotationArgument]
            )
          }.toArray
      }
  }

  // HOT method, hand optimized to reduce allocations and needless creation of Names with calls to getterIn/setterIn
  // on non-fields.
  private def annotations(in: Symbol, s: Symbol): Array[xsbti.api.Annotation] = {
    val saved = phase
    phase = currentRun.typerPhase
    try {
      val base = if (s.hasFlag(Flags.ACCESSOR)) s.accessed else NoSymbol
      val b = if (base == NoSymbol) s else base
      // annotations from bean methods are not handled because:
      //  a) they are recorded as normal source methods anyway
      //  b) there is no way to distinguish them from user-defined methods
      if (b.hasGetter) {
        val annotations = collection.mutable.LinkedHashSet[xsbti.api.Annotation]()
        def add(sym: Symbol) = if (sym != NoSymbol) {
          val anns = mkAnnotations(in, sym.annotations)
          var i = 0
          while (i < anns.length) {
            annotations += anns(i)
            i += 1
          }
        }
        add(b)
        add(b.getterIn(b.enclClass))
        add(b.setterIn(b.enclClass))
        annotations.toArray
      } else {
        if (b.annotations.isEmpty) ExtractAPI.emptyAnnotationArray
        else mkAnnotations(in, b.annotations)
      }
    } finally {
      phase = saved
    }
  }

  /**
   * Bridges, mixin and mirror forwarders are generated from the erasure of a member as declared
   * in its owner, which the source signature as seen from `in` does not determine: a value class
   * erases to its underlying type, an intersection to its dominator, and a type parameter of the
   * owner to its bound. Hashing the erased signature with the member makes the API of every class
   * that declares or inherits it change exactly when that erasure does.
   */
  private def withErasedSignature(
      s: Symbol,
      as: Array[xsbti.api.Annotation]
  ): Array[xsbti.api.Annotation] = {
    val erased = erasedSignatureCache.getOrElseUpdate(
      s,
      xsbti.api.Annotation.of(
        ExtractAPI.erasedSignatureMarker,
        Array(xsbti.api.AnnotationArgument.of("descriptor", erasedSignature(transformedType(s))))
      )
    )
    as :+ erased
  }

  private def erasedSignature(tp: Type): String = tp match {
    case MethodType(params, res) =>
      params.map(p => erasedSignature(p.info)).mkString("(", ",", ")") + erasedSignature(res)
    case NullaryMethodType(res)                                       => "()" + erasedSignature(res)
    case TypeRef(_, sym, arg :: Nil) if sym == definitions.ArrayClass =>
      "[" + erasedSignature(arg)
    case TypeRef(_, sym, _) => sym.fullName
    case _                  => tp.typeSymbol.fullName
  }

  private def viewer(s: Symbol) = (if (s.isModule) s.moduleClass else s).thisType

  private def defDef(in: Symbol, s: Symbol): xsbti.api.Def = {
    @tailrec
    def build(
        t: Type,
        typeParams: Array[xsbti.api.TypeParameter],
        valueParameters: List[xsbti.api.ParameterList]
    ): xsbti.api.Def = {
      def parameterList(syms: List[Symbol]): xsbti.api.ParameterList = {
        val isImplicitList = cond(syms) { case head :: _ => isImplicit(head) }
        xsbti.api.ParameterList.of(syms.map(parameterS).toArray, isImplicitList)
      }
      t match {
        case PolyType(typeParams0, base) =>
          assert(typeParams.isEmpty, typeParams.toString)
          assert(valueParameters.isEmpty, valueParameters.toString)
          build(base, typeParameters(in, typeParams0), Nil)
        case MethodType(params, resultType) =>
          build(resultType, typeParams, parameterList(params) :: valueParameters)
        case NullaryMethodType(resultType) =>
          build(resultType, typeParams, valueParameters)
        case returnType =>
          val retType = processType(in, dropConst(returnType))
          xsbti.api.Def.of(
            simpleNameForMethod(s),
            getAccess(s),
            getModifiers(s),
            withErasedSignature(s, annotations(in, s)),
            typeParams,
            valueParameters.reverse.toArray,
            retType
          )
      }
    }
    def parameterS(s: Symbol): xsbti.api.MethodParameter = {
      val tp: global.Type = s.info
      makeParameter(simpleName(s), tp, tp.typeSymbol, s)
    }

    def makeParameter(
        name: String,
        tpe: Type,
        ts: Symbol,
        paramSym: Symbol
    ): xsbti.api.MethodParameter = {
      import xsbti.api.ParameterModifier._
      val (t, special) =
        if (ts == definitions.RepeatedParamClass) // || s == definitions.JavaRepeatedParamClass)
          (tpe.typeArgs.head, Repeated)
        else if (ts == definitions.ByNameParamClass)
          (tpe.typeArgs.head, ByName)
        else
          (tpe, Plain)
      xsbti.api.MethodParameter.of(name, processType(in, t), hasDefault(paramSym), special)
    }
    val t = viewer(in).memberInfo(s)
    build(t, Array(), Nil)
  }
  private def hasDefault(s: Symbol) = s != NoSymbol && s.hasFlag(Flags.DEFAULTPARAM)
  private def fieldDef[T](
      in: Symbol,
      s: Symbol,
      keepConst: Boolean,
      create: (
          String,
          xsbti.api.Access,
          xsbti.api.Modifiers,
          Array[xsbti.api.Annotation],
          xsbti.api.Type
      ) => T
  ): T = {
    val t = dropNullary(viewer(in).memberType(s))
    val t2 = if (keepConst) t else dropConst(t)
    val as = withErasedSignature(s, annotations(in, s))
    create(simpleName(s), getAccess(s), getModifiers(s), as, processType(in, t2))
  }
  private def dropConst(t: Type): Type = t match {
    case ConstantType(constant) => constant.tpe
    case _                      => t
  }
  private def dropNullary(t: Type): Type = t match {
    case NullaryMethodType(un) => un
    case _                     => t
  }

  private def typeDef(in: Symbol, s: Symbol): xsbti.api.TypeMember = {
    val (typeParams, tpe) =
      viewer(in).memberInfo(s) match {
        case PolyType(typeParams0, base) => (typeParameters(in, typeParams0), base)
        case t                           => (Array[xsbti.api.TypeParameter](), t)
      }
    val name = simpleName(s)
    val access = getAccess(s)
    val modifiers = getModifiers(s)
    val as = annotations(in, s)

    if (s.isAliasType)
      xsbti.api.TypeAlias.of(name, access, modifiers, as, typeParams, processType(in, tpe))
    else if (s.isAbstractType) {
      val bounds = tpe.bounds
      xsbti.api.TypeDeclaration.of(
        name,
        access,
        modifiers,
        as,
        typeParams,
        processType(in, bounds.lo),
        processType(in, bounds.hi)
      )
    } else
      error("Unknown type member" + s)
  }

  private def structure(info: Type, s: Symbol): xsbti.api.Structure =
    structureCache.getOrElseUpdate(s, mkStructure(info, s))
  private def structureWithInherited(info: Type, s: Symbol): xsbti.api.Structure =
    structureCache.getOrElseUpdate(s, mkStructureWithInherited(info, s))

  private def removeConstructors(ds: List[Symbol]): List[Symbol] = ds filter { !_.isConstructor }

  /**
   * Create structure as-is, without embedding ancestors
   *
   * (for refinement types, and ClassInfoTypes encountered outside of a definition???).
   */
  private def mkStructure(info: Type, s: Symbol): xsbti.api.Structure = {
    // We're not interested in the full linearization, so we can just use `parents`,
    // which side steps issues with baseType when f-bounded existential types and refined types mix
    // (and we get cyclic types which cause a stack overflow in showAPI).
    val parentTypes = info.parents
    val decls = info.decls.toList
    val declsNoModuleCtor = if (s.isModuleClass) removeConstructors(decls) else decls
    mkStructure(s, parentTypes, declsNoModuleCtor, Nil)
  }

  /**
   * Track all ancestors and inherited members for a class's API.
   *
   * A class's hash does not include hashes for its parent classes -- only the symbolic names --
   * so we must ensure changes propagate somehow.
   *
   * TODO: can we include hashes for parent classes instead? This seems a bit messy.
   *
   * Under Merkle hashing (`merkle`), Zinc does compose them: members inherited from analysed
   * classes are left out, and library ones may be stubs.
   */
  private def mkStructureWithInherited(info: Type, s: Symbol): xsbti.api.Structure = {
    val ancestorTypes0 = linearizedAncestorTypes(info)
    val ancestorTypes =
      if (s.isDerivedValueClass) {
        val underlying = s.derivedValueClassUnbox.tpe.finalResultType
        // The underlying type of a value class should be part of the name hash
        // of the value class (see the test `value-class-underlying`), this is accomplished
        // by adding the underlying type to the list of parent types.
        underlying :: ancestorTypes0
      } else
        ancestorTypes0
    val decls = info.decls.toList
    val declsNoModuleCtor = if (s.isModuleClass) removeConstructors(decls) else decls
    if (merkle) {
      val (inherited, platform) =
        ancestorDecls(info).partition(m => !isStubbedOwner(m.owner) || discoveryReads(m))
      mkStructure(s, ancestorTypes, declsNoModuleCtor, inherited, platform.flatMap(stub))
    } else {
      val declSet = decls.toSet
      val inherited =
        info.nonPrivateMembers.toList.filterNot(declSet) // private members are not inherited
      mkStructure(s, ancestorTypes, declsNoModuleCtor, inherited)
    }
  }

  /**
   * Is `owner` defined in this subproject, or in another one that Zinc has analysed? Zinc
   * composes the name hashes of members inherited from such classes from their own decls, so
   * they are not materialised here, except annotated ones: test discovery reads the annotations
   * of inherited methods (a JUnit `@Test` in a base class). Members of plain library classes
   * still are.
   */
  private def isInternal(owner: Symbol): Boolean = {
    val cached = internalCache.get(owner)
    if (cached ne null) cached.booleanValue
    else {
      val b = isInternal0(owner)
      internalCache.put(owner, b)
      b
    }
  }

  private[this] val internalCache = new java.util.HashMap[Symbol, java.lang.Boolean]()

  /**
   * Is `owner` part of the platform: `Any`, `AnyRef`/`Object`, or a class of scala-library or
   * scala-reflect? Those change only with the Scala version, which recompiles everything, or
   * (for `Object`) not at all, so their members are materialised as stubs without types (`==`,
   * `hashCode`, `Product`'s members in each case class). Other JDK classes are not included: a
   * JDK upgrade need not recompile, and it can add inherited members.
   */
  private def isPlatform(owner: Symbol): Boolean = {
    val cached = platformCache.get(owner)
    if (cached ne null) cached.booleanValue
    else {
      val b = isPlatform0(owner)
      platformCache.put(owner, b)
      b
    }
  }

  private[this] val platformCache = new java.util.HashMap[Symbol, java.lang.Boolean]()

  /**
   * Are members inherited from `owner` recorded as stubs (name, access, modifiers) rather than in
   * full? Always for the platform. For other libraries, unless Zinc asks for their members: it
   * otherwise treats a library ancestor coarsely, invalidating by the names a class inherits from
   * it when its jar changes, rather than copying its signatures into every descendant.
   */
  private def isStubbedOwner(owner: Symbol): Boolean =
    stubbedOwnerCache.getOrElseUpdate(
      owner,
      isPlatform(owner) || !materialiseLibraryMembers(flatname(owner, '.') + owner.moduleSuffix)
    )

  private[this] val stubbedOwnerCache = perRunCaches.newMap[Symbol, Boolean]()

  private def isPlatform0(owner: Symbol): Boolean =
    owner == definitions.AnyClass || owner == definitions.AnyRefClass ||
      owner == definitions.ObjectClass ||
      (owner.associatedFile match {
        case entry: scala.reflect.io.ZipArchive#Entry =>
          entry.underlyingSource.exists { jar =>
            jar.name.startsWith("scala-library") || jar.name.startsWith("scala-reflect")
          }
        case _ => false
      })

  private def isInternal0(owner: Symbol): Boolean =
    isSubprojectClass(flatname(owner, '.') + owner.moduleSuffix) ||
      (owner.sourceFile match {
        case AbstractZincFile(_) => true
        case _                   =>
          val at = owner.associatedFile
          def inOutput(f: java.io.File) =
            f != null &&
              outputDirs.exists(d => f.toPath.toAbsolutePath.startsWith(d.toAbsolutePath))
          at match {
            case null                                     => false
            case entry: scala.reflect.io.ZipArchive#Entry =>
              entry.underlyingSource.exists(z => inOutput(z.file))
            case f => inOutput(f.file)
          }
      })

  // Note that the ordering of classes in `baseClasses` is important.
  // It would be easier to just say `baseTypeSeq.toList.tail`,
  // but that does not take linearization into account.
  def linearizedAncestorTypes(info: Type): List[Type] = info.baseClasses.tail.map(info.baseType)

  private def mkStructure(
      s: Symbol,
      bases: List[Type],
      declared: List[Symbol],
      inherited: List[Symbol],
      stubs: List[xsbti.api.ClassDefinition] = Nil
  ): xsbti.api.Structure = {
    xsbti.api.Structure.of(
      lzy(types(s, bases)),
      lzy(processDefinitions(s, declared)),
      lzy(processDefinitions(s, inherited) ++ stubs.sortBy(_.name))
    )
  }

  /**
   * The declarations a class's ancestors contribute to its API: every non-private declaration of
   * every library base class, and those of a base class in this subproject that discovery reads.
   * Overridden declarations are included, and no member's type is consulted: a name's hashes
   * combine all its declarations along the linearization, as Zinc's composition does for ancestors
   * in this subproject. That is a superset of the inherited members, and it keeps the declarations
   * of library ancestors that another ancestor overrides, which descendant invalidation needs:
   * when `class D extends P with LibT` and `P` stops implementing `LibT`'s abstract `n`, `D` must
   * recompile, and a library class has no stored API to show that `n` is abstract there. Scala 3's
   * `ExtractAPI` also takes all declarations of each base class. The walk mirrors
   * `FindMembers.walkBaseClasses`, but without its override checks, which compare member types as
   * seen from the class.
   */
  private def ancestorDecls(info: Type): List[Symbol] = {
    val result = new collection.mutable.ListBuffer[Symbol]
    val flagMask = phase.flagMask
    val fastFlags = (flagMask & ~Flags.InitialFlags) == 0
    var bcs = info.baseClasses
    if (bcs ne Nil) bcs = bcs.tail
    while (bcs ne Nil) {
      val bc = bcs.head
      val internal = isInternal(bc)
      var ms = bc.info.decls.toList
      while (ms ne Nil) {
        val m = ms.head
        val flags = if (fastFlags) m.rawflags & flagMask else m.flags & flagMask
        if (
          (flags & Flags.BridgeAndPrivateFlags) == 0 && !m.isConstructor &&
          (!internal || discoveryReadsAnnotations(m))
        ) result += m
        ms = ms.tail
      }
      bcs = bcs.tail
    }
    result.toList
  }

  /** Test and main-class discovery read inherited annotations and `main` signatures. */
  private def discoveryReads(m: Symbol): Boolean = discoveryReadsAnnotations(m) ||
    m.name == nme.main

  /**
   * Does `m` carry an annotation discovery can read? Only static annotations count, as in
   * `mkAnnotations`: a source-only one such as `@nowarn` is present when `m`'s owner is compiled
   * in the same run and absent when it is read from a classfile, so counting it would make a
   * descendant's API depend on the batch. `m`'s type is completed first: on a member read from a
   * classfile, scalac adds `@throws` only then, so it would be present or not depending on what
   * else the run had typed.
   */
  private def discoveryReadsAnnotations(m: Symbol): Boolean = {
    m.info
    staticAnnotations(m.annotations).nonEmpty
  }

  /**
   * A library member as a name with its access and modifiers, but no types: descendant
   * invalidation still sees which names a class inherits, and which are abstract, without
   * paying for their signatures. Type members and classes count too, except the platform's.
   */
  private def stub(m: Symbol): Option[xsbti.api.ClassDefinition] = {
    var s = stubCache.get(m)
    if (s eq null) {
      s = stub0(m)
      stubCache.put(m, s)
    }
    s
  }
  private[this] val stubCache = new java.util.HashMap[Symbol, Option[xsbti.api.ClassDefinition]]()
  private def stub0(m: Symbol): Option[xsbti.api.ClassDefinition] =
    if (
      ((isClass(m) || m.isNonClassType) && isPlatform(m.owner)) ||
      (m.isMethod && (!m.isSourceMethod || m.isSetter))
    ) None
    else {
      val name = if (m.isMethod) simpleNameForMethod(m) else simpleName(m)
      Some(
        xsbti.api.Def.of(
          name,
          getAccess(m),
          getModifiers(m),
          Array.empty,
          Array.empty,
          Array.empty,
          Constants.emptyType
        )
      )
    }
  private def processDefinitions(in: Symbol, defs: List[Symbol]): Array[xsbti.api.ClassDefinition] =
    sort(defs.toArray).flatMap((d: Symbol) => definition(in, d))
  private[this] def sort(defs: Array[Symbol]): Array[Symbol] = {
    Arrays.sort(defs, sortClasses)
    defs
  }

  private def definition(in: Symbol, sym: Symbol): Option[xsbti.api.ClassDefinition] = {
    def mkVar = Some(fieldDef(in, sym, keepConst = false, xsbti.api.Var.of(_, _, _, _, _)))
    def mkVal = Some(fieldDef(in, sym, keepConst = true, xsbti.api.Val.of(_, _, _, _, _)))
    if (isClass(sym))
      if (ignoreClass(sym)) {
        allNonLocalClassSymbols.+=(sym); None
      } else Some(classLike(in, sym))
    else if (sym.isNonClassType)
      Some(typeDef(in, sym))
    else if (sym.isVariable)
      if (isSourceField(sym)) mkVar else None
    else if (sym.isStable)
      if (isSourceField(sym)) mkVal else None
    else if (sym.isSourceMethod && !sym.isSetter)
      if (sym.isGetter) mkVar else Some(defDef(in, sym))
    else
      None
  }
  private def ignoreClass(sym: Symbol): Boolean =
    sym.isLocalClass || sym.isAnonymousClass || sym.fullName.endsWith(tpnme.LOCAL_CHILD.toString)

  // This filters private[this] vals/vars that were not in the original source.
  //  The getter will be used for processing instead.
  private def isSourceField(sym: Symbol): Boolean = {
    val getter = sym.getterIn(sym.enclClass)
    // the check `getter eq sym` is a precaution against infinite recursion
    // `isParamAccessor` does not exist in all supported versions of Scala, so the flag check is done directly
    (getter == NoSymbol && !sym.hasFlag(Flags.PARAMACCESSOR)) || (getter eq sym)
  }
  private[this] val modifiersCache = new java.util.HashMap[Symbol, xsbti.api.Modifiers]()
  private def getModifiers(s: Symbol): xsbti.api.Modifiers = {
    var m = modifiersCache.get(s)
    if (m eq null) {
      m = getModifiers0(s)
      modifiersCache.put(s, m)
    }
    m
  }
  private def getModifiers0(s: Symbol): xsbti.api.Modifiers = {
    import Flags._
    import xsbt.Compat._
    val absOver = s.hasFlag(ABSOVERRIDE)
    val abs = s.hasFlag(ABSTRACT) || s.hasFlag(DEFERRED) || absOver
    val over = s.hasFlag(OVERRIDE) || absOver
    val hasInline = global.settings.optInlinerEnabled && s.annotations.exists(
      _.symbol.tpe == typeOf[scala.inline]
    )
    new xsbti.api.Modifiers(
      abs,
      over,
      s.isFinal,
      s.hasFlag(SEALED),
      isImplicit(s),
      s.hasFlag(LAZY),
      (s.hasFlag(MACRO) && !isStubMacro(s)) || hasInline,
      s.hasFlag(SUPERACCESSOR)
    )
  }

  private def isImplicit(s: Symbol) = s.hasFlag(Flags.IMPLICIT)
  private[this] val accessCache = new java.util.HashMap[Symbol, xsbti.api.Access]()
  private def getAccess(c: Symbol): xsbti.api.Access = {
    var a = accessCache.get(c)
    if (a eq null) {
      a = getAccess0(c)
      accessCache.put(c, a)
    }
    a
  }
  private def getAccess0(c: Symbol): xsbti.api.Access = {
    if (c.isPublic) Constants.public
    else if (c.isPrivateLocal) Constants.privateLocal
    else if (c.isProtectedLocal) Constants.protectedLocal
    else {
      val within = c.privateWithin
      val qualifier =
        if (within == NoSymbol) Constants.unqualified
        else xsbti.api.IdQualifier.of(within.fullName)
      if (c.hasFlag(Flags.PROTECTED)) xsbti.api.Protected.of(qualifier)
      else xsbti.api.Private.of(qualifier)
    }
  }

  /**
   * Replace all types that directly refer to the `forbidden` symbol by `NoType`.
   * (a specialized version of substThisAndSym)
   */
  class SuppressSymbolRef(forbidden: Symbol) extends TypeMap {
    def apply(tp: Type) =
      if (tp.typeSymbolDirect == forbidden) NoType
      else mapOver(tp)
  }

  private def processType(in: Symbol, t: Type): xsbti.api.Type =
    if (existentialRenamings.isEmpty) {
      val plain = plainTypeCache.get(t)
      if (plain ne null) plain
      else if (isPlain(t)) {
        val made = makeType(in, t)
        plainTypeCache.put(t, made)
        made
      } else typeCache.getOrElseUpdate((in, t), makeType(in, t))
    } else typeCache.getOrElseUpdate((in, t), makeType(in, t))

  /**
   * Whether `t` converts and hashes the same in any owner and outside existential renamings: it
   * names classes, prefixes and type parameters only, and holds no alias, refinement, raw Java
   * type, annotation or binder (existential or polymorphic), whose conversion reads `in`.
   */
  private def isPlain(t: Type): Boolean = t match {
    case TypeRef(pre, sym, args) =>
      !sym.isAliasType && !sym.isRefinementClass && isPlain(pre) && {
        if (args.isEmpty) !isRawType(t)
        else {
          var rest = args
          while ((rest ne Nil) && isPlain(rest.head)) rest = rest.tail
          rest eq Nil
        }
      }
    case ThisType(_)        => true
    case SingleType(pre, _) => isPlain(pre)
    case ConstantType(_)    => true
    case NoPrefix | NoType  => true
    case _                  => false
  }
  private def makeType(in: Symbol, t: Type): xsbti.api.Type = {

    val dealiased = t match {
      case TypeRef(_, sym, _) if sym.isAliasType => t.dealias
      case _                                     => t
    }

    dealiased match {
      case NoPrefix               => Constants.emptyType
      case ThisType(sym)          => xsbti.api.Singleton.of(thisPath(sym))
      case SingleType(pre, sym)   => projectionType(in, pre, sym)
      case ConstantType(constant) =>
        xsbti.api.Constant.of(processType(in, constant.tpe), constant.stringValue)

      /* explaining the special-casing of references to refinement classes (https://support.typesafe.com/tickets/1882)
       *
       * goal: a representation of type references to refinement classes that's stable across compilation runs
       *       (and thus insensitive to typing from source or unpickling from bytecode)
       *
       * problem: the current representation, which corresponds to the owner chain of the refinement:
       *   1. is affected by pickling, so typing from source or using unpickled symbols give different results (because the unpickler "localizes" owners -- this could be fixed in the compiler)
       *   2. can't distinguish multiple refinements in the same owner (this is a limitation of SBT's internal representation and cannot be fixed in the compiler)
       *
       * potential solutions:
       *   - simply drop the reference: won't work as collapsing all refinement types will cause recompilation to be skipped when a refinement is changed to another refinement
       *   - represent the symbol in the api: can't think of a stable way of referring to an anonymous symbol whose owner changes when pickled
       *   + expand the reference to the corresponding refinement type: doing that recursively may not terminate, but we can deal with that by approximating recursive references
       *     (all we care about is being sound for recompilation: recompile iff a dependency changes, and this will happen as long as we have one unrolling of the reference to the refinement)
       */
      case TypeRef(pre, sym, Nil) if sym.isRefinementClass =>
        // Since we only care about detecting changes reliably, we unroll a reference to a refinement class once.
        // Recursive references are simply replaced by NoType -- changes to the type will be seen in the first unrolling.
        // The API need not be type correct, so this truncation is acceptable. Most of all, the API should be compact.
        val unrolling = pre.memberInfo(sym) // this is a refinement type

        // in case there are recursive references, suppress them -- does this ever happen?
        // we don't have a test case for this, so warn and hope we'll get a contribution for it :-)
        val withoutRecursiveRefs = new SuppressSymbolRef(sym).mapOver(unrolling)
        if (unrolling ne withoutRecursiveRefs)
          reporter.warning(
            sym.pos,
            "sbt-api: approximated refinement ref" + t + " (== " + unrolling + ") to " +
              withoutRecursiveRefs +
              "\nThis is currently untested, please report the code you were compiling."
          )

        structure(withoutRecursiveRefs, sym)
      case tr @ TypeRef(pre, sym, args) =>
        val base = projectionType(in, pre, sym)
        if (args.isEmpty)
          if (isRawType(tr))
            processType(in, rawToExistential(tr))
          else
            base
        else
          xsbti.api.Parameterized.of(base, types(in, args))
      case SuperType(thistpe: Type, supertpe: Type) =>
        reporter.warning(
          NoPosition,
          "sbt-api: Super type (not implemented): this=" + thistpe + ", super=" + supertpe
        )
        Constants.emptyType
      case at: AnnotatedType =>
        at.annotations match {
          case Nil    => processType(in, at.underlying)
          case annots =>
            xsbti.api.Annotated.of(processType(in, at.underlying), mkAnnotations(in, annots))
        }
      case rt: CompoundType   => structure(rt, rt.typeSymbol)
      case t: ExistentialType => makeExistentialType(in, t)
      case NoType             =>
        Constants.emptyType // this can happen when there is an error that will be reported by a later phase
      case PolyType(typeParams, resultType) =>
        xsbti.api.Polymorphic.of(processType(in, resultType), typeParameters(in, typeParams))
      case NullaryMethodType(_) =>
        reporter.warning(
          NoPosition,
          "sbt-api: Unexpected nullary method type " + in + " in " + in.owner
        )
        Constants.emptyType
      case MethodType(_, _) =>
        reporter.echo(NoPosition, s"sbt-api: Unhandled method type $in in ${in.owner}")
        Constants.emptyType
      case _ =>
        reporter.warning(NoPosition, "sbt-api: Unhandled type " + t.getClass + " : " + t)
        Constants.emptyType
    }
  }
  private def makeExistentialType(in: Symbol, t: ExistentialType): xsbti.api.Existential = {
    val ExistentialType(typeVariables, qualified) = t
    existentialRenamings.enterExistentialTypeVariables(typeVariables)
    try {
      val typeVariablesConverted = typeParameters(in, typeVariables)
      val qualifiedConverted = processType(in, qualified)
      xsbti.api.Existential.of(qualifiedConverted, typeVariablesConverted)
    } finally {
      existentialRenamings.leaveExistentialTypeVariables(typeVariables)
    }
  }
  private def typeParameters(in: Symbol, s: Symbol): Array[xsbti.api.TypeParameter] =
    typeParameters(in, s.typeParams)
  private def typeParameters(in: Symbol, s: List[Symbol]): Array[xsbti.api.TypeParameter] =
    s.map(typeParameter(in, _)).toArray[xsbti.api.TypeParameter]
  private def typeParameter(in: Symbol, s: Symbol): xsbti.api.TypeParameter = {
    val varianceInt = s.variance
    import xsbti.api.Variance._
    val annots = annotations(in, s)
    val variance =
      if (varianceInt < 0) Contravariant else if (varianceInt > 0) Covariant else Invariant
    viewer(in).memberInfo(s) match {
      case TypeBounds(low, high) =>
        xsbti.api.TypeParameter.of(
          tparamID(s),
          annots,
          typeParameters(in, s),
          variance,
          processType(in, low),
          processType(in, high)
        )
      case PolyType(typeParams, base) =>
        xsbti.api.TypeParameter.of(
          tparamID(s),
          annots,
          typeParameters(in, typeParams),
          variance,
          processType(in, base.bounds.lo),
          processType(in, base.bounds.hi)
        )
      case x => error("Unknown type parameter info: " + x.getClass)
    }
  }
  private def tparamID(s: Symbol): String =
    existentialRenamings.renaming(s) match {
      case Some(rename) =>
        debuglog(s"Renaming existential type variable ${s.fullName} to $rename")
        rename
      case None =>
        val name = refinementRelativeName(s)
        if (!name.startsWith(refineClassName) && ownedByNonClassType(s)) s.nameString
        else name
    }

  /**
   * Is `s` a type parameter of a type alias or abstract type, or one the unpickler gave no owner?
   * The pickler stores such a parameter as local to the pickle, with an owner of its own
   * (`nonClassRoot`) rather than the alias, so when the alias is eta-expanded (`F[List]`) its
   * parameter's full name is `scala.package.A` from source but `<none>.A` once unpickled. Only
   * the binding within the type lambda matters, so the simple name is enough. A parameter
   * declared inside a refinement keeps its refinement-relative name, which is already stable.
   *
   * Typed from source on 2.13, an eta-expansion's parameter is owned by the alias's local dummy
   * (`value <local List>`) rather than by the alias itself, so that counts as the alias too.
   */
  private def ownedByNonClassType(s: Symbol): Boolean = {
    val owner = s.owner
    (owner eq NoSymbol) || owner.isNonClassType ||
    (owner.isLocalDummy && owner.owner.isNonClassType)
  }

  /**
   * `s.fullName` cut at the outermost refinement class. The pickler rewrites that class's
   * owner (scala/bug#6596), so the full name of a type parameter declared inside a refinement
   * differs between typing from source and unpickling, flipping the API hash of every class
   * built on it (sbt/sbt#1079). Names with no refinement in the owner chain are unchanged.
   */
  private def refinementRelativeName(s: Symbol): String = {
    val full = s.fullName
    val start = full.indexOf(refineClassName)
    if (start < 0) full else full.substring(start)
  }

  /* Representation for the self type of a class symbol `s`, or `emptyType` for an *unascribed* self variable (or no self variable at all).
     Only the self variable's explicitly ascribed type is relevant for incremental compilation. */
  private def selfType(in: Symbol, s: Symbol): xsbti.api.Type =
    // `sym.typeOfThis` is implemented as `sym.thisSym.info`, which ensures the *self* symbol is initialized (the type completer is run).
    // We can safely avoid running the type completer for `thisSym` for *class* symbols where `thisSym == this`,
    // as that invariant is established on completing the class symbol (`mkClassLike` calls `s.initialize` before calling us).
    // Technically, we could even ignore a self type that's a supertype of the class's type,
    // as it does not contribute any information relevant outside of the class definition.
    if ((s.thisSym eq s) || (s.thisSym.tpeHK == s.tpeHK)) Constants.emptyType
    else processType(in, s.typeOfThis)

  def extractAllClassesOf(in: Symbol, c: Symbol): Unit = {
    classLike(in, c)
    ()
  }

  def allExtractedNonLocalClasses: Set[ClassLike] = {
    forceStructures()
    allNonLocalClassesInSrc.toSet
  }

  def allExtractedNonLocalSymbols: Set[Symbol] = allNonLocalClassSymbols.toSet

  def mainClasses: Set[String] = {
    forceStructures()
    _mainClasses.toSet
  }

  /**
   * A class extracted with its hashes: `full` is the full API (when `buildTree`), `thin` the part
   * Zinc keeps, as `APIUtil.minimizeWithStubs` produces it.
   */
  final class Extracted(val full: ClassLike, val thin: ClassLike, val hashes: xsbti.ClassHashes)

  private def isModuleDefType(d: DefinitionType): Boolean =
    d == DefinitionType.Module || d == DefinitionType.PackageModule

  private final class PendingClass(
      val in: Symbol,
      val c: Symbol,
      val sym: Symbol,
      val info: Type,
      val name: String,
      val acc: xsbti.api.Access,
      val modifiers: xsbti.api.Modifiers,
      val anns: Array[xsbti.api.Annotation],
      val defType: DefinitionType,
      val selfType: xsbti.api.Lazy[xsbti.api.Type],
      val childrenOfSealedClass: Array[xsbti.api.Type],
      val topLevel: Boolean,
      val tParams: Array[xsbti.api.TypeParameter]
  ) {
    def isModule: Boolean = isModuleDefType(defType)
  }

  /**
   * Keyed by name and whether the class is a module: a class and its companion object share the
   * name, and Zinc needs both (keyed by name alone, the one extracted last replaced the other).
   */
  private[this] val fullClasses = perRunCaches.newMap[(String, Boolean), ClassLike]()
  private[this] val pendingHashes = collection.mutable.ArrayBuffer[PendingClass]()
  private[this] val extracted = collection.mutable.LinkedHashMap[(String, Boolean), Extracted]()

  /** The classes extracted from this unit, each with its thin API and hashes (`buildHashes`). */
  def allExtracted: List[Extracted] = {
    forceAll()
    extracted.valuesIterator.toList
  }

  @tailrec private def forceAll(): Unit = {
    forceStructures()
    if (pendingHashes.nonEmpty) {
      val todo = pendingHashes.toList
      pendingHashes.clear()
      todo.foreach(p => extracted((p.name, p.isModule)) = hashClass(p))
      forceAll()
    }
  }

  /*
   * Direct hashing. Each function below mirrors the `xsbti.api` value that `makeType`,
   * `definition` and `mkClassLike` would build, and `HashAPI` would hash, folding the same
   * information into an `Int` without allocating the value. See "Name-hash contract" in
   * PLAN-merkle-poc.md.
   *
   * Memoisation. Hashes keyed by a symbol alone (names, modifiers, erased signatures, stubs) and
   * hashes of plain types (`isPlain`) depend on nothing else, and are shared by all units of the
   * run, so members inherited from libraries, platform stubs and common types are hashed once.
   * Hashes per (owner, type) and per (owner, member) are kept per unit, like `typeCache`, except
   * for owners that are refinement classes, which other units reach through aliases. A hash
   * computed inside an existential depends on the renaming in force, so it is kept per unit and
   * seen only by that unit, which reproduces the per-unit `typeCache` of the tree path.
   */
  private object H {
    final val ValHash = 1
    final val VarHash = 2
    final val DefHash = 3
    final val ClassDefHash = 4
    final val TypeDeclHash = 5
    final val TypeAliasHash = 6
    final val PublicHash = 30
    final val ProtectedHash = 31
    final val PrivateHash = 32
    final val UnqualifiedHash = 33
    final val ThisQualifierHash = 34
    final val IdQualifierHash = 35
    final val ThisPathHash = 22
    final val ValueParamsHash = 40
    final val StructurePendingHash = 42
    final val EmptyTypeHash = 51
    final val ParameterRefHash = 52
    final val SingletonHash = 53
    final val ProjectionHash = 54
    final val ParameterizedHash = 55
    final val AnnotatedHash = 56
    final val PolymorphicHash = 57
    final val ConstantHash = 58
    final val ExistentialHash = 59
    final val StructureHash = 60
    final val ClassHash = 70
    final val TraitHash = 71
    final val ErasedSignatureHash = 80
    final val ListHash = 90
    final val TrueHash = 97
    final val FalseHash = 98
  }
  import scala.util.hashing.MurmurHash3

  @inline private def mix(h: Int, d: Int): Int = MurmurHash3.mix(h, d)
  @inline private def strHash(s: String): Int = MurmurHash3.stringHash(s)
  @inline private def boolHash(b: Boolean): Int = if (b) H.TrueHash else H.FalseHash

  private final class Unordered {
    private[this] var a, b, n = 0
    private[this] var c = 1
    def add(h: Int): Unit = {
      a += h; b ^= h; if (h != 0) c *= h; n += 1
    }
    def result: Int =
      MurmurHash3.finalizeHash(mix(mix(mix(H.ListHash, a), b), c), n)
  }

  private def listHash[A](as: List[A])(f: A => Int): Int = {
    var h = mix(H.ListHash, as.length)
    var rest = as
    while (rest ne Nil) {
      h = mix(h, f(rest.head))
      rest = rest.tail
    }
    MurmurHash3.finalizeHash(h, 0)
  }

  /** `listHash(xs)(identity)`, without boxing. */
  private def intListHash(xs: List[Int]): Int = {
    var h = mix(H.ListHash, xs.length)
    var rest = xs
    while (rest ne Nil) {
      h = mix(h, rest.head)
      rest = rest.tail
    }
    MurmurHash3.finalizeHash(h, 0)
  }

  /** `intListHash(xs :+ last)`. */
  private def intListHash(xs: List[Int], last: Int): Int = {
    var h = mix(H.ListHash, xs.length + 1)
    var rest = xs
    while (rest ne Nil) {
      h = mix(h, rest.head)
      rest = rest.tail
    }
    MurmurHash3.finalizeHash(mix(h, last), 0)
  }

  /**
   * Refinement classes met while hashing the current type or member. Name hashes include the
   * members of refinements reachable from a class's non-private members, as `NameHashing`'s
   * visitor does, so each memo entry remembers the refinements below it.
   */
  private[this] var structSink: List[Symbol] = Nil

  /** A memoised hash, computed in unit `unit`. */
  private final class TypeH(val hash: Int, val structs: List[Symbol], val unit: Int)

  private final class OwnerMemo[K <: AnyRef, V <: AnyRef] {
    private[this] val byOwner = new java.util.HashMap[Symbol, java.util.HashMap[K, V]]()
    def get(in: Symbol, k: K): V = {
      val inner = byOwner.get(in)
      if (inner eq null) null.asInstanceOf[V] else inner.get(k)
    }
    def put(in: Symbol, k: K, v: V): Unit = {
      var inner = byOwner.get(in)
      if (inner eq null) {
        inner = new java.util.HashMap[K, V]()
        byOwner.put(in, inner)
      }
      inner.put(k, v)
      ()
    }
    def clear(): Unit = byOwner.clear()
  }

  private[this] val plainTypeHashes = new java.util.HashMap[Type, TypeH]()
  private[this] val refinementTypeHashes = new OwnerMemo[Type, TypeH]
  private[this] val unitTypeHashes = new OwnerMemo[Type, TypeH]

  /** Whether a shared entry may be used here: always outside existentials, else if made here. */
  @inline private def visible(unit: Int, outside: Boolean): Boolean = outside || unit == unitId

  private def typeHash(in: Symbol, t: Type): Int = {
    val outside = existentialRenamings.isEmpty
    var th = unitTypeHashes.get(in, t)
    if ((th eq null) && outside) th = plainTypeHashes.get(t)
    if ((th eq null) && in.isRefinementClass) {
      th = refinementTypeHashes.get(in, t)
      if ((th ne null) && !visible(th.unit, outside)) th = null
    }
    if (th eq null) {
      val saved = structSink
      structSink = Nil
      th =
        try new TypeH(makeTypeHash(in, t), structSink, unitId)
        finally structSink = saved
      if (!outside) unitTypeHashes.put(in, t, th)
      else if (isPlain(t)) plainTypeHashes.put(t, th)
      else if (in.isRefinementClass) refinementTypeHashes.put(in, t, th)
      else unitTypeHashes.put(in, t, th)
    }
    if (th.structs ne Nil) structSink = th.structs ::: structSink
    th.hash
  }

  private def typesHash(in: Symbol, ts: List[Type]): Int = {
    var h = mix(H.ListHash, ts.length)
    var rest = ts
    while (rest ne Nil) {
      h = mix(h, typeHash(in, rest.head))
      rest = rest.tail
    }
    MurmurHash3.finalizeHash(h, 0)
  }

  /** A per-run memo of an `Int` per symbol, without a closure per lookup. */
  private final class SymbolIntMemo(f: Symbol => Int) {
    private[this] val memo = new java.util.HashMap[Symbol, Integer]()
    def apply(s: Symbol): Int = {
      val cached = memo.get(s)
      if (cached ne null) cached.intValue
      else {
        val h = f(s)
        memo.put(s, h)
        h
      }
    }
  }

  private[this] val nameHashes = new SymbolIntMemo(s => strHash(simpleName(s)))
  private def simpleNameHash(s: Symbol): Int = nameHashes(s)

  private[this] val thisPathHashes = new SymbolIntMemo(sym => {
    var h = H.ThisPathHash
    var s = sym
    while (!(s == NoSymbol || s.isRoot || s.isEmptyPackageClass || s.isRootPackage)) {
      h = mix(h, simpleNameHash(s))
      s = s.owner
    }
    MurmurHash3.finalizeHash(h, 0)
  })
  private def thisPathHash(sym: Symbol): Int = thisPathHashes(sym)

  private[this] val tparamIDHashes = new SymbolIntMemo(s => strHash(tparamID(s)))
  private def tparamIDHash(s: Symbol): Int =
    existentialRenamings.renaming(s) match {
      case Some(rename) => strHash(rename)
      case None         => tparamIDHashes(s)
    }

  private def projectionHash(in: Symbol, pre: Type, sym: Symbol): Int =
    if (pre == NoPrefix) {
      if (sym.isLocalClass || sym.isRoot || sym.isRootPackage) H.EmptyTypeHash
      else mix(H.ParameterRefHash, tparamIDHash(sym))
    } else if (sym.isRoot || sym.isRootPackage) H.EmptyTypeHash
    else mix(mix(H.ProjectionHash, simpleNameHash(sym)), typeHash(in, pre))

  private def makeTypeHash(in: Symbol, t: Type): Int = {
    val dealiased = t match {
      case TypeRef(_, sym, _) if sym.isAliasType => t.dealias
      case _                                     => t
    }
    dealiased match {
      case NoPrefix               => H.EmptyTypeHash
      case ThisType(sym)          => mix(H.SingletonHash, thisPathHash(sym))
      case SingleType(pre, sym)   => projectionHash(in, pre, sym)
      case ConstantType(constant) =>
        mix(mix(H.ConstantHash, strHash(constant.stringValue)), typeHash(in, constant.tpe))
      case TypeRef(pre, sym, Nil) if sym.isRefinementClass =>
        val unrolling = pre.memberInfo(sym)
        val withoutRecursiveRefs = new SuppressSymbolRef(sym).mapOver(unrolling)
        if (!buildTree && (unrolling ne withoutRecursiveRefs))
          reporter.warning(
            sym.pos,
            "sbt-api: approximated refinement ref" + t + " (== " + unrolling + ") to " +
              withoutRecursiveRefs +
              "\nThis is currently untested, please report the code you were compiling."
          )
        structureHash(withoutRecursiveRefs, sym)
      case tr @ TypeRef(pre, sym, args) =>
        val base = projectionHash(in, pre, sym)
        if (args.isEmpty)
          if (isRawType(tr)) typeHash(in, rawToExistential(tr))
          else base
        else mix(mix(H.ParameterizedHash, base), typesHash(in, args))
      case SuperType(_, _)   => H.EmptyTypeHash
      case at: AnnotatedType =>
        at.annotations match {
          case Nil    => typeHash(in, at.underlying)
          case annots =>
            mix(
              mix(H.AnnotatedHash, typeHash(in, at.underlying)),
              intListHash(annotationHashes(in, annots))
            )
        }
      case rt: CompoundType    => structureHash(rt, rt.typeSymbol)
      case et: ExistentialType =>
        val ExistentialType(typeVariables, qualified) = et
        existentialRenamings.enterExistentialTypeVariables(typeVariables)
        try {
          val tps = typeParamsHash(in, typeVariables)
          mix(mix(H.ExistentialHash, tps), typeHash(in, qualified))
        } finally existentialRenamings.leaveExistentialTypeVariables(typeVariables)
      case NoType                           => H.EmptyTypeHash
      case PolyType(typeParams, resultType) =>
        mix(mix(H.PolymorphicHash, typeParamsHash(in, typeParams)), typeHash(in, resultType))
      case _ => H.EmptyTypeHash
    }
  }

  private[this] val structureHashes = new java.util.HashMap[Symbol, TypeH]()
  private[this] val unitStructureHashes = new java.util.HashMap[Symbol, TypeH]()
  private[this] val structureInfos = new java.util.HashMap[Symbol, Type]()
  private[this] val structuresInProgress = collection.mutable.HashSet[Symbol]()

  /** A refinement (or other compound type) as `mkStructure` builds it: parents and decls. */
  private def structureHash(info: Type, s: Symbol): Int = {
    structSink = s :: structSink
    val outside = existentialRenamings.isEmpty
    var sh = unitStructureHashes.get(s)
    if (sh eq null) {
      sh = structureHashes.get(s)
      if ((sh ne null) && !visible(sh.unit, outside)) sh = null
    }
    if (sh ne null) sh.hash
    else if (!structuresInProgress.add(s)) H.StructurePendingHash
    else
      try {
        structureInfos.put(s, info)
        val parents = typesHash(s, info.parents)
        val declared = new Unordered
        structureDecls(info, s).foreach { m =>
          val d = defH(s, m)
          if ((d ne null) && d.nonPrivate) declared.add(d.hash)
        }
        val h = mix(mix(mix(H.StructureHash, parents), declared.result), (new Unordered).result)
        (if (outside) structureHashes else unitStructureHashes).put(s, new TypeH(h, Nil, unitId))
        h
      } finally {
        structuresInProgress -= s
        ()
      }
  }

  private def structureDecls(info: Type, s: Symbol): List[Symbol] = {
    val decls = info.decls.toList
    if (s.isModuleClass) removeConstructors(decls) else decls
  }

  private def annotationHashes(in: Symbol, as: List[AnnotationInfo]): List[Int] =
    if (in == NoSymbol) Nil
    else
      staticAnnotations(as).map { a =>
        val args =
          if (a.assocs.isEmpty)
            mix(
              mix(H.ListHash, strHash("")),
              strHash(printedArgs(a))
            )
          else
            listHash(a.assocs) { case (name, value) =>
              mix(strHash(name.toString), strHash(value.toString))
            }
        mix(typeHash(in, a.atp), args)
      }

  /** Mirrors `annotations(in, s)`, deduplicated the same way for fields and their accessors. */
  private def symAnnotationHashes(in: Symbol, s: Symbol): List[Int] = {
    val saved = phase
    phase = currentRun.typerPhase
    try {
      val base = if (s.hasFlag(Flags.ACCESSOR)) s.accessed else NoSymbol
      val b = if (base == NoSymbol) s else base
      if (b.hasGetter) {
        val getter = b.getterIn(b.enclClass)
        val setter = b.setterIn(b.enclClass)
        def none(sym: Symbol) = sym == NoSymbol || sym.annotations.isEmpty
        if (none(b) && none(getter) && none(setter)) return Nil
        val hs = collection.mutable.LinkedHashSet[Int]()
        def add(sym: Symbol) = if (sym != NoSymbol) hs ++= annotationHashes(in, sym.annotations)
        add(b)
        add(b.getterIn(b.enclClass))
        add(b.setterIn(b.enclClass))
        hs.toList
      } else if (b.annotations.isEmpty) Nil
      else annotationHashes(in, b.annotations)
    } finally phase = saved
  }

  /** The hash of `erasedSignature(transformedType(s))`, without building the string. */
  private[this] val erasedSignatureHashes =
    new SymbolIntMemo(s => mix(H.ErasedSignatureHash, erasedTypeHash(transformedType(s))))
  private def erasedSignatureHash(s: Symbol): Int = erasedSignatureHashes(s)

  private def erasedTypeHash(tp: Type): Int = tp match {
    case MethodType(params, res) =>
      mix(
        mix(H.ValueParamsHash, listHash(params)(p => erasedTypeHash(p.info))),
        erasedTypeHash(res)
      )
    case NullaryMethodType(res) => mix(H.ValueParamsHash, erasedTypeHash(res))
    case TypeRef(_, sym, arg :: Nil) if sym == definitions.ArrayClass =>
      mix(H.ParameterizedHash, erasedTypeHash(arg))
    case TypeRef(_, sym, _) => fullNameHash(sym)
    case _                  => fullNameHash(tp.typeSymbol)
  }

  private[this] val fullNameHashes = new SymbolIntMemo(s => strHash(s.fullName))
  private def fullNameHash(s: Symbol): Int = fullNameHashes(s)

  private def accessHash(a: xsbti.api.Access): Int = a match {
    case q: xsbti.api.Qualified =>
      val kind = q match {
        case _: xsbti.api.Protected => H.ProtectedHash
        case _                      => H.PrivateHash
      }
      val qual = q.qualifier match {
        case _: xsbti.api.Unqualified   => H.UnqualifiedHash
        case _: xsbti.api.ThisQualifier => H.ThisQualifierHash
        case id: xsbti.api.IdQualifier  => mix(H.IdQualifierHash, strHash(id.value))
        case _                          => H.UnqualifiedHash
      }
      mix(kind, qual)
    case _ => H.PublicHash
  }

  private def typeParamsHash(in: Symbol, tps: List[Symbol]): Int = {
    var h = mix(H.ListHash, tps.length)
    var rest = tps
    while (rest ne Nil) {
      h = mix(h, typeParamHash(in, rest.head))
      rest = rest.tail
    }
    MurmurHash3.finalizeHash(h, 0)
  }

  private def typeParamHash(in: Symbol, s: Symbol): Int = {
    val annots = intListHash(symAnnotationHashes(in, s))
    var h = tparamIDHash(s)
    val varianceInt = s.variance
    h = mix(h, if (varianceInt < 0) 0 else if (varianceInt > 0) 2 else 1)
    viewer(in).memberInfo(s) match {
      case TypeBounds(low, high) =>
        h = mix(h, typeParamsHash(in, s.typeParams))
        h = mix(h, typeHash(in, low))
        h = mix(h, typeHash(in, high))
      case PolyType(typeParams, base) =>
        h = mix(h, typeParamsHash(in, typeParams))
        h = mix(h, typeHash(in, base.bounds.lo))
        h = mix(h, typeHash(in, base.bounds.hi))
      case x => error("Unknown type parameter info: " + x.getClass)
    }
    mix(h, annots)
  }

  private def selfTypeHash(in: Symbol, s: Symbol): Int =
    if ((s.thisSym eq s) || (s.thisSym.tpeHK == s.tpeHK)) H.EmptyTypeHash
    else typeHash(in, s.typeOfThis)

  /**
   * A member as `definition` would extract it. `name` is its API name, `nonPrivate` whether
   * `HashAPI` and `NameHashing` count it, and `traitBreaker` whether it is one of the private
   * members of a trait that its implementors depend on.
   */
  private final class DefH(
      val name: String,
      val hash: Int,
      val isImplicit: Boolean,
      val isAbstract: Boolean,
      val nonPrivate: Boolean,
      val traitBreaker: Boolean,
      val isMacro: Boolean,
      val structs: List[Symbol],
      val unit: Int
  )

  private[this] val refinementDefHs = new OwnerMemo[Symbol, DefH]
  private[this] val unitDefHs = new OwnerMemo[Symbol, DefH]
  private[this] val NoDefH = new DefH("", 0, false, false, false, false, false, Nil, -1)

  /**
   * `null` when `definition(in, sym)` is `None`. Only members of refinements are memoised: a
   * class's members are hashed once, by `hashClass`. A member of a refinement is never a class,
   * so sharing it skips no registration in `mkDefH`.
   */
  private def defH(in: Symbol, sym: Symbol): DefH =
    if (!in.isRefinementClass) mkDefH(in, sym)
    else {
      val outside = existentialRenamings.isEmpty
      var d = unitDefHs.get(in, sym)
      if (d eq null) {
        d = refinementDefHs.get(in, sym)
        if ((d ne null) && (d ne NoDefH) && !visible(d.unit, outside)) d = null
      }
      if (d eq null) {
        d = mkDefH(in, sym)
        if (d eq null) d = NoDefH
        (if (outside) refinementDefHs else unitDefHs).put(in, sym, d)
      }
      if (d eq NoDefH) null else d
    }

  private def mkDefH(in: Symbol, sym: Symbol): DefH = {
    val saved = structSink
    structSink = Nil
    try {
      if (isClass(sym))
        if (ignoreClass(sym)) {
          allNonLocalClassSymbols += sym; null
        } else {
          classLike(in, sym)
          val cls = if (sym.isModule) sym.moduleClass else sym
          val body = mix(H.ClassDefHash, typeParamsHash(in, cls.typeParams))
          val isModule = cls.isModuleClass && !cls.isPackageObjectClass
          val annots = intListHash(symAnnotationHashes(in, sym))
          member(classNameAsSeenIn(in, sym), sym, annots, body, isModule)
        }
      else if (sym.isNonClassType) typeDefH(in, sym)
      else if (sym.isVariable)
        if (isSourceField(sym)) fieldH(in, sym, keepConst = false) else null
      else if (sym.isStable)
        if (isSourceField(sym)) fieldH(in, sym, keepConst = true) else null
      else if (sym.isSourceMethod && !sym.isSetter)
        if (sym.isGetter) fieldH(in, sym, keepConst = false) else defDefH(in, sym)
      else null
    } finally structSink = saved
  }

  private def member(
      name: String,
      s: Symbol,
      annotsHash: Int,
      body: Int,
      traitBreaker: Boolean
  ): DefH = {
    val mods = getModifiers(s)
    val acc = getAccess(s)
    var h = strHash(name)
    h = mix(h, annotsHash)
    h = mix(h, mods.raw.toInt)
    h = mix(h, accessHash(acc))
    h = mix(h, body)
    val nonPrivate = acc match {
      case p: xsbti.api.Private => p.qualifier.isInstanceOf[xsbti.api.IdQualifier]
      case _                    => true
    }
    val isPrivate = acc.isInstanceOf[xsbti.api.Private]
    new DefH(
      name,
      MurmurHash3.finalizeHash(h, 0),
      mods.isImplicit,
      mods.isAbstract,
      nonPrivate,
      isPrivate && (traitBreaker || mods.isSuperAccessor),
      mods.isMacro,
      structSink,
      unitId
    )
  }

  private def typeDefH(in: Symbol, s: Symbol): DefH = {
    val (tps, tpe) = viewer(in).memberInfo(s) match {
      case PolyType(typeParams0, base) => (typeParamsHash(in, typeParams0), base)
      case t                           => (typeParamsHash(in, Nil), t)
    }
    val body =
      if (s.isAliasType) mix(mix(H.TypeAliasHash, tps), typeHash(in, tpe))
      else if (s.isAbstractType) {
        val bounds = tpe.bounds
        mix(mix(mix(H.TypeDeclHash, tps), typeHash(in, bounds.lo)), typeHash(in, bounds.hi))
      } else error("Unknown type member" + s)
    member(simpleName(s), s, intListHash(symAnnotationHashes(in, s)), body, traitBreaker = false)
  }

  private def fieldH(in: Symbol, s: Symbol, keepConst: Boolean): DefH = {
    val t = dropNullary(viewer(in).memberType(s))
    val t2 = if (keepConst) t else dropConst(t)
    val body = mix(if (keepConst) H.ValHash else H.VarHash, typeHash(in, t2))
    val annots = intListHash(symAnnotationHashes(in, s), erasedSignatureHash(s))
    member(simpleName(s), s, annots, body, traitBreaker = true)
  }

  private def defDefH(in: Symbol, s: Symbol): DefH = {
    def paramHash(p: Symbol): Int = {
      val tp = p.info
      val ts = tp.typeSymbol
      val special =
        if (ts == definitions.RepeatedParamClass) 1
        else if (ts == definitions.ByNameParamClass) 2
        else 0
      val t = if (special == 0) tp else tp.typeArgs.head
      var h = simpleNameHash(p)
      h = mix(h, typeHash(in, t))
      h = mix(h, special)
      mix(h, boolHash(hasDefault(p)))
    }
    def paramsHash(params: List[Symbol]): Int = {
      var h = mix(H.ListHash, params.length)
      var rest = params
      while (rest ne Nil) {
        h = mix(h, paramHash(rest.head))
        rest = rest.tail
      }
      MurmurHash3.finalizeHash(h, 0)
    }
    @tailrec def countLists(t: Type, n: Int): Int = t match {
      case PolyType(_, base)             => countLists(base, 0)
      case MethodType(_, resultType)     => countLists(resultType, n + 1)
      case NullaryMethodType(resultType) => countLists(resultType, n)
      case _                             => n
    }
    // `vls` folds the value parameter lists as `listHash` would, so needs their number up front.
    @tailrec def loop(t: Type, tps: Int, vls: Int): Int = t match {
      case PolyType(typeParams0, base) =>
        loop(base, typeParamsHash(in, typeParams0), mix(H.ListHash, countLists(base, 0)))
      case MethodType(params, resultType) =>
        val isImplicitList = cond(params) { case head :: _ => isImplicit(head) }
        val vl = mix(mix(H.ValueParamsHash, boolHash(isImplicitList)), paramsHash(params))
        loop(resultType, tps, mix(vls, vl))
      case NullaryMethodType(resultType) => loop(resultType, tps, vls)
      case returnType                    =>
        val ret = typeHash(in, dropConst(returnType))
        mix(mix(mix(H.DefHash, tps), MurmurHash3.finalizeHash(vls, 0)), ret)
    }
    val info = viewer(in).memberInfo(s)
    val body = loop(info, typeParamsHash(in, Nil), mix(H.ListHash, countLists(info, 0)))
    val annots = intListHash(symAnnotationHashes(in, s), erasedSignatureHash(s))
    member(simpleNameForMethod(s), s, annots, body, traitBreaker = false)
  }

  /** A typeless stub, as `stub` builds it. */
  private def stubH(m: Symbol): Option[DefH] = {
    var h = stubHs.get(m)
    if (h eq null) {
      h = stub(m).map { d =>
        val saved = structSink
        structSink = Nil
        try member(d.name, m, intListHash(Nil), stubBodyHash, traitBreaker = false)
        finally structSink = saved
      }
      stubHs.put(m, h)
    }
    h
  }
  private[this] val stubHs = new java.util.HashMap[Symbol, Option[DefH]]()

  private[this] lazy val stubBodyHash =
    mix(
      mix(mix(H.DefHash, typeParamsHash(NoSymbol, Nil)), intListHash(Nil)),
      H.EmptyTypeHash
    )

  /** The members of a class's API, as `mkStructureWithInherited` selects them. */
  private final class Members(info: Type, sym: Symbol) {
    val decls: List[Symbol] = info.decls.toList
    val declared: List[Symbol] =
      sort((if (sym.isModuleClass) removeConstructors(decls) else decls).toArray).toList
    private val (inherited0, platform) =
      ancestorDecls(info).partition(m => !isStubbedOwner(m.owner) || discoveryReads(m))
    val inherited: List[Symbol] = sort(inherited0.toArray).toList
    val stubbed: List[Symbol] = platform
    def ancestorTypes: List[Type] = {
      val ancestorTypes0 = linearizedAncestorTypes(info)
      if (sym.isDerivedValueClass) sym.derivedValueClassUnbox.tpe.finalResultType :: ancestorTypes0
      else ancestorTypes0
    }
  }

  private def addDefHs(
      in: Symbol,
      syms: List[Symbol],
      b: collection.mutable.ListBuffer[DefH]
  ): Unit = {
    var rest = syms
    while (rest ne Nil) {
      val d = defH(in, rest.head)
      if (d ne null) b += d
      rest = rest.tail
    }
  }

  private def localName(name: String): String = name.substring(name.lastIndexOf('.') + 1)

  private def hashClass(p: PendingClass): Extracted = {
    val sym = p.sym
    val in = p.in
    val members = new Members(p.info, sym)
    val ancestorTypes = members.ancestorTypes
    val isTrait = p.defType == DefinitionType.Trait
    val isModule = p.defType == DefinitionType.Module || p.defType == DefinitionType.PackageModule

    val saved = structSink
    structSink = Nil
    val tparamsH = typeParamsHash(in, sym.typeParams)
    val selfH = selfTypeHash(in, sym)
    val parentsH = typesHash(sym, ancestorTypes)
    val headerStructs = structSink
    val sealedH = {
      val u = new Unordered
      sym.sealedDescendants.foreach(c => u.add(typeHash(c, c.tpe)))
      u.result
    }
    structSink = saved

    val declared = {
      val b = new collection.mutable.ListBuffer[DefH]
      addDefHs(sym, members.declared, b)
      b.toList
    }
    val inherited = {
      val b = new collection.mutable.ListBuffer[DefH]
      addDefHs(sym, members.inherited, b)
      var rest = members.stubbed
      while (rest ne Nil) {
        stubH(rest.head) match {
          case Some(d) => b += d
          case None    =>
        }
        rest = rest.tail
      }
      b.toList
    }

    def unordered(ds: List[DefH]): Int = {
      val u = new Unordered
      ds.foreach(d => u.add(d.hash))
      u.result
    }
    val declaredH = unordered(declared.filter(_.nonPrivate))
    val inheritedH = unordered(inherited.filter(_.nonPrivate))
    def classHash(withSealed: Boolean, structure: Int): Int = {
      var h = mix(H.ClassHash, tparamsH)
      h = mix(h, selfH)
      if (withSealed) h = mix(h, sealedH)
      if (isTrait) h = mix(h, H.TraitHash)
      MurmurHash3.finalizeHash(mix(h, structure), 0)
    }
    def structureHash(declaredH: Int): Int =
      mix(mix(mix(H.StructureHash, parentsH), declaredH), inheritedH)
    val apiHash = classHash(withSealed = true, structureHash(declaredH))
    val extraHash =
      if (!isTrait) apiHash
      else {
        val breakers = declared.filter(_.traitBreaker)
        if (breakers.isEmpty) apiHash
        else
          classHash(
            withSealed = true,
            structureHash(unordered(declared.filter(_.nonPrivate) ++ breakers))
          )
      }

    val nameHashes = {
      import xsbti.UseScope
      val location = mix(strHash(p.name), boolHash(isModule))
      val groups = Array.fill(3)(new java.util.HashMap[String, Unordered]())
      val scopes = Array(UseScope.Default, UseScope.Implicit, UseScope.PatMatTarget)
      def add(name: String, scope: UseScope, hash: Int): Unit = {
        val group = groups(scopes.indexOf(scope))
        val key = localName(name)
        var u = group.get(key)
        if (u eq null) {
          u = new Unordered
          group.put(key, u)
        }
        u.add(mix(hash, location))
      }
      def scopeOf(isImplicit: Boolean) = if (isImplicit) UseScope.Implicit else UseScope.Default
      def header(withSealed: Boolean): Int = {
        var h = strHash(p.name)
        h = mix(h, intListHash(symAnnotationHashes(in, p.c)))
        h = mix(h, p.modifiers.raw.toInt)
        h = mix(h, accessHash(p.acc))
        mix(h, classHash(withSealed, mix(H.StructureHash, parentsH)))
      }
      add(p.name, scopeOf(p.modifiers.isImplicit), header(withSealed = !optimizedSealed))
      if (optimizedSealed && p.modifiers.isSealed)
        add(p.name, UseScope.PatMatTarget, header(withSealed = true))
      val seen = collection.mutable.HashSet[Symbol]()
      var work: List[Symbol] = headerStructs
      def addDef(d: DefH): Unit =
        if (d.nonPrivate) {
          add(d.name, scopeOf(d.isImplicit), d.hash)
          if (d.structs ne Nil) work = d.structs ::: work
        }
      declared.foreach(addDef)
      inherited.foreach(addDef)
      while (work ne Nil) {
        val s = work.head
        work = work.tail
        if (seen.add(s)) Option(structureInfos.get(s)).foreach { info =>
          val saved = structSink
          structSink = Nil
          typesHash(s, info.parents)
          work = structSink ::: work
          structSink = saved
          structureDecls(info, s).foreach { m =>
            val d = defH(s, m)
            if (d ne null) addDef(d)
          }
        }
      }
      val result = new Array[xsbti.api.NameHash](groups.map(_.size).sum)
      var i = 0
      for (g <- 0 until 3) {
        val it = groups(g).entrySet.iterator
        while (it.hasNext) {
          val e = it.next()
          result(i) = xsbti.api.NameHash.of(e.getKey, scopes(g), e.getValue.result)
          i += 1
        }
      }
      result
    }

    val hasMacro = p.modifiers.isMacro || declared.exists(_.isMacro)
    val hashes = new xsbti.ClassHashes(apiHash, extraHash, nameHashes, hasMacro)
    new Extracted(
      fullClasses.getOrElse((p.name, isModule), null),
      thinClass(p, members, isModule),
      hashes
    )
  }

  /** What `APIUtil.minimizeWithStubs` keeps of the class `mkClassLike` builds. */
  private def thinClass(p: PendingClass, members: Members, isModule: Boolean): ClassLike = {
    val sym = p.sym
    val parents = types(sym, members.ancestorTypes)
    def isMainCandidate(d: Symbol) =
      isModule && d.isSourceMethod && !d.isSetter && !d.isGetter && d.name == nme.main
    def mainOrStub(d: Symbol): Either[xsbti.api.ClassDefinition, xsbti.api.ClassDefinition] =
      if (isMainCandidate(d)) {
        val full = defDef(sym, d)
        if (ExtractAPI.isMainMethod(full)) Left(full) else Right(stubOf(sym, d))
      } else Right(stubOf(sym, d))
    val declaredKept = members.declared.filter(hasDefinition).map(mainOrStub)
    val declared =
      (declaredKept.collect { case Left(d) => d } ++ declaredKept.collect { case Right(d) => d })
        .toArray[xsbti.api.ClassDefinition]
    val inheritedKept = members.inherited.filter(hasDefinition)
    val inheritedMains = inheritedKept.filter(isMainCandidate).map(defDef(sym, _)).filter(
      ExtractAPI.isMainMethod
    )
    val abstractInherited = {
      val b = new collection.mutable.ListBuffer[xsbti.api.ClassDefinition]
      inheritedKept.foreach(d => if (isAbstractMember(d)) b += stubOf(sym, d))
      var rest = members.stubbed
      while (rest ne Nil) {
        stub(rest.head) match {
          case Some(d) if d.modifiers.isAbstract => b += d
          case _                                 =>
        }
        rest = rest.tail
      }
      b.toList
    }
    val inherited = (inheritedMains ++ abstractInherited).toArray[xsbti.api.ClassDefinition]
    val savedAnnotations = {
      val names = new java.util.LinkedHashSet[String]()
      def addAnnotations(d: Symbol): Unit =
        if (d.isSourceMethod && !d.isSetter && !d.isGetter && d.isPublic && hasDefinition(d)) {
          val as = enteringPhase(currentRun.typerPhase)(d.annotations)
          if (as.nonEmpty) staticAnnotations(as).foreach { a =>
            annotationName(sym, a.atp).foreach(names.add)
          }
        }
      members.declared.foreach(addAnnotations)
      members.inherited.foreach(addAnnotations)
      names.toArray(new Array[String](names.size))
    }
    xsbti.api.ClassLike.of(
      p.name,
      p.acc,
      p.modifiers,
      p.anns,
      p.defType,
      p.selfType,
      xsbti.api.SafeLazy.strict(
        xsbti.api.Structure.of(
          xsbti.api.SafeLazy.strict(parents),
          xsbti.api.SafeLazy.strict(declared),
          xsbti.api.SafeLazy.strict(inherited)
        )
      ),
      savedAnnotations,
      p.childrenOfSealedClass,
      p.topLevel,
      p.tParams
    )
  }

  private[this] val annotationNameCache = new java.util.HashMap[Type, Option[String]]()

  /** `Discovery.simpleName` of the annotation type `atp`, as `mkAnnotations` would render it. */
  private def annotationName(in: Symbol, atp: Type): Option[String] = {
    var n = annotationNameCache.get(atp)
    if (n eq null) {
      n = ExtractAPI.simpleName(processType(in, atp))
      annotationNameCache.put(atp, n)
    }
    n
  }

  private def isAbstractMember(s: Symbol): Boolean =
    s.hasFlag(Flags.ABSTRACT) || s.hasFlag(Flags.DEFERRED) || s.hasFlag(Flags.ABSOVERRIDE)

  /** Whether `definition(in, sym)` is defined, without its side effects. */
  private def hasDefinition(sym: Symbol): Boolean =
    if (isClass(sym)) !ignoreClass(sym)
    else if (sym.isNonClassType) true
    else if (sym.isVariable || sym.isStable) isSourceField(sym)
    else sym.isSourceMethod && !sym.isSetter

  /**
   * A stub of the member `definition(in, s)` extracts, as `APIUtil.stubDefinition` makes it,
   * which drops the erased-signature witness: it only feeds the hash.
   */
  private def stubOf(in: Symbol, s: Symbol): xsbti.api.ClassDefinition = {
    val name =
      if (isClass(s)) classNameAsSeenIn(in, s)
      else if (s.isNonClassType || s.isVariable || s.isStable || s.isGetter) simpleName(s)
      else simpleNameForMethod(s)
    xsbti.api.Def.of(
      name,
      getAccess(s),
      getModifiers(s),
      annotations(in, s),
      Array.empty,
      Array.empty,
      Constants.emptyType
    )
  }

  private def classLike(in: Symbol, c: Symbol): ClassLikeDef =
    classLikeCache.getOrElseUpdate((in, c), mkClassLike(in, c))
  private def mkClassLike(in: Symbol, c: Symbol): ClassLikeDef = {
    // Normalize to a class symbol, and initialize it.
    // (An object -- aka module -- also has a term symbol,
    //  but it's the module class that holds the info about its structure.)
    val sym = (if (c.isModule) c.moduleClass else c).initialize
    val defType =
      if (sym.isTrait) DefinitionType.Trait
      else if (sym.isModuleClass) {
        if (sym.isPackageObjectClass) DefinitionType.PackageModule
        else DefinitionType.Module
      } else DefinitionType.ClassDef
    val childrenOfSealedClass = sort(sym.sealedDescendants.toArray).map(c => processType(c, c.tpe))
    val topLevel = sym.owner.isPackageClass
    val anns = annotations(in, c)
    val modifiers = getModifiers(c)
    val acc = getAccess(c)
    val name = classNameAsSeenIn(in, c)
    val tParams = typeParameters(in, sym) // look at class symbol
    val selfType = lzy(this.selfType(in, sym))
    val info = viewer(in).memberInfo(sym)
    if (buildTree) {
      val structure = lzy(structureWithInherited(info, sym))
      val classWithMembers = xsbti.api.ClassLike.of(
        name,
        acc,
        modifiers,
        anns,
        defType,
        selfType,
        structure,
        emptyStringArray,
        childrenOfSealedClass,
        topLevel,
        tParams
      ) // use original symbol (which is a term symbol when `c.isModule`) for `name` and other non-classy stuff
      allNonLocalClassesInSrc += classWithMembers
      fullClasses((name, isModuleDefType(defType))) = classWithMembers
    }
    if (buildHashes)
      pendingHashes += new PendingClass(
        in,
        c,
        sym,
        info,
        name,
        acc,
        modifiers,
        anns,
        defType,
        selfType,
        childrenOfSealedClass,
        topLevel,
        tParams
      )
    allNonLocalClassSymbols += sym

    if (isJava25Plus) {
      if (hasJava25MainMethod(sym)) {
        _mainClasses += name
      }
    } else if (
      sym.isStatic && defType == DefinitionType.Module && definitions.hasJavaMainMethod(sym)
    ) {
      _mainClasses += name
    }

    val classDef = xsbti.api.ClassLikeDef.of(
      name,
      acc,
      modifiers,
      anns,
      tParams,
      defType
    ) // use original symbol (which is a term symbol when `c.isModule`) for `name` and other non-classy stuff
    classDef
  }

  private[this] def hasJava25MainMethod(sym: Symbol): Boolean =
    !sym.isAbstract && sym.tpe.member(nme.main).alternatives.exists(isJava25MainMethod)

  private[this] def isJava25MainMethod(sym: Symbol): Boolean = (sym.name == nme.main) &&
    (sym.info match {
      case MethodType(Nil, restpe)      => restpe.typeSymbol == definitions.UnitClass
      case MethodType(p :: Nil, restpe) =>
        definitions.isArrayOfSymbol(p.tpe, definitions.StringClass) &&
        restpe
          .typeSymbol == definitions.UnitClass
      case _ => false
    })

  // TODO: could we restrict ourselves to classes, ignoring the term symbol for modules,
  // since everything we need to track about a module is in the module's class (`moduleSym.moduleClass`)?
  private[this] def isClass(s: Symbol) = s.isClass || s.isModule
  // necessary to ensure a stable ordering of classes in the definitions list:
  //  modules and classes come first and are sorted by name
  // all other definitions come later and are not sorted
  private[this] val sortClasses = new Comparator[Symbol] {
    def compare(a: Symbol, b: Symbol) = {
      val aIsClass = isClass(a)
      val bIsClass = isClass(b)
      if (aIsClass == bIsClass)
        if (aIsClass)
          if (a.isModule == b.isModule)
            a.fullName.compareTo(b.fullName)
          else if (a.isModule)
            -1
          else
            1
        else
          0 // substantial performance hit if fullNames are compared here
      else if (aIsClass)
        -1
      else
        1
    }
  }
  private object Constants {
    val local = xsbti.api.ThisQualifier.of()
    val public = xsbti.api.Public.of()
    val privateLocal = xsbti.api.Private.of(local)
    val protectedLocal = xsbti.api.Protected.of(local)
    val unqualified = xsbti.api.Unqualified.of()
    val emptyPath = xsbti.api.Path.of(Array())
    val thisPath = xsbti.api.This.of()
    val emptyType = xsbti.api.EmptyType.of()
  }

  private def simpleName(s: Symbol): String = {
    s.unexpandedName.decode.trim
  }

  private[this] val methodNameCache = new java.util.HashMap[Symbol, String]()
  private def simpleNameForMethod(s: Symbol): String = {
    var n = methodNameCache.get(s)
    if (n eq null) {
      n = simpleNameForMethod0(s)
      methodNameCache.put(s, n)
    }
    n
  }
  private def simpleNameForMethod0(s: Symbol): String = {
    val name = s.unexpandedName
    val untrimmedName = if (name == nme.CONSTRUCTOR)
      constructorNameAsString(s.enclClass)
    else {
      val decoded = name.decode
      if (!decoded.startsWith("<init>$default$")) decoded
      else
        decoded match {
          case ConstructorWithDefaultArgument(index) => constructorNameAsString(s.enclClass, index)
          case _                                     => decoded
        }
    }
    untrimmedName.trim
  }

  private def staticAnnotations(annotations: List[AnnotationInfo]): List[AnnotationInfo] =
    if (annotations == Nil) Nil
    else {
      // `isStub` for scala/bug#11679: annotations of inherited members may be absent from the compile time
      // classpath so avoid calling `isNonBottomSubClass` on these stub symbols which would trigger an error.
      //
      // `initialize` for sbt/zinc#998: 2.13 identifies Java annotations by flags. Up to 2.13.6, this is done
      // without forcing the info of `ann.atp.typeSymbol`, flags are missing it's still a `ClassfileLoader`.
      annotations.filter(ann =>
        !isStub(ann.atp.typeSymbol) && { ann.atp.typeSymbol.initialize; ann.isStatic }
      )
    }

  private def isStub(sym: Symbol): Boolean = sym match {
    case _: StubSymbol => true
    case _             => false
  }
}

object ExtractAPI {
  private val emptyAnnotationArray = new Array[xsbti.api.Annotation](0)
  private val erasedSignatureMarker: xsbti.api.Type =
    xsbti.api.Singleton.of(xsbti.api.Path.of(Array(xsbti.api.Id.of("<erased-signature>"))))
  private val ConstructorWithDefaultArgument = "<init>\\$default\\$(\\d+)".r

  /** `Discovery.isMainMethod`, which the bridge cannot depend on. */
  def isMainMethod(d: xsbti.api.Definition): Boolean = d match {
    case d: xsbti.api.Def =>
      d.name == "main" && d.access.isInstanceOf[xsbti.api.Public] && !d.modifiers.isAbstract &&
      simpleName(d.returnType) == Some("scala.Unit") &&
      d.valueParameters.length == 1 && d.valueParameters()(0).parameters.length == 1 && {
        val p = d.valueParameters()(0).parameters()(0)
        (p.modifier == xsbti.api.ParameterModifier.Plain ||
          p.modifier == xsbti.api.ParameterModifier.Repeated) &&
        (p.tpe match {
          case pt: xsbti.api.Parameterized =>
            simpleName(pt.baseType) == Some("scala.Array") && pt.typeArguments.length == 1 &&
            simpleName(pt.typeArguments()(0)) == Some("java.lang.String")
          case _ => false
        })
      }
    case _ => false
  }

  /** `Discovery.simpleName`. */
  @tailrec def simpleName(t: xsbti.api.Type): Option[String] = t match {
    case a: xsbti.api.Annotated  => simpleName(a.baseType)
    case p: xsbti.api.Projection =>
      p.prefix match {
        case s: xsbti.api.Singleton =>
          val cs = s.path.components
          cs.last match {
            case _: xsbti.api.This =>
              val ids = cs.init.collect { case i: xsbti.api.Id => i.id }
              if (ids.length == cs.length - 1) Some((ids :+ p.id).mkString(".")) else None
            case _ => None
          }
        case _: xsbti.api.EmptyType => Some(p.id)
        case _                      => None
      }
    case _ => None
  }
}
