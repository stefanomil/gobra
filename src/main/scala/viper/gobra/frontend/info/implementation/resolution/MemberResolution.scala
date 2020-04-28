package viper.gobra.frontend.info.implementation.resolution

import java.io.File

import viper.gobra.ast.frontend._
import viper.gobra.frontend.Parser
import viper.gobra.frontend.info.{ExternalTypeInfo, Info}
import viper.gobra.frontend.info.base.SymbolTable._
import viper.gobra.frontend.info.base.Type._
import viper.gobra.frontend.info.implementation.TypeInfoImpl


trait MemberResolution { this: TypeInfoImpl =>

  import scala.collection.breakOut

  private def createField(decl: PFieldDecl): Field =
    defEntity(decl.id).asInstanceOf[Field]

  private def createEmbbed(decl: PEmbeddedDecl): Embbed =
    defEntity(decl.id).asInstanceOf[Embbed]

  private def createMethodImpl(decl: PMethodDecl): MethodImpl =
    defEntity(decl.id).asInstanceOf[MethodImpl]

  private def createMethodSpec(spec: PMethodSig): MethodSpec =
    defEntity(spec.id).asInstanceOf[MethodSpec]

  private def createMPredImpl(decl: PMPredicateDecl): MPredicateImpl =
    defEntity(decl.id).asInstanceOf[MPredicateImpl]

  private def createMPredSpec(spec: PMPredicateSig): MPredicateSpec =
    defEntity(spec.id).asInstanceOf[MPredicateSpec]

  private lazy val receiverMethodSetMap: Map[Type, AdvancedMemberSet[MethodLike]] = {
    tree.root.declarations
      .collect { case m: PMethodDecl => createMethodImpl(m) }(breakOut)
      .groupBy { m: MethodImpl => miscType(m.decl.receiver) }
      .mapValues(ms => AdvancedMemberSet.init(ms))
  }

  def receiverMethodSet(recv: Type): AdvancedMemberSet[MethodLike] =
    receiverMethodSetMap.getOrElse(recv, AdvancedMemberSet.empty)

  private lazy val receiverPredicateSetMap: Map[Type, AdvancedMemberSet[MethodLike]] = {
    tree.root.declarations
      .collect { case m: PMPredicateDecl => createMPredImpl(m) }(breakOut)
      .groupBy { m: MPredicateImpl => miscType(m.decl.receiver) }
      .mapValues(ms => AdvancedMemberSet.init(ms))
  }

  def receiverPredicateSet(recv: Type): AdvancedMemberSet[MethodLike] =
    receiverPredicateSetMap.getOrElse(recv, AdvancedMemberSet.empty)

  lazy val receiverSet: Type => AdvancedMemberSet[MethodLike] =
    attr[Type, AdvancedMemberSet[MethodLike]] (t => receiverMethodSet(t) union receiverPredicateSet(t))

  lazy val interfaceMethodSet: InterfaceT => AdvancedMemberSet[MethodLike] =
    attr[InterfaceT, AdvancedMemberSet[MethodLike]] {
      case InterfaceT(PInterfaceType(es, methSpecs, predSpecs)) =>
        AdvancedMemberSet.init[MethodLike](methSpecs.map(m => createMethodSpec(m))) union
          AdvancedMemberSet.init[MethodLike](predSpecs.map(m => createMPredSpec(m))) union
          AdvancedMemberSet.union {
            es.map(e => interfaceMethodSet(
              entity(e.typ.id) match {
                case NamedType(PTypeDef(t: PInterfaceType, _), _, _) => InterfaceT(t)
              }
            ))
          }
    }


  private def pastPromotions[M <: TypeMember](cont: Type => AdvancedMemberSet[M]): Type => AdvancedMemberSet[M] = {

    def go(pastDeref: Boolean): Type => AdvancedMemberSet[M] = attr[Type, AdvancedMemberSet[M]] {

      case DeclaredT(decl) => go(pastDeref)(typeType(decl.right)).surface
      case PointerT(t) if !pastDeref => go(pastDeref = true)(t).ref

      case StructT(t) =>
        AdvancedMemberSet.union(t.embedded map { e =>
          val et = miscType(e.typ)
          (cont(et) union go(pastDeref = false)(et)).promote(createEmbbed(e))
        })

      case _ => AdvancedMemberSet.empty
    }

    go(pastDeref = false)
  }

  private val fieldSuffix: Type => AdvancedMemberSet[StructMember] = {

    def go(pastDeref: Boolean): Type => AdvancedMemberSet[StructMember] = attr[Type, AdvancedMemberSet[StructMember]] {

      case DeclaredT(decl) => go(pastDeref)(typeType(decl.right)).surface
      case PointerT(t) if !pastDeref => go(pastDeref = true)(t).ref

      case StructT(t) =>
        val (es, fs) = (t.embedded, t.fields)
        AdvancedMemberSet.init[StructMember](fs map createField) union AdvancedMemberSet.init(es map createEmbbed)

      case _ => AdvancedMemberSet.empty
    }

    go(pastDeref = false)
  }

  val structMemberSet: Type => AdvancedMemberSet[StructMember] =
    attr[Type, AdvancedMemberSet[StructMember]] { t => fieldSuffix(t) union pastPromotions(fieldSuffix)(t) }

  private val pastPromotionsMethodSuffix: Type => AdvancedMemberSet[MethodLike] =
    attr[Type, AdvancedMemberSet[MethodLike]] {
      case t: InterfaceT => interfaceMethodSet(t)
      case pt@ PointerT(t) => receiverSet(pt) union receiverSet(t).ref
      case t => receiverSet(t) union receiverSet(PointerT(t)).deref
    }

  val nonAddressableMethodSet: Type => AdvancedMemberSet[MethodLike] =
    attr[Type, AdvancedMemberSet[MethodLike]] { t =>
      pastPromotions(pastPromotionsMethodSuffix)(t) union (t match {
        case pt@ PointerT(st) => receiverSet(pt) union receiverSet(st).ref
        case _ => receiverSet(t)
      })
    }

  val addressableMethodSet: Type => AdvancedMemberSet[MethodLike] =
    attr[Type, AdvancedMemberSet[MethodLike]] { t =>
      pastPromotions(pastPromotionsMethodSuffix)(t) union (t match {
        case pt@ PointerT(st) => receiverSet(pt) union receiverSet(st).ref
        case _ => receiverSet(t) union receiverSet(PointerT(t)).deref
      })
    }




  def tryFieldLookup(t: Type, id: PIdnUse): Option[(StructMember, Vector[MemberPath])] =
    structMemberSet(t).lookupWithPath(id.name)

  def tryMethodLikeLookup(e: PExpression, id: PIdnUse): Option[(MethodLike, Vector[MemberPath])] = {
    if (effAddressable(e)) addressableMethodSet(exprType(e)).lookupWithPath(id.name)
    else nonAddressableMethodSet(exprType(e)).lookupWithPath(id.name)
  }

  def tryMethodLikeLookup(e: Type, id: PIdnUse): Option[(MethodLike, Vector[MemberPath])] = {
    nonAddressableMethodSet(e).lookupWithPath(id.name)
  }

  def tryMethodLikeLookup(e: PType, id: PIdnUse): Option[(MethodLike, Vector[MemberPath])] = tryMethodLikeLookup(typeType(e), id)

  def tryPackageLookup(importedPkg: ImportT, id: PIdnUse): Option[(Regular, Vector[MemberPath])] = {
    def getTypeChecker(importedPkg: ImportT): Option[ExternalTypeInfo] =
      // check if package was already parsed:
      context.getTypeInfo(importedPkg.decl.pkg).map(Some(_)).getOrElse {
        // TODO get files belonging to package
        val pkgFile = new File("src/test/resources/regressions/features/import/simple_example/bar.go")
        (for {
          // TODO parse only decls and specs
          parsedProgram <- Parser.parse(pkgFile)(config)
          // TODO maybe don't check whole file but only members that are actually used/imported
          typeChecker <- Info.check(parsedProgram, context)(config)
          // store typeChecker for reuse:
          _ = context.addPackage(typeChecker)
        } yield Some(typeChecker)).getOrElse(None)
      }


    val foreignPkgResult = for {
      typeChecker <- getTypeChecker(importedPkg)
      entity <- typeChecker.externalRegular(id)
    } yield entity
    foreignPkgResult.flatMap(m => Some((m, Vector())))
  }


  def tryDotLookup(b: PExpressionOrType, id: PIdnUse): Option[(Regular, Vector[MemberPath])] = {
    exprOrType(b) match {
      case Left(expr) =>
        val methodLikeAttempt = tryMethodLikeLookup(expr, id)
        if (methodLikeAttempt.isDefined) methodLikeAttempt
        else tryFieldLookup(exprType(expr), id)

      case Right(typ) => typeType(typ) match {
        case pkg: ImportT => tryPackageLookup(pkg, id)
        case _ => tryMethodLikeLookup(typ, id)
      }
    }
  }





  def findField(t: Type, id: PIdnUse): Option[StructMember] =
    structMemberSet(t).lookup(id.name)


}
