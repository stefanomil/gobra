package viper.gobra.frontend.info

import org.bitbucket.inkytonik.kiama.relation.Tree
import viper.gobra.ast.frontend.PNode.PPkg
import viper.gobra.ast.frontend.{PNode, PProgram}
import viper.gobra.frontend.Config
import viper.gobra.frontend.info.implementation.TypeInfoImpl
import viper.gobra.frontend.info.implementation.typing.ghost.separation.GhostLessPrinter
import viper.gobra.reporting.{TypeCheckDebugMessage, TypeCheckFailureMessage, TypeCheckSuccessMessage, TypeError, VerifierError}

import scala.collection.immutable.ListMap

object Info {
  type GoTree = Tree[PNode, PProgram]

  class Context {
    private var contextMap: Map[PPkg, ExternalTypeInfo] = ListMap[PPkg, ExternalTypeInfo]()

    def addPackage(typeInfo: ExternalTypeInfo): Unit =
      contextMap = contextMap + (typeInfo.pkgName.name -> typeInfo)

    def getTypeInfo(pkg: PPkg): Option[ExternalTypeInfo] = contextMap.get(pkg)

    def getContexts: Iterable[ExternalTypeInfo] = contextMap.values
  }

  def check(program: PProgram, context: Context = new Context)(config: Config): Either[Vector[VerifierError], TypeInfo with ExternalTypeInfo] = {
    val tree = new GoTree(program)
    //    println(program.declarations.head)
    //    println("-------------------")
    //    println(tree)
    val info = new TypeInfoImpl(tree, context)(config: Config)

    val errors = info.errors
    config.reporter report TypeCheckDebugMessage(config.inputFile, () => program, () => getDebugInfo(program, info))
    if (errors.isEmpty) {
      config.reporter report TypeCheckSuccessMessage(config.inputFile, () => program, () => getErasedGhostCode(program, info))
      Right(info)
    } else {
      val typeErrors = program.positions.translate(errors, TypeError)
      config.reporter report TypeCheckFailureMessage(config.inputFile, () => program, typeErrors)
      Left(typeErrors)
    }
  }

  private def getErasedGhostCode(program: PProgram, info: TypeInfoImpl): String = {
    new GhostLessPrinter(info).format(program)
  }

  private def getDebugInfo(program: PProgram, info: TypeInfoImpl): String = {
    new InfoDebugPrettyPrinter(info).format(program)
  }
}
