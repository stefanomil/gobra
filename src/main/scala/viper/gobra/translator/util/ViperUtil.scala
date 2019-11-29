package viper.gobra.translator.util

import viper.silver.ast._

object ViperUtil {

  def toVarDecl(v: LocalVar): LocalVarDecl = {
    LocalVarDecl(v.name, v.typ)(v.pos, v.info, v.errT)
  }

  def toVar(d: LocalVarDecl): LocalVar = {
    d.localVar
  }

  def bigAnd(it: Iterable[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    it.foldLeft[Exp](TrueLit()(pos, info, errT)){case (l, r) => And(l, r)(pos, info, errT)}
  }

  def seqn(ss: Vector[Stmt])(pos: Position, info: Info, errT: ErrorTrafo): Seqn = Seqn(ss, Vector.empty)(pos, info, errT)

  def nop(pos: Position, info: Info, errT: ErrorTrafo): Seqn = Seqn(Vector.empty, Vector.empty)(pos, info, errT)
}
