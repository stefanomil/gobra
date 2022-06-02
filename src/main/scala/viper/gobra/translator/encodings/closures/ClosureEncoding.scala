package viper.gobra.translator.encodings.closures

import viper.gobra.translator.encodings.LeafTypeEncoding
import org.bitbucket.inkytonik.kiama.==>
import viper.gobra.ast.{internal => in}
import viper.gobra.theory.Addressability
import viper.gobra.translator.Names.serializeType
import viper.gobra.translator.interfaces.Context
import viper.silver.{ast => vpr}

class ClosureEncoding extends LeafTypeEncoding{
  import viper.gobra.translator.util.ViperWriter.CodeLevel._
  import viper.gobra.translator.util.ViperWriter.MemberWriter
  import viper.gobra.translator.util.ViperWriter.{MemberLevel => ml}
  import viper.gobra.translator.util.TypePatterns._

  override def finalize(addMemberFn: vpr.Member => Unit): Unit = {
    closureDomainMap foreach { entry => addMemberFn(entry._2) }
    genPredicates foreach addMemberFn
    genMembers foreach addMemberFn
  }

  override def member(ctx: Context): in.Member ==> MemberWriter[Vector[vpr.Member]] = {
    case p: in.ClosureSpec =>
      {
        // Domain
        val closureDomain = genClosureDomain(p)

        // Proof inferface (ignoring interface members for now)
        val interfaceParam = in.Parameter.In(s"thisSpec", in.InterfaceT(s"proof_${p.name}", Addressability.Exclusive))(p.info)
        val memPredProxy = in.MPredicateProxy("mem", s"mem_${p.name}")(p.info)
        val memPred = in.MPredicate(interfaceParam, memPredProxy, Vector.empty, None)(p.info)
        val statelessFuncProxy = in.MethodProxy("stateless", s"stateless_${p.name}")(p.info)
        val statelessFunc = in.PureMethod(interfaceParam, statelessFuncProxy, Vector.empty,
          Vector(in.Parameter.Out("", in.BoolT(Addressability.Exclusive))(p.info)), Vector.empty, Vector.empty, Vector.empty, None)(p.info)
        genPredicates ::= ctx.predicate.mpredicate(memPred)(ctx).res
        genMembers ::= ctx.pureMethod.pureMethod(statelessFunc)(ctx).res

        val closureArg = in.Parameter.In(s"closure", in.DomainT(closureDomain.name, Addressability.Exclusive))(p.info)
        val proofArg = in.Parameter.In(s"proof", in.InterfaceT(s"proof_${p.name}", Addressability.Exclusive))(p.info)
        // Satisfies function
        val satisfiesFuncProxy = in.FunctionProxy(s"satisfies_${p.name}")(p.info)
        val satisfiesFunc = in.PureFunction(satisfiesFuncProxy, p.params ++ Vector(closureArg, proofArg),
          Vector(in.Parameter.Out("", in.BoolT(Addressability.Exclusive))(p.info)), Vector.empty, Vector.empty, Vector.empty, None)(p.info)
        genMembers ::= ctx.pureMethod.pureFunction(satisfiesFunc)(ctx).res

        // Omitting default proof

        // Closure method
        val accAss = in.Implication(in.Negation(in.PureMethodCall(proofArg, statelessFuncProxy, Vector.empty, in.BoolT(Addressability.Exclusive))(p.info))(p.info),
          in.Access(in.Accessible.Predicate(in.MPredicateAccess(proofArg, memPredProxy, Vector.empty)(p.info)), in.FullPerm(p.info))(p.info))(p.info)
        val satisfiesAss = in.ExprAssertion(in.PureFunctionCall(satisfiesFuncProxy, p.params ++ Vector(closureArg, proofArg), in.BoolT(Addressability.Exclusive))(p.info))(p.info)
        val specFunc = in.Function(in.FunctionProxy(p.name.name)(p.info), Vector(closureArg, proofArg) ++ p.params ++ p.args,
          p.results, Vector(accAss, satisfiesAss) ++ p.pres, Vector(accAss, satisfiesAss) ++ p.posts, Vector.empty, None)(p.info)

        ctx.method.function(specFunc)(ctx).map(res => Vector(res))
      }
  }

  private var genPredicates: List[vpr.Predicate] = List.empty
  private var genMembers: List[vpr.Member] = List.empty

  private def genClosureDomain(spec: in.ClosureSpec): vpr.Domain = {
//    val typeString = s"${spec.args.map(arg => serializeType(arg.typ)).mkString("_")}$$${spec.results.map(res => serializeType(res.typ)).mkString("_")}"
    val closureType = (spec.args.map(_.typ), spec.results.map(_.typ))
    closureDomainMap.getOrElse(closureType, {
      val res = vpr.Domain(genClosureDomainName(spec.args.map(_.typ), spec.results.map(_.typ)), Nil, Nil, Nil)()
      closureDomainMap += (closureType -> res)
      res
    })
  }
  private var closureDomainMap: Map[(Seq[in.Type], Seq[in.Type]), vpr.Domain] = Map.empty


  private def genClosureDomainName(args: Vector[in.Type], results: Vector[in.Type]): String =
    s"Closure$$${args.map(serializeType).mkString("_")}$$${results.map(serializeType).mkString("_")}"
}
