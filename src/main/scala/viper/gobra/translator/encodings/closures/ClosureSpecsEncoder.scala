// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.gobra.translator.encodings.closures

import viper.gobra.ast.internal.FunctionLikeMemberOrLit
import viper.gobra.ast.{internal => in}
import viper.gobra.reporting.BackTranslator.ErrorTransformer
import viper.gobra.reporting.{PreconditionError, Source, SpecNotImplementedByClosure}
import viper.gobra.theory.Addressability
import viper.gobra.translator.Names
import viper.gobra.translator.context.Context
import viper.gobra.translator.util.ViperWriter.CodeLevel.errorT
import viper.gobra.translator.util.ViperWriter.MemberKindCompanion.ErrorT
import viper.gobra.translator.util.ViperWriter.{CodeWriter, MemberWriter}
import viper.silver.verifier.{reasons, errors => vprerr}
import viper.silver.{ast => vpr}

protected class ClosureSpecsEncoder {

  /** Encodes spec implementation expressions as calls to the corresponding generated function.
    * R[ cl implements spec{params} ] -> closureImplements$[spec]$[idx of params]([cl], [params])
    * */
  def closureImplementsExpression(a: in.ClosureImplements)(ctx: Context): CodeWriter[vpr.Exp] = {
    register(a.spec)(ctx, a.info)
    ctx.expression(in.PureFunctionCall(implementsFunctionProxy(a.spec)(a.info),
      Vector(a.closure) ++ a.spec.params.toVector.sortBy(_._1).map(_._2), in.BoolT(Addressability.rValue))(a.info))
  }

  /**
    * Encodes:
    *   - function literal getters
    *   - function getters
    *
    * R[ pure? func funcLitName(_)_ { _ } ] ->
    *   register spec instance funcLitName{}
    *   return closureGet$funcLitName([ pointers to captured vars ])
    *
    * R[ funcName ] ->
    *   register spec instance funcName{}
    *   return closureGet$funcName()
    */
  def callToClosureGetter(func: in.FunctionMemberOrLitProxy, captured: Vector[(in.Expr, in.Parameter.In)] = Vector.empty)(ctx: Context): CodeWriter[vpr.Exp] = {
    val errorTransformers = register(in.ClosureSpec(func, Map.empty)(func.info))(ctx, func.info)
    for {
      exp <- ctx.expression(in.PureFunctionCall(closureGetterFunctionProxy(func), captured.map(c => c._1), genericFuncType)(func.info))
      _ <- errorT(errorTransformers: _*)
    } yield exp
  }

  /**
    * Encodes (non-pure) closure calls.
    *
    * [ts := cl(args) as spec{params}] -> [ts] := closureCall$[spec]$[idx of params]([cl], [params], [args])
    */
  def closureCall(c: in.ClosureCall)(ctx: Context): CodeWriter[vpr.Stmt] = {
    register(c.spec)(ctx, c.spec.info)

    for {
      call <- ctx.statement(in.FunctionCall(c.targets, closureCallProxy(c.spec)(c.info), closureCallArgs(c.closure, c.args, c.spec)(ctx))(c.info))
      _ <- errorT(doesNotImplementSpecErr(c.closure, c.spec))
    } yield call
  }

  /**
    * Encodes pure closure calls.
    *
    * [cl(args) as spec{params}] -> closureCall$[spec]$[idx of params]([cl], [vars captured by cl], [args + params])
    */
  def pureClosureCall(c: in.PureClosureCall)(ctx: Context): CodeWriter[vpr.Exp] = {
    register(c.spec)(ctx, c.spec.info)

    for {
      exp <- ctx.expression(in.PureFunctionCall(closureCallProxy(c.spec)(c.info), closureCallArgs(c.closure, c.args, c.spec)(ctx), c.typ)(c.info))
      _ <- errorT(doesNotImplementSpecErr(c.closure, c.spec))
    } yield exp
  }

  def finalize(addMemberFn: vpr.Member => Unit): Unit = {
    genMembers foreach { m => addMemberFn(m.res) }
  }

  private def doesNotImplementSpecErr(closureExpr: in.Expr, spec: in.ClosureSpec): ErrorTransformer = {
    case vprerr.PreconditionInCallFalse(Source(info), reasons.AssertionFalse(vpr.FuncApp(funcName, args)), _)
      if info.isInstanceOf[Source.Verifier.Info] &&
        args.size == 1 + spec.params.size &&
        args.head.info.asInstanceOf[Source.Verifier.Info].node == closureExpr &&
        args.tail.zip(spec.params.toVector.sortBy(p => p._1).map(p => p._2))
          .forall(p => p._1.info.asInstanceOf[Source.Verifier.Info].node == p._2) &&
         funcName == implementsFunctionName(spec) =>
            PreconditionError(info).dueTo(SpecNotImplementedByClosure(info, closureExpr.info.tag, spec.info.tag))
  }

  private def captured(ctx: Context)(func: in.FunctionMemberOrLitProxy): Vector[(in.Expr, in.Parameter.In)] = func match {
    case _: in.FunctionProxy => Vector.empty
    case p: in.FunctionLitProxy => ctx.table.lookup(p).captured
  }

  private def memberOrLit(ctx: Context)(func: in.FunctionMemberOrLitProxy): in.FunctionLikeMemberOrLit = func match {
    case p: in.FunctionProxy => ctx.table.lookup(p).asInstanceOf[in.FunctionMember]
    case p: in.FunctionLitProxy => ctx.table.lookup(p)
  }

  /**
    * Registers spec fName{params}:
    * - if necessary, updates the maximum number of captured variables for the corresponding type
    * - if the spec has not already been registered:
    *   > generates a closureImplements$[spec] function (see [[implementsFunction]])
    *   > generates a closureCall$[spec] method/function (see [[callableMemberWithClosure]])
    *   > collects any error transformers generated while encoding closureCall$[...]
    * - if no spec with base function fName has already been registered:
    *   > generates a closureGet$fName getter function (see [[closureGetter]])
    * - Adds all of the generated members to [[genMembers]]
    * - Returns the collected error transformers
    * */
  private def register(spec: in.ClosureSpec)(ctx: Context, info: Source.Parser.Info): Vector[ErrorTransformer] = {
    var errorTransformers: Vector[ErrorTransformer] = Vector.empty
    updateCaptVarTypes(ctx)(captured(ctx)(spec.func).map(_._1.typ))
    if (!specsSeen.contains((spec.func, spec.params.keySet))) {
      specsSeen += ((spec.func, spec.params.keySet))
      val implementsF = implementsFunction(spec)(ctx, info)
      val callable = callableMemberWithClosure(spec)(ctx)
      errorTransformers = callable.sum.collect{ case ErrorT(t) => t }.toVector
      genMembers :+= implementsF
      genMembers :+= callable
    }
    if (!funcsUsedAsClosures.contains(spec.func)) {
      funcsUsedAsClosures += spec.func
      val getter = closureGetter(spec.func)(ctx)
      genMembers :+= getter
    }

    errorTransformers
  }

  private var captVarTypeIdAndNum = Map[vpr.Type, (Int, Int)]()
  def captVarsTypeMap: Map[vpr.Type, (Int, Int)] = captVarTypeIdAndNum

  /**
    * Updates the maximum counts of captured variables for each encountered type.
    * Assigns a unique id to each encountered type.
    */
  private def updateCaptVarTypes(ctx: Context)(types: Vector[in.Type]): Unit = {
    types.groupBy(ctx.typ).foreach {
      case (typ, vec) =>
        val (id, num) = captVarTypeIdAndNum.getOrElse(typ, (captVarTypeIdAndNum.size, 0))
        if (vec.size > num) captVarTypeIdAndNum += typ -> (id, vec.size)
    }
  }
  def numSpecs: Int = specsSeen.size

  private var specsSeen: Set[(in.FunctionMemberOrLitProxy, Set[Int])] = Set.empty
  private var funcsUsedAsClosures: Set[in.FunctionMemberOrLitProxy] = Set.empty
  private var genMembers: Vector[MemberWriter[vpr.Member]] = Vector.empty

  private val genericFuncType: in.FunctionT = in.FunctionT(Vector.empty, Vector.empty, Addressability.rValue)

  private def closureSpecName(spec: in.ClosureSpec): String =  s"${spec.func}$$${spec.params.keySet.toSeq.sorted.mkString("_")}"
  private def implementsFunctionName(spec: in.ClosureSpec) = s"${Names.closureImplementsFunc}$$${closureSpecName(spec)}"
  private def implementsFunctionProxy(spec: in.ClosureSpec)(info: Source.Parser.Info): in.FunctionProxy = in.FunctionProxy(implementsFunctionName(spec))(info)
  private def closureGetterFunctionProxy(func: in.FunctionMemberOrLitProxy): in.FunctionProxy = in.FunctionProxy(s"${Names.closureGetter}$$$func")(func.info)
  private def closureCallProxy(spec: in.ClosureSpec)(info: Source.Parser.Info): in.FunctionProxy = in.FunctionProxy(s"${Names.closureCall}$$${closureSpecName(spec)}")(info)

  /**
    * Given spec{params}, generates:
    * function closureImplements$[spec]$[idx of params](closure: Closure, [params name and type]): Bool
    * */
  private def implementsFunction(spec: in.ClosureSpec)(ctx: Context, info: Source.Parser.Info): MemberWriter[vpr.Member] = {
    val proxy = implementsFunctionProxy(spec)(info)
    val closurePar = in.Parameter.In(Names.closureArg, genericFuncType)(info)
    val params = spec.params.map(p => in.Parameter.In(Names.closureImplementsParam(p._1), p._2.typ.withAddressability(Addressability.inParameter))(p._2.info))
    val args = Vector(closurePar) ++ params
    val result = Vector(in.Parameter.Out("r", in.BoolT(Addressability.outParameter))(info))
    val terminates = in.WildcardMeasure(None)(info)
    val func = in.PureFunction(proxy, args, result, Vector(terminates), Vector.empty, Vector.empty, None)(info)
    ctx.defaultEncoding.pureFunction(func)(ctx)
  }

  /**
    * Given fName, generates:
    * function closureGet$[fName](captvar1_0: Type0, captvar2_0: Type0, captvar1_1: Type1, ...): Closure
    *   ensures [result implements fName]
    *   for X-th captured variable of T-th type: ensures captVarXClosure_T(result) == captvarX_T(result)
    * */
  private def closureGetter(func: in.FunctionMemberOrLitProxy)(ctx: Context): MemberWriter[vpr.Member] = {
    val proxy = closureGetterFunctionProxy(func)
    val info = func.info
    val result = in.Parameter.Out(Names.closureArg, genericFuncType)(info)
    val satisfiesSpec = in.ExprAssertion(in.ClosureImplements(result, in.ClosureSpec(func, Map.empty)(info))(info))(info)
    val terminates = in.WildcardMeasure(None)(info)
    val (args, captAssertions) = capturedArgsAndAssertions(ctx)(result, captured(ctx)(func), info)
    val getter = in.PureFunction(proxy, args, Vector(result), Vector(terminates), Vector(satisfiesSpec) ++ captAssertions, Vector.empty, None)(memberOrLit(ctx)(func).info)
    ctx.defaultEncoding.pureFunction(getter)(ctx)
  }

  /**
    * Returns the arguments for an encoded closure call:
    *   (closure, args, fName{params}) -> (closure, vars captured by fName, args + params)
   */
  private def closureCallArgs(closure: in.Expr, args: Vector[in.Expr], spec: in.ClosureSpec)(ctx: Context): Vector[in.Expr] = {
    val capt = captured(ctx)(spec.func)
    val captProxies = captVarProxies(ctx)(capt.map(_._1.typ), spec.func.info)
    val captArgs = (1 to capt.size).map(i => in.DomainFunctionCall(captProxies(i-1), Vector(closure), capt(i-1)._2.typ)(closure.info))
    val argsAndParams = {
      var argsUsed = 0
      (1 to (args.size + spec.params.size)).map(i => if (spec.params.contains(i)) spec.params(i) else { argsUsed += 1; args(argsUsed-1) })
    }
    Vector(closure) ++ captArgs ++ argsAndParams
  }

  /**
    * Returns (captArgs, assertions), where:
    *   - captArgs is the list of parameters corresponding to the variables captured by the closure
    *   - assertions is the list of assertions, one for each captured variable captVarXClosure_T, of the form:
    *       captVarXClosure_T(result) == captvarX_T(result)
    */
  private def capturedArgsAndAssertions(ctx: Context)(closure: in.Expr, captured: Vector[(in.Expr, in.Parameter.In)], info: Source.Parser.Info): (Vector[in.Parameter.In], Vector[in.Assertion]) = {
    val captArgs = captured.map(c => c._2)
    val captProxies = captVarProxies(ctx)(captured.map(c => c._1.typ), info)
    val capturesVar: Int => in.Assertion = i => in.ExprAssertion(in.EqCmp(in.DomainFunctionCall(
      captProxies(i-1), Vector(closure), captArgs(i-1).typ)(info), captArgs(i-1))(info))(info)
    val assertions = (1 to captured.size).toVector map { i => capturesVar(i) }
    (captArgs, assertions)
  }

  /** Generate the proxies for the domain functions corresponding to the variables captured by the closure.
    * The name is captVarNClosure_T, where T is an id different for each Viper type, and N denotes the position
    * of the variable among all the variables with the same type. */
  private def captVarProxies(ctx: Context)(types: Vector[in.Type], info: Source.Parser.Info): Vector[in.DomainFuncProxy] = {
    var seenSoFar = Map[vpr.Type, Int]()
    types map { t =>
      val vprTyp = ctx.typ(t)
      val i = seenSoFar.getOrElse(vprTyp, 0) + 1
      seenSoFar += vprTyp -> i
      val (tid, _) = captVarsTypeMap(vprTyp)
      in.DomainFuncProxy(Names.closureCaptVarDomFunc(i, tid), Names.closureDomain)(info)
    }
  }

  /** Replaces all the parameter expressions in spec with the corresponding in-parameter of function f */
  private def specWithFuncArgs(spec: in.ClosureSpec, f: FunctionLikeMemberOrLit): in.ClosureSpec =
    in.ClosureSpec(spec.func, spec.params.map{ case (i, _) => i -> f.args(i-1)})(spec.info)

  /** Generates a Viper method/function with the same specification as the original, but with an additional
    * closure argument and closure implementation precondition.
    * For function literals, also inlcudes captured variables among the arguments, and encodes the body as
    * well as the specification, so that the literal is verified. */
  private def callableMemberWithClosure(spec: in.ClosureSpec)(ctx: Context): MemberWriter[vpr.Member] = {
    val proxy = closureCallProxy(spec)(spec.info)
    val func = memberOrLit(ctx)(spec.func)
    val closurePar = in.Parameter.In(Names.closureArg, genericFuncType)(func.info)
    val (captArgs, captAssertions) = capturedArgsAndAssertions(ctx)(closurePar, captured(ctx)(spec.func), spec.func.info)
    val args = Vector(closurePar) ++ captArgs ++ func.args
    val implementsAssertion = in.ExprAssertion(in.ClosureImplements(closurePar, specWithFuncArgs(spec, func))(spec.info))(spec.info)
    val pres = Vector(implementsAssertion) ++ func.pres ++ captAssertions
    func match {
      case _: in.Function =>
        val m = in.Function(proxy, args, func.results, pres, func.posts, func.terminationMeasures, None)(spec.info)
        ctx.defaultEncoding.function(m)(ctx)
      case lit: in.FunctionLit =>
        val body = if (spec.params.isEmpty) lit.body else None
        val func = in.Function(proxy, args, lit.results, pres, lit.posts, lit.terminationMeasures, body)(lit.info)
        ctx.defaultEncoding.function(func)(ctx)
      case f: in.PureFunction =>
        val posts = func.posts ++ assertionFromPureFunctionBody(f.body, f.results.head)
        val m = in.PureFunction(proxy, args, f.results, pres, posts, f.terminationMeasures, None)(spec.info)
        ctx.defaultEncoding.pureFunction(m)(ctx)
      case lit: in.PureFunctionLit =>
        val body = if (spec.params.isEmpty) lit.body else None
        val posts = lit.posts ++ (if (spec.params.isEmpty) Vector.empty else assertionFromPureFunctionBody(lit.body, lit.results.head).toVector)
        val func = in.PureFunction(proxy, args, lit.results, pres, posts, lit.terminationMeasures, body)(lit.info)
        ctx.defaultEncoding.pureFunction(func)(ctx)
    }
  }

  /** From { body }, get assertion result == body
    * This is useful to avoid multiple error messages when the body does not verify,
    * by encoding the body as a postcondition.
    * The original body is still encoded, so this does not affect correctness. */
  private def assertionFromPureFunctionBody(body: Option[in.Expr], res: in.Expr): Option[in.Assertion] =
    body.map(e => in.ExprAssertion(in.EqCmp(res, e)(e.info))(e.info))
}
