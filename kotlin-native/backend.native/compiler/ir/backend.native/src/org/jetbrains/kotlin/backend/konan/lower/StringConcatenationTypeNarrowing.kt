/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.backend.konan.lower

import org.jetbrains.kotlin.backend.konan.Context
import org.jetbrains.kotlin.backend.common.FileLoweringPass
import org.jetbrains.kotlin.backend.common.lower.IrBuildingTransformer
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.ir.builders.*
import org.jetbrains.kotlin.ir.declarations.*
import org.jetbrains.kotlin.ir.expressions.IrCall
import org.jetbrains.kotlin.ir.expressions.IrExpression
import org.jetbrains.kotlin.ir.expressions.IrGetValue
import org.jetbrains.kotlin.ir.expressions.impl.IrCallImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrConstImpl
import org.jetbrains.kotlin.ir.types.*
import org.jetbrains.kotlin.ir.util.functions
import org.jetbrains.kotlin.ir.util.isTrivial
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.Name

/**
 * This pass replaces calls to:
 * - StringBuilder.append(Any?) with StringBuilder.append(String?)
 * - StringBuilder.append(Any) with StringBuilder.append(String)
 * - String.plus(Any?) with String.plusImpl(String)
 * - String?.plus(Any?) with String.plusImpl(String)
 * For this, toString() is called for non-String arguments. This call can be later devirtualized, improving escape analysis
 * For nullable arguments, the following snippet is used:
 * - "if (arg==null) null else arg.toString()"  to pass to StringBuilder.append(String?)
 * - "if (arg==null) "null" else arg.toString()"  to pass to other methods as non-nullable String
 */
internal class StringConcatenationTypeNarrowing(val context: Context) : FileLoweringPass, IrBuildingTransformer(context) {

    private val string = context.ir.symbols.string.owner
    private val stringBuilder = context.ir.symbols.stringBuilder.owner
    private val namePlusImpl = Name.identifier("plusImpl")
    private val nameAppend = Name.identifier("append")

    private val appendStringFunction = stringBuilder.functions.single {  // StringBuilder.append(String)
        it.name == nameAppend &&
                it.valueParameters.size == 1 &&
                it.valueParameters.single().type.isString()
    }
    private val appendNullableStringFunction = stringBuilder.functions.single {  // StringBuilder.append(String?)
        it.name == nameAppend &&
                it.valueParameters.size == 1 &&
                it.valueParameters.single().type.isNullableString()
    }
    private val appendAnyFunction = stringBuilder.functions.single {  // StringBuilder.append(Any?)
        it.name == nameAppend &&
                it.valueParameters.size == 1 &&
                it.valueParameters.single().type.isNullableAny()
    }

    // null happens in :kotlin-native:endorsedLibraries:kotlinx.cli:macos_arm64KotlinxCliCache
    private val plusImplFunction = string.functions.singleOrNull {// external fun String.plusImpl(String)
        it.name == namePlusImpl &&
                it.valueParameters.size == 1 &&
                it.valueParameters.single().type.isString()
    }

    override fun lower(irFile: IrFile) {
        if (context.shouldOptimize()) {
            irFile.transformChildrenVoid(this)
        }
    }

    override fun visitCall(expression: IrCall): IrExpression {
        expression.transformChildrenVoid(this)
        return with(expression) {
            when (symbol) {
                appendAnyFunction.symbol -> {  // StringBuilder.append(Any?)
                    val argument = getValueArgument(0)!!
                    if (argument.type.isNullable()) {
                        // Transform `StringBuilder.append(Any?)` to `StringBuilder.append(ARG?.toString())`, using "StringBuilder.append(String?)"
                        buildConcatenationCall(appendNullableStringFunction, dispatchReceiver!!, argument, ::buildNullableArgToNullableString)
                    } else {
                        // Transform `StringBuilder.append(Any)` to `StringBuilder.append(ARG.toString())`, using "StringBuilder.append(String)"
                        buildConcatenationCall(appendStringFunction, dispatchReceiver!!, argument, ::buildNonNullableArgToString)
                    }
                }

                context.irBuiltIns.memberStringPlus -> {  // String.plus(Any?)
                    if (plusImplFunction != null) {
                        buildConcatenationCall(plusImplFunction, dispatchReceiver!!, getValueArgument(0)!!, ::buildNullableArgToString)
                    } else expression
                }

                context.irBuiltIns.extensionStringPlus -> {  // String?.plus(Any?)
                    if (plusImplFunction != null)
                        buildConcatenationCall(plusImplFunction, buildNullableArgToString(this, extensionReceiver!!),
                                getValueArgument(0)!!, ::buildNullableArgToString)
                    else expression
                }
                else -> expression
            }
        }
    }

    private fun IrCall.buildConcatenationCall(function: IrSimpleFunction, receiver: IrExpression, argument: IrExpression,
                                              blockBuilder: (IrCall, IrExpression) -> IrExpression) =
            IrCallImpl(startOffset, endOffset, function.returnType, function.symbol, typeArgumentsCount = 0, valueArgumentsCount = 1).apply {
                putValueArgument(0, blockBuilder(this, argument))
                dispatchReceiver = receiver
            }

    private fun IrCall.buildEQEQ(arg0: IrExpression, arg1: IrExpression) =
            IrCallImpl(startOffset, endOffset, context.irBuiltIns.booleanType, context.irBuiltIns.eqeqSymbol,
                    typeArgumentsCount = 0, valueArgumentsCount = 2, origin).apply {
                putValueArgument(0, arg0)
                putValueArgument(1, arg1)
            }

    // Builds snippet of type String
    // - "if(argument==null) "null" else argument.toString()", if argument's type is nullable. Note: fortunately, all "null" string structures are unified
    // - "argument.toString()", otherwise
    private fun buildNullableArgToString(irCall: IrCall, argument: IrExpression): IrExpression {
        return with(irCall) {
            if (argument.type.isNullable()) {
                context.createIrBuilder(builder.scope.scopeOwnerSymbol).irBlock(irCall.startOffset, irCall.endOffset) {
                    val argumentValue = createTempValIfNecessary(argument)
                    +irIfThenElse(
                            context.irBuiltIns.stringType,
                            condition = buildEQEQ(argumentValue, IrConstImpl.constNull(startOffset, endOffset, context.irBuiltIns.nothingNType)),
                            thenPart = IrConstImpl.string(startOffset, endOffset, context.irBuiltIns.stringType, "null"),
                            elsePart = buildNonNullableArgToString(irCall, argumentValue),
                            origin = null
                    )
                }
            } else buildNonNullableArgToString(this, argument)
        }
    }

    // Builds snippet of type String?
    // "if(argument==null) null else argument.toString()", that is similar to "argument?.toString()"
    private fun buildNullableArgToNullableString(irCall: IrCall, argument: IrExpression): IrExpression {
        return with(irCall) {
            context.createIrBuilder(builder.scope.scopeOwnerSymbol).irBlock(irCall.startOffset, irCall.endOffset) {
                val argumentValue = createTempValIfNecessary(argument)
                +irIfThenElse(
                        context.irBuiltIns.stringType.makeNullable(),
                        condition = buildEQEQ(argumentValue, IrConstImpl.constNull(startOffset, endOffset, context.irBuiltIns.nothingNType)),
                        thenPart = IrConstImpl.constNull(startOffset, endOffset, context.irBuiltIns.nothingNType),
                        elsePart = buildNonNullableArgToString(irCall, argumentValue),
                        origin = null
                )
            }
        }
    }

    // Builds snippet of type String
    // - "argument", in case argument's type is String, since String.toString() is no-op
    // - "argument", in case argument's type is String?, due to smart-cast and no-op
    // - "argument.toString()", otherwise
    private fun buildNonNullableArgToString(irCall: IrCall, argument: IrExpression): IrExpression {
        return with(irCall) {
            if (argument.type.isString() || argument.type.isNullableString())
                argument
            else IrCallImpl(startOffset, endOffset, context.irBuiltIns.stringType, context.ir.symbols.memberToString,
                    0, symbol.owner.valueParameters.size, origin).apply {
                dispatchReceiver = argument
            }
        }
    }

    /**
     * If [expression] is non-trivial, this function creates a temporary local variable for that expression and returns [IrGetValue] for it.
     * Otherwise, it returns original trivial [expression]. This helps reduce excessive unnecessary local variable usage.
     * Inspired by lower/loops/utils/DeclarationIrBuilder.createTemporaryVariableIfNecessary
     */
    private fun IrBlockBuilder.createTempValIfNecessary(expression: IrExpression): IrExpression =
            if (expression.isTrivial())
                expression
            else
                irGet(createTmpVariable(expression))

}
