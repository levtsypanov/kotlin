/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.ir.backend.js.export

import org.jetbrains.kotlin.ir.backend.js.JsIrBackendContext
import org.jetbrains.kotlin.ir.backend.js.lower.isBuiltInClass
import org.jetbrains.kotlin.ir.backend.js.lower.isStdLibClass
import org.jetbrains.kotlin.ir.declarations.IrClass
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.symbols.IrTypeParameterSymbol
import org.jetbrains.kotlin.ir.types.*
import org.jetbrains.kotlin.ir.types.impl.IrSimpleTypeImpl

private typealias SubstitutionMap = Map<IrTypeParameterSymbol, IrTypeArgument>

class TransitiveExportCollector(val context: JsIrBackendContext) {
    private val typesCaches = hashMapOf<ClassWithAppliedArguments, Set<IrType>>()

    fun collectSuperTransitiveHierarchyFor(type: IrSimpleType): Set<IrType> {
        return (type.classifier as? IrClassSymbol)?.let { type.collectSuperTransitiveHierarchyFor(it, type.arguments) } ?: emptySet()
    }

    private fun IrSimpleType.collectSuperTransitiveHierarchyFor(classSymbol: IrClassSymbol, typeArguments: List<IrTypeArgument>): Set<IrType> {
        return typesCaches.getOrPut(ClassWithAppliedArguments(classSymbol, typeArguments)) { collectSuperTransitiveHierarchy(emptyMap()) }
    }

    private fun IrSimpleType.collectSuperTransitiveHierarchy(typeSubstitutionMap: SubstitutionMap): Set<IrType> {
        return (classifier as? IrClassSymbol)?.collectSuperTransitiveHierarchy(calculateTypeSubstitutionMap(typeSubstitutionMap))
            ?: emptySet()
    }

    private fun IrClassSymbol.collectSuperTransitiveHierarchy(typeSubstitutionMap: SubstitutionMap): Set<IrType> =
        superTypes()
            .flatMap { (it as? IrSimpleType)?.collectTransitiveHierarchy(typeSubstitutionMap) ?: emptyList() }
            .toSet()

    private fun IrSimpleType.collectTransitiveHierarchy(typeSubstitutionMap: SubstitutionMap): Set<IrType> {
        val owner = classifier.owner as? IrClass ?: return emptySet()
        return when {
            isBuiltInClass(owner) || isStdLibClass(owner) -> emptySet()
            owner.isExported(context) -> setOf(getSubstitutionFrom(typeSubstitutionMap) as IrType)
            else -> collectSuperTransitiveHierarchy(typeSubstitutionMap)
        }
    }

    private fun IrSimpleType.calculateTypeSubstitutionMap(typeSubstitutionMap: SubstitutionMap): SubstitutionMap {
        val classifier = this.classifier as? IrClassSymbol ?: error("Unexpected classifier $classifier for collecting transitive hierarchy")

        return typeSubstitutionMap + classifier.owner.typeParameters.zip(arguments).associate {
            it.first.symbol to it.second.getSubstitution(typeSubstitutionMap)
        }
    }

    private fun IrType.getSubstitutionFrom(typeSubstitutionMap: SubstitutionMap): IrTypeArgument {
        if (this !is IrSimpleType) return this as IrTypeArgument

        val classifier = when (val classifier = this.classifier) {
            is IrClassSymbol -> classifier
            is IrTypeParameterSymbol -> return typeSubstitutionMap[classifier] ?: this
            else -> return this
        }

        if (classifier.owner.typeParameters.isEmpty()) return this

        return IrSimpleTypeImpl(
            classifier,
            nullability,
            arguments.map { it.getSubstitution(typeSubstitutionMap) },
            this.annotations
        )
    }

    private fun IrTypeArgument.getSubstitution(typeSubstitutionMap: SubstitutionMap): IrTypeArgument {
        return when (this) {
            is IrType -> getSubstitutionFrom(typeSubstitutionMap)
            is IrTypeProjection -> type.getSubstitutionFrom(typeSubstitutionMap)
            else -> this
        }
    }

    private data class ClassWithAppliedArguments(val classSymbol: IrClassSymbol, val appliedArguments: List<IrTypeArgument>)
}
