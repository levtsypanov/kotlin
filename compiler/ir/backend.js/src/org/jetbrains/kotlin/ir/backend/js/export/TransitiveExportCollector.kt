/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.ir.backend.js.export

import org.jetbrains.kotlin.ir.backend.js.JsIrBackendContext
import org.jetbrains.kotlin.ir.backend.js.lower.isBuiltInClass
import org.jetbrains.kotlin.ir.backend.js.lower.isStdLibClass
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.types.classifierOrNull
import org.jetbrains.kotlin.ir.types.defaultType
import org.jetbrains.kotlin.ir.types.superTypes

class TransitiveExportCollector(val context: JsIrBackendContext) {
    private val classesCache = hashMapOf<IrClassSymbol, Set<IrType>>()

    fun collectSuperTransitiveHierarchyFor(classSymbol: IrClassSymbol): Set<IrType> {
        return classesCache.getOrPut(classSymbol) { classSymbol.collectSuperTransitiveHierarchy() }
    }

    private fun IrClassSymbol.collectSuperTransitiveHierarchy(): Set<IrType> =
        superTypes()
            .flatMap { (it.classifierOrNull as? IrClassSymbol)?.collectTransitiveHierarchy() ?: emptyList() }
            .toSet()

    private fun IrClassSymbol.collectTransitiveHierarchy(): Set<IrType> = when {
        isBuiltInClass(owner) || isStdLibClass(owner) -> emptySet()
        owner.isExported(context) -> setOf(defaultType)
        else -> collectSuperTransitiveHierarchy()
    }
}