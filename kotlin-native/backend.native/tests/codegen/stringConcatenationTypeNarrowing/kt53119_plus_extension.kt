/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with FileCheck in folder ../../filecheck/kt53119_*.kt
// Please keep them in sync

package codegen.stringConcatenationTypeNarrowing.kt53119_plus_extension
import kotlin.test.*

fun manualPlusExtensionAny(maybeStr: String?, maybeAny: kotlin.Any?): kotlin.String =
        maybeStr.plus(maybeAny)

fun manualPlusExtensionString(maybeStr: String?, str: String): kotlin.String =
        maybeStr.plus(str)

fun generatedPlusExtensionAny(maybeStr: String?, maybeAny: Any?): String {
    return "$maybeStr$maybeAny"
}

fun generatedPlusExtensionString(maybeStr: String?, str: String): String {
    return "$maybeStr$str"
}

data class Foo(val bar: Int)

@Test
fun runTest() {
    val foo = Foo(42)
    println(manualPlusExtensionAny("foo", foo))
    println(manualPlusExtensionAny(null, null))
    println(manualPlusExtensionString("foo", "bar"))
    println(manualPlusExtensionString(null, "bar"))
    println(generatedPlusExtensionAny("foo", foo))
    println(generatedPlusExtensionAny(null, null))
    println(generatedPlusExtensionString("foo", "bar"))
    println(generatedPlusExtensionString(null, "bar"))
}
