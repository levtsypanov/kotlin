/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with FileCheck in folder ../../filecheck/kt53119_*.kt
// Please keep them in sync

package codegen.stringConcatenationTypeNarrowing.kt53119_plus_member
import kotlin.test.*

fun manualPlusMemberAny(str: String, maybeAny: kotlin.Any?): kotlin.String =
    str.plus(maybeAny)

fun manualPlusMemberString(str1: String, str2: String): kotlin.String =
        str1.plus(str2)

fun generatedPlusMemberAny(str: String, maybeAny: Any?): String {
    return "$str$maybeAny"
}

fun generatedPlusMemberString(str1: String, str2: String): String {
    return "$str1$str2"
}

data class Foo(val bar: Int)

@Test
fun runTest() {
    val foo = Foo(42)
    println(manualPlusMemberAny("foo", foo))
    println(manualPlusMemberAny("foo", null))
    println(manualPlusMemberString("foo", "bar"))
    println(generatedPlusMemberAny("foo", null))
    println(generatedPlusMemberAny("foo", foo))
    println(generatedPlusMemberString("foo", "bar"))
}
