/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with FileCheck in folder ../../filecheck/kt53119_*.kt
// Please keep them in sync

package codegen.stringConcatenationTypeNarrowing.kt53119_append_generated
import kotlin.test.*

fun maybeAnyMaybeAny(maybeAny1: Any?, maybeAny2: Any?): String {
    return "$maybeAny1,$maybeAny2"
}

fun maybeAnyMaybeString(maybeAny1: Any?, maybeString2: String?): String {
    return "$maybeAny1,$maybeString2"
}

fun maybeAnyString(maybeAny1: Any?, string: String): String {
    return "$maybeAny1,$string"
}

data class Foo(val bar: Int)

@Test
fun runTest() {
    val foo = Foo(42)
    println(maybeAnyMaybeAny(foo, foo))
    println(maybeAnyMaybeAny(null, null))
    println(maybeAnyMaybeString(foo, "bar"))
    println(maybeAnyMaybeString(null, null))
    println(maybeAnyString(foo, "bar"))
    println(maybeAnyString(null, "bar"))
}
