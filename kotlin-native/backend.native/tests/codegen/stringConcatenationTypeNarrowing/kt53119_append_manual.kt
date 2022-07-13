/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with FileCheck in folder ../../filecheck/kt53119_*.kt
// Please keep them in sync

package codegen.stringConcatenationTypeNarrowing.kt53119_append_manual
import kotlin.test.*

fun appendMaybeAny(maybeAny: Any?): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(maybeAny)
    return sb.toString()
}

fun appendAny(any: Any): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(any)
    return sb.toString()
}

fun appendMaybeString(maybeStr: String?): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(maybeStr)
    return sb.toString()
}

fun appendString(str: String): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(str)
    return sb.toString()
}

data class Foo(val bar: Int)

@Test
fun runTest() {
    val foo = Foo(42)
    println(appendMaybeAny(foo))
    println(appendMaybeAny(null))
    println(appendAny(foo))
    println(appendMaybeString("foo"))
    println(appendMaybeString(null))
    println(appendString("foo"))
}
