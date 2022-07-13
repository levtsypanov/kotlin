/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with testLocal in folder ../codegen/stringConcatenationTypeNarrowing/kt53119_*.kt
// Please keep them in sync

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#appendMaybeAny(kotlin.Any?)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: ret %struct.ObjHeader*

fun appendMaybeAny(maybeAny: Any?): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(maybeAny)
    return sb.toString()
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#appendAny(kotlin.Any)
// CHECK: %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String)

// CHECK-NOT: %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append
// CHECK: ret %struct.ObjHeader*

fun appendAny(any: Any): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(any)
    return sb.toString()
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#appendMaybeString(kotlin.String?)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String

// CHECK: ret %struct.ObjHeader*

fun appendMaybeString(maybeStr: String?): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(maybeStr)
    return sb.toString()
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#appendString(kotlin.String)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String

// CHECK: ret %struct.ObjHeader*

fun appendString(str: String): String {
    val sb = kotlin.text.StringBuilder()
    sb.append(str)
    return sb.toString()
}

data class Foo(val bar: Int)

fun main() {
    val foo = Foo(42)
    println(appendMaybeAny(foo))
    println(appendMaybeAny(null))
    println(appendAny(foo))
    println(appendMaybeString("foo"))
    println(appendMaybeString(null))
    println(appendString("foo"))
}
