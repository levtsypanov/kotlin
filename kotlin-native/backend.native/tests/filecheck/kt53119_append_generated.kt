/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with testLocal in folder ../codegen/stringConcatenationTypeNarrowing/kt53119_*.kt
// Please keep them in sync

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#maybeAnyMaybeAny
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: ret %struct.ObjHeader*

fun maybeAnyMaybeAny(maybeAny1: Any?, maybeAny2: Any?): String {
    return "$maybeAny1,$maybeAny2"
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#maybeAnyMaybeString
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append
// CHECK: ret %struct.ObjHeader*

fun maybeAnyMaybeString(maybeAny1: Any?, maybeString2: String?): String {
    return "$maybeAny1,$maybeString2"
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#maybeAnyString
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String?)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String)
// CHECK: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append(kotlin.String)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.text.StringBuilder#append
// CHECK: ret %struct.ObjHeader*

fun maybeAnyString(maybeAny1: Any?, string: String): String {
    return "$maybeAny1,$string"
}

data class Foo(val bar: Int)

fun main() {
    val foo = Foo(42)
    println(maybeAnyMaybeAny(foo, foo))
    println(maybeAnyMaybeAny(null, null))
    println(maybeAnyMaybeString(foo, "bar"))
    println(maybeAnyMaybeString(null, null))
    println(maybeAnyString(foo, "bar"))
    println(maybeAnyString(null, "bar"))
}
