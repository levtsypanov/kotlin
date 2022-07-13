/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with testLocal in folder ../codegen/stringConcatenationTypeNarrowing/kt53119_*.kt
// Please keep them in sync

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#manualPlusMemberAny
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: ret %struct.ObjHeader*

fun manualPlusMemberAny(str: String, maybeAny: kotlin.Any?): kotlin.String =
    str.plus(maybeAny)

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#manualPlusMemberString
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"

// CHECK: ret %struct.ObjHeader*

fun manualPlusMemberString(str1: String, str2: String): kotlin.String =
        str1.plus(str2)

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#generatedPlusMemberAny
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"

// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: ret %struct.ObjHeader*

fun generatedPlusMemberAny(str: String, maybeAny: Any?): String {
    return "$str$maybeAny"
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#generatedPlusMemberString
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: call %struct.ObjHeader* @Kotlin_String_plusImpl

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: ret %struct.ObjHeader*

fun generatedPlusMemberString(str1: String, str2: String): String {
    return "$str1$str2"
}

data class Foo(val bar: Int)

fun main() {
    val foo = Foo(42)
    println(manualPlusMemberAny("foo", foo))
    println(manualPlusMemberAny("foo", null))
    println(manualPlusMemberString("foo", "bar"))
    println(generatedPlusMemberAny("foo", null))
    println(generatedPlusMemberAny("foo", foo))
    println(generatedPlusMemberString("foo", "bar"))
}
