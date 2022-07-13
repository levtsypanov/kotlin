/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// The same tests are also tested with testLocal in folder ../codegen/stringConcatenationTypeNarrowing/kt53119_*.kt
// Please keep them in sync

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#manualPlusExtensionAny
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: ret %struct.ObjHeader*

fun manualPlusExtensionAny(maybeStr: String?, maybeAny: kotlin.Any?): kotlin.String =
        maybeStr.plus(maybeAny)

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#manualPlusExtensionString
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: ret %struct.ObjHeader*

fun manualPlusExtensionString(maybeStr: String?, str: String): kotlin.String =
        maybeStr.plus(str)

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#generatedPlusExtensionAny
// CHECK-NOT: kfun:kotlin#plus__at__kotlin.String?(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: kfun:kotlin#plus__at__kotlin.String?(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"

// CHECK-NOT: call %struct.ObjHeader* @"kfun:Foo#toString(){}kotlin.String"
// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin#plus__at__kotlin.String?(kotlin.Any?)
// CHECK-NOT: call %struct.ObjHeader* @Kotlin_String_plusImpl

// CHECK: ret %struct.ObjHeader*

fun generatedPlusExtensionAny(maybeStr: String?, maybeAny: Any?): String {
    return "$maybeStr$maybeAny"
}

// CHECK-LABEL: define %struct.ObjHeader* @"kfun:#generatedPlusExtensionString
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: call %struct.ObjHeader* @Kotlin_String_plusImpl
// CHECK-NOT: call %struct.ObjHeader* @Kotlin_String_plusImpl

// CHECK-NOT: call %struct.ObjHeader* @"kfun:kotlin.String#toString(){}kotlin.String"
// CHECK-NOT: kfun:kotlin.String#plus(kotlin.Any?)

// CHECK: ret %struct.ObjHeader*

fun generatedPlusExtensionString(maybeStr: String?, str: String): String {
    return "$maybeStr$str"
}

data class Foo(val bar: Int)

fun main() {
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
