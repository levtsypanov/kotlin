/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.js.test.handlers

import org.jetbrains.kotlin.descriptors.ModuleDescriptor
import org.jetbrains.kotlin.ir.backend.js.transformers.irToJs.TranslationMode
import org.jetbrains.kotlin.js.parser.sourcemaps.*
import org.jetbrains.kotlin.test.services.TestServices
import org.jetbrains.kotlin.test.services.configuration.JsEnvironmentConfigurator
import org.jetbrains.kotlin.test.services.jsLibraryProvider
import org.jetbrains.kotlin.test.services.moduleStructure
import java.io.File

/**
 * The sourcemaps generated for test files contain relative paths that don't resolve anywhere.
 * This handler rewrites the sourcemaps to contain the correct absolute paths.
 */
class JsSourceMapPathRewriter(testServices: TestServices) : AbstractJsArtifactsCollector(testServices) {

    override fun processAfterAllModules(someAssertionWasFailed: Boolean) {
        val supportedTranslationModes = arrayOf(
            TranslationMode.FULL,
            TranslationMode.FULL_DCE_MINIMIZED_NAMES,
            TranslationMode.PER_MODULE,
            TranslationMode.PER_MODULE_DCE_MINIMIZED_NAMES,
        )
        val testModules = testServices.moduleStructure.modules
        val allTestFiles = testModules.flatMap { it.files }
        for (module in testModules) {
            for (mode in supportedTranslationModes) {
                val sourceMapFile =
                    File(JsEnvironmentConfigurator.getJsModuleArtifactPath(testServices, module.name, mode) + ".js.map")
                if (!sourceMapFile.exists()) continue

                val dependencies = JsEnvironmentConfigurator.getAllRecursiveDependenciesFor(module, testServices)
                SourceMap.replaceSources(sourceMapFile) { path ->
                    allTestFiles.find { it.name == path }?.originalFile?.absolutePath?.let {
                        return@replaceSources it
                    }

                    tryToMapLibrarySourceFile(dependencies, path)?.let {
                        return@replaceSources it
                    }

                    path
                }
            }
        }
    }

    /**
     * Some heuristics to find the library source file that this [sourceMapPath] should point to.
     * May not work in 100% of cases, but should be good enough for our tests.
     */
    private fun tryToMapLibrarySourceFile(dependencies: Iterable<ModuleDescriptor>, sourceMapPath: String): String? {
        for (dependency in dependencies) {
            val libraryFile = try {
                File(testServices.jsLibraryProvider.getPathByDescriptor(dependency))
            } catch (e: NoSuchElementException) {
                continue
            }

            val sourceRoot: File = libraryFile // libraries/stdlib/{js-ir-minimal-for-test|js-ir}/build/classes/kotlin/js/main
                .parentFile                    // libraries/stdlib/{js-ir-minimal-for-test|js-ir}/build/classes/kotlin/js/
                ?.parentFile                   // libraries/stdlib/{js-ir-minimal-for-test|js-ir}/build/classes/kotlin/
                ?.parentFile                   // libraries/stdlib/{js-ir-minimal-for-test|js-ir}/build/classes/
                ?.parentFile                   // libraries/stdlib/{js-ir-minimal-for-test|js-ir}/build/
                ?.parentFile                   // libraries/stdlib/{js-ir-minimal-for-test|js-ir}/
                ?: continue

            val searchPaths = listOf(sourceRoot, sourceRoot.resolve("build"))

            for (searchPath in searchPaths) {
                val resolved = searchPath.resolve(sourceMapPath)
                if (resolved.exists()) {
                    return resolved.absolutePath
                }
            }
        }
        return null
    }
}
