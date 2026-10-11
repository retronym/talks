/*
 * Zinc - The incremental compiler for Scala.
 * Copyright Scala Center, Lightbend, and Mark Harrah
 *
 * Licensed under Apache License 2.0
 * SPDX-License-Identifier: Apache-2.0
 *
 * See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.
 */

package sbt.internal.inc

class PackagePrefixImplicitsSpec extends UnitSpec:
  behavior of "PackageScope.packagePrefixImplicits"

  import PackageScope.packagePrefixImplicits

  it should "hold for Scala 2 unless a source feature drops package prefixes" in {
    packagePrefixImplicits("2.13.16", Nil) shouldBe true
    packagePrefixImplicits("2.12.20", Seq("-deprecation")) shouldBe true
    packagePrefixImplicits("2.13.16", Seq("-Xsource:3")) shouldBe true
    packagePrefixImplicits("2.13.16", Seq("-Xsource:3-cross")) shouldBe false
    packagePrefixImplicits("2.13.16", Seq("-Xsource:3", "-Xsource-features:_")) shouldBe false
    packagePrefixImplicits("2.13.16", Seq("-Xsource-features:leading-infix")) shouldBe true
    packagePrefixImplicits(
      "2.13.16",
      Seq("-Xsource-features:leading-infix,package-prefix-implicits")
    ) shouldBe false
    packagePrefixImplicits("2.13.16", Seq("-Xsource-features:v2.13.13")) shouldBe false
  }

  it should "hold for Scala 3 only under 3.0-migration" in {
    packagePrefixImplicits("3.7.1", Nil) shouldBe false
    packagePrefixImplicits("3.7.1", Seq("-source:3.0-migration")) shouldBe true
    packagePrefixImplicits("3.7.1", Seq("-source", "3.0-migration")) shouldBe true
  }
end PackagePrefixImplicitsSpec
