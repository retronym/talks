#!/usr/bin/env bash
# MiMa on the Scala catalogue (Scala/Catalogue.lean): writes each case's library sources, compiles
# v0 and v1 separately with scalac, and runs MiMa on the two class directories.
# Usage: probes/mima/scala.sh OUT [scala-version]   (run from the lean directory)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1
sv=${2:-2.13.18}
mkdir -p "$out"
lake exe bincompat scala "$out" > "$out/cases.tsv"
cut -f1 "$out/cases.tsv" | while read -r name; do
  for v in v0 v1; do
    rm -rf "$out/$name/$v" && mkdir -p "$out/$name/$v"
    coursier launch "org.scala-lang:scala-compiler:$sv" -M scala.tools.nsc.Main -- -usejavacp -d "$out/$name/$v" "$out/$name/$v.scala"
  done
done
scala-cli run --server=false "$here/Mima.scala" -- "$out" $(cut -f1 "$out/cases.tsv")
