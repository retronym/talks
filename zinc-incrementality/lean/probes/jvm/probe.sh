#!/usr/bin/env bash
# Renders the catalogue with the Classfile API (JDK 24+) and runs it on every JDK given.
# Usage: probes/jvm/probe.sh [cases.jsonl] -- JAVA_HOME...   (run from the lean directory)
# With OUT=dir, the rendered classfiles are kept in dir/<case>/{v0,v1,client,sites} (for MiMa, track B).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cases=${1:-}
shift || true
[ "${1:-}" = "--" ] && shift
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
out=${OUT:-$work/out}
if [ -z "$cases" ]; then cases=$work/cases.jsonl; lake exe jvmcases > "$cases"; fi
render=${RENDER_JAVA_HOME:-$HOME/.sdkman/candidates/java/25.0.4-tem}
"$render/bin/javac" -d "$work/render" "$here/Render.java" "$here/Json.java"
"$render/bin/java" -cp "$work/render" Render "$cases" "$out"
"$render/bin/javac" --release 17 -d "$work/run" "$here/Run.java" "$here/Json.java" "$here/ProbeLog.java"
status=0
for jh in "$@"; do
  "$jh/bin/java" -cp "$work/run" Run "$cases" "$out" || status=1
done
exit $status
