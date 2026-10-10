#!/usr/bin/env bash
# Renders the catalogue with the Classfile API (JDK 24+) and runs it on every JDK given.
# Usage: probes/jvm/probe.sh [cases.jsonl] -- JAVA_HOME...   (run from the lean directory)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cases=${1:-}
shift || true
[ "${1:-}" = "--" ] && shift
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
if [ -z "$cases" ]; then cases=$work/cases.jsonl; lake exe jvmcases > "$cases"; fi
render=${RENDER_JAVA_HOME:-$HOME/.sdkman/candidates/java/25.0.4-tem}
"$render/bin/javac" -d "$work/render" "$here/Render.java" "$here/Json.java"
"$render/bin/java" -cp "$work/render" Render "$cases" "$work/out"
"$render/bin/javac" --release 17 -d "$work/run" "$here/Run.java" "$here/Json.java" "$here/ProbeLog.java"
status=0
for jh in "$@"; do
  "$jh/bin/java" -cp "$work/run" Run "$cases" "$work/out" || status=1
done
exit $status
