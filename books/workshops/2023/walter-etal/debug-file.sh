#!/usr/bin/env bash

DIR="$(dirname "${BASH_SOURCE[0]}")"
VERSION=$(<$DIR/parser/version.txt)
JAR="$DIR/parser/org.neu.acl2.handproof.cli/build/libs/org.neu.acl2.handproof.cli-$VERSION-SNAPSHOT-all.jar"
FILE=$1

if [ $# -eq 0 ]; then
    echo "Must provide an input file!"
    echo "USAGE: debug-file.sh FILE"
    exit 1
fi

if [ ! -f "$FILE" ]; then
    echo "The given file, \"$FILE\", does not exist."
    exit 1
fi

if [ ! -f "$JAR" ]; then
    echo "You need to build the parser CLI first. Try \"make parser-cli\"."
    exit 1
fi


if [ ! -f "$DIR/prover-debug" ]; then
    echo "You need to build the prover-debug lisp image first. Try \"make build-debug-binary\"."
    exit 1
fi

# Borrowed from https://github.com/nextflow-io/nextflow/blob/master/launch.sh
JAVA_BIN=java
JAVA_VER="$($JAVA_BIN -version 2>&1)"
if [ $? -ne 0 ]; then
    echo "${JAVA_VER:-Failed to launch Java}"
    exit 1
fi
# This incantation from https://odoepner.wordpress.com/2014/07/27/get-java-version-string-via-shell-commands/
JAVA_VER=$(echo "$JAVA_VER" \
               | head -1 \
               | cut -d'"' -f2 \
               | sed 's/^1\.//' \
               | cut -d'.' -f1)
if [[ $JAVA_VER -lt 17 ]]; then
    echo "Error: cannot find Java or it's the wrong version -- please make sure that Java 17 or higher is installed"
    exit 1
fi
JVM_ARGS+=" --add-opens java.base/java.lang=ALL-UNNAMED"

rm -f output.lisp
rm -f debug-output.log

PROVE_FILE_SH="$DIR/prove-file-java.sh" "$JAVA_BIN" $JVM_ARGS -jar "$JAR" "$FILE" -g -o output.lisp --no-full
"$DIR/prover-debug" output.lisp
