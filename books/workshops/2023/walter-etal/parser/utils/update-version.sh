#!/usr/bin/env bash

DIR="$(dirname "${BASH_SOURCE[0]}")"
NEWVERSION=$1

if [ $# -eq 0 ]; then
    echo "Must provide a new version number!"
    echo "USAGE: update-version.sh NEW_VERSION"
    exit 1
fi

if [[ ! $NEWVERSION =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "Must provide a valid version number, consisting of three integers separated by periods."
    exit 1
fi

cd $DIR/..

mvn -Dtycho.mode=maven org.eclipse.tycho:tycho-versions-plugin:3.0.3:set-version -DnewVersion=$NEWVERSION-SNAPSHOT
echo $NEWVERSION > version.txt
sed -E -e "0,/<version>[^<]+<\\/version>/{s//<version>$NEWVERSION-SNAPSHOT<\\/version>/}" pom.xml
