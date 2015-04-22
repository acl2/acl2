#!/bin/sh

set -e

if [ ! -z "`git tag --contains HEAD | grep mac`" ]
then
    echo "Oops, looks like this version is already tagged:"
    git tag --contains HEAD
    exit 1
fi

if [ ! -z "`git diff --name-only`" ]
then
    echo "Oops, looks like you have uncommitted changes:"
    git status
    exit 1
fi

echo "Running mac tests."
./mac-test.sh

DATE=`date +"%F_%T" | sed 's/:/_/g'`
TAG="mac.$DATE"

echo "All mac tests passed."
echo "Collecting platform information..."

rm -f tagmessage
echo "All mac tests passed. " > tagmessage
./mac-info.sh | tee -a tagmessage

echo "Adding Git tag."
git tag -a $TAG -F tagmessage
rm tagmessage



