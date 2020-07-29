#!/bin/bash

set -e

NEXT_BUILD_NUMBER=`cat /var/lib/jenkins/jobs/${BUILD_NAME}/nextBuildNumber`
LAST_BUILD_NUMBER=$((NEXT_BUILD_NUMBER-1))

LAST_BUILD_LOG_FILENAME=/var/lib/jenkins/jobs/${BUILD_NAME}/builds/${LAST_BUILD_NUMBER}/log

FAILED=$(grep "error: failed to push some refs" ${LAST_BUILD_LOG_FILENAME})

if [ -n "$FAILED" ]; then
    curl http://leeroy.defthm.com/job/github-update-testing-kestrel-branch-with-master/build?token=${JENKINS_TOKEN}&cause=automatically-merge-from-master-upon-failed-build-script
fi
