#!/bin/bash

set -e

#NEXT_BUILD_NUMBER=`cat /var/lib/jenkins/jobs/${BUILD_NAME}/nextBuildNumber`
#LAST_BUILD_NUMBER=$((NEXT_BUILD_NUMBER-1))

#LAST_BUILD_LOG_FILENAME=/var/lib/jenkins/jobs/${BUILD_NAME}/builds/${LAST_BUILD_NUMBER}/log
LAST_BUILD_LOG_FILENAME=/var/lib/jenkins/jobs/${JOB_NAME}/builds/${BUILD_NUMBER}/log
echo "LAST_BUILD_LOG_FILENAME=${LAST_BUILD_LOG_FILENAME}"

FAILED=$(grep "error: failed to push some refs" ${LAST_BUILD_LOG_FILENAME})

if [ -n "$FAILED" ]; then
    curl http://leeroy.defthm.com/job/${JOB_NAME}/build?token=${JENKINS_BUILD_TOKEN}&cause=automatically-merge-from-master-upon-failed-build-script
fi
