#!/bin/bash

################################################################################

# Java Library -- AIJ -- Compilation
#
# Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles the Java source files of AIJ without IntelliJ IDEA.
# It generated the class and jar files in the same places as IntelliJ IDEA does.
# It assumes that Java 10 is in the path.

################################################################################

# stop on error:
set -e

# generate class files:
javac -d java/out/production/AIJ java/src/edu/kestrel/acl2/aij/*.java

# generate jar file:
mkdir -p java/out/artifacts/AIJ_jar
jar cfM java/out/artifacts/AIJ_jar/AIJ.jar -C java/out/production/AIJ/ .
