# Java Library -- AIJ -- Compilation
#
# Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles the Java source files of AIJ without IntelliJ IDEA.
# It generates the class and jar files in the same places as IntelliJ IDEA does.
# It assumes that OpenJDK Java 12 is in the path,
# but it may well work with other Java versions or implementations.

################################################################################

aij: java/out/artifacts/AIJ_jar/AIJ.jar

java/out/artifacts/AIJ_jar/AIJ.jar: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate class files:"
	mkdir -p java/out/production/AIJ
	javac -d java/out/production/AIJ java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate jar file:"
	mkdir -p java/out/artifacts/AIJ_jar
	jar cfM java/out/artifacts/AIJ_jar/AIJ.jar -C java/out/production/AIJ/ .

clean:
	@echo "Delete class files and jar file:"
	/bin/rm -rf java/out
