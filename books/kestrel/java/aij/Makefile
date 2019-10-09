# Java Library
#
# Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles the Java source files of AIJ without IntelliJ IDEA.
# It generates the class and jar files in the same places as IntelliJ IDEA does.

# This file also generates Javadoc documentation
# for public, package-private, and private classes and members
# (not for protected classes and members
# because AIJ currently does not have any).
# The generated documentation goes into the directories
# javadoc-public, javadoc-package, and javadoc-private,
# from where it can be opened in a browser.

# This file also certifies the ACL2 files in this directory,
# which currently just consist of XDOC documentation for AIJ.
# Note that the ACL2 files do not depend on the Java-related files,
# and that the Java-related files do not depend on the ACL2 files.
# This file does not assume cert.pl and clean.pl to be in the path:
# it references them via a relative path from this directory.

# This file assumes that OpenJDK Java 12 is in the path,
# but it may well work with other Java versions or implementations.

################################################################################

all: aij doc-all acl2-files

aij: java/out/artifacts/AIJ_jar/AIJ.jar

java/out/artifacts/AIJ_jar/AIJ.jar: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate class files:"
	mkdir -p java/out/production/AIJ
	javac -d java/out/production/AIJ java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate jar file:"
	mkdir -p java/out/artifacts/AIJ_jar
	jar cfm java/out/artifacts/AIJ_jar/AIJ.jar java/META-INF/MANIFEST.MF -C java/out/production/AIJ/ .

doc-all: doc-public doc-package doc-private

doc-public: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate public Javadoc documentation:"
	javadoc -d javadoc-public -public java/src/edu/kestrel/acl2/aij/*.java

doc-package: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate package Javadoc documentation:"
	javadoc -d javadoc-package -package java/src/edu/kestrel/acl2/aij/*.java

doc-private: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate private Javadoc documentation:"
	javadoc -d javadoc-private -private java/src/edu/kestrel/acl2/aij/*.java

acl2-files: *.lisp
	@echo "Certify ACL2 files:"
	../../../build/cert.pl *.lisp

clean:
	@echo "Delete class files and jar file:"
	/bin/rm -rf java/out
	@echo "Delete Javadoc HTML files:"
	/bin/rm -rf javadoc-public
	/bin/rm -rf javadoc-package
	/bin/rm -rf javadoc-private
	@echo "Delete ACL2 certification files:"
	../../../build/clean.pl
