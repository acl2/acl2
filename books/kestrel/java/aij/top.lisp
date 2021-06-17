; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc aij
  :parents (java)
  :short "AIJ (<b>A</b>CL2 <b>I</b>n <b>J</b>ava)
          is a deep embedding of ACL2 in Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "AIJ is a deep embedding in Java
     of an executable, side-effect-free, non-stobj-accessing
     subset of the ACL2 language without guards.")
   (xdoc::p
    "AIJ is realized as a Java package that includes
     Java representations of all the ACL2 values,
     Java implementations of all the ACL2 primitive functions,
     and an interpreter that evaluates
     ACL2 "
    (xdoc::seetopic "acl2::term" "translated terms")
    " to ACL2 values.
     The interpreter evaluates terms ``in the logic'',
     without "
    (xdoc::seetopic "acl2::guard-checking" "checking guards")
    " and without side effects.
     The interpreter evaluates @(tsee if) non-strictly.
     The interpreter can be invoked only on
     (Java representations of) concrete ACL2 values,
     not on global variables
     like @(tsee state) and user-defined "
    (xdoc::seetopic "acl2::stobj" "stobjs")
    ".")
   (xdoc::p
    "AIJ is in the @('java') subdirectory of this directory,
     which contains an "
    (xdoc::ahref "https://www.jetbrains.com/idea" "IntelliJ IDEA")
    " project.
     The Java code is thoroughly documented with Javadoc.
     AIJ is in a Java package called @('edu.kestrel.acl2.aij').")
   (xdoc::p
    "The Java source files of AIJ may be edited either in IntelliJ IDEA
     or in a text editor like Emacs.
     These source files can be compiled either in IntelliJ IDEA
     or via the @('Makefile') file in this directory,
     which generates class and jar files in the same place
     where IntelliJ IDEA does.
     This @('Makefile') also generates Javadoc HTML documentation.")
   (xdoc::p
    "AIJ is written in Java 8,
     which means that it can be compiled
     using a compiler for Java 8 or later.
     The aforementioned @('Makefile') assumes that
     a Java 8 (or later) compiler and related tools (e.g. the latest OpenJDK)
     is in the path.")))
