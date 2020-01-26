; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial

  :parents (atj)

  :short "ATJ tutorial."

  :long

  (xdoc::topstring

   (xdoc::p
    "This tutorial is work in progress,
     but it may be already useful in its current incomplete form.
     This tutorial's goal is to provide user-level information
     on how ATJ works and how to use ATJ effectively.
     The ATJ reference documentation is "
    (xdoc::seeurl "atj" "here")
    ", along with some additional information
     that will likely be moved to this tutorial.")

   (xdoc::p
    "The subtopics of this manual page
     may be navigated sequentially,
     using the `next' and `previous' links.")

   (xdoc::p
    "Start: "
    (xdoc::seetopic "atj-tutorial-motivation" "Motivation"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-motivation

  :parents (atj-tutorial)

  :short "ATJ tutorial: Motivation."

  :long

  (xdoc::topstring

   (xdoc::p
    "A benefit of writing code in a theorem prover like ACL2
     is the ability to prove properties about it,
     such as the satisfaction of requirements specifications.
     A facility to generate code in one or more programming languages
     from an executable subset of the prover's logical language
     enables the possibly verified code to run as, and interoperate with,
     code written in those programming languages.
     Assuming the correctness of code generation
     (whose verification is a separable problem,
     akin to compilation verification)
     the properties proved about the original code
     carry over to the generated code.")

   (xdoc::p
    "ACL2's tight integration with the underlying Lisp platform
     enables the executable subset of the ACL2 logical language
     to run readily and efficiently as Lisp,
     without the need for explicit code generation facilities.
     Nonetheless, some situations may call for
     running ACL2 code in other programming languages:
     specifically, when the ACL2 code must interoperate
     with external code in those programming languages
     in a more integrated and efficient way than afforded
     by inter-language communication via foreign function interfaces
     such as "
    (xdoc::ahref "https://common-lisp.net/project/cffi" "CFFI")
    " and "
    (xdoc::ahref "https://docs.oracle.com/javase/10/docs/specs/jni" "JNI")
    " or by inter-process communication with the ACL2/Lisp runtime
     via mechanisms like "
    (xdoc::seetopic "acl2::bridge" "the ACL2 Bridge")
    ". Using Lisp implementations
     written in the target programming languages,
     such as "
    (xdoc::ahref "https://abcl.org" "ABCL")
    ", involves not only porting ACL2 to them,
     but also including much more runtime code
     than necessary for the target applications.
     Compilers from Lisp to the target programming languages
     may need changes or wrappers,
     because executable ACL2 is not quite a subset of Lisp;
     furthermore, the ability to compile non-ACL2 Lisp code
     is an unnecessary complication as far as ACL2 compilation is concerned,
     making potential verification harder.")

   (xdoc::p
    "ATJ translates ACL2 to Java,
     enabling possibly verified ACL2 code
     to run as, and interoperate with, Java code,
     without much of the ACL2 framework or any of the Lisp runtime.")

   (xdoc::p
    "ATJ is useful
     to generate Java code at the end of an "
    (xdoc::seetopic "apt::apt" "APT")
    " program synthesis derivation.")

   (xdoc::p
    "Generators for ACL2 of code in other programming languages (than Java)
     may be developed similarly to ATJ.")))
