; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "fold-returns")
(include-book "tailrec-elimination")
(include-book "lift-loop-tests")
(include-book "remove-continue")
(include-book "remove-array-write-calls")
(include-book "simplify-conds")
(include-book "cache-const-methods")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation
  :parents (atj-code-generation)
  :short "Post-translation performed by ATJ, as part of code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see atj-code-generation),
     after translating ACL2 to Java,
     ATJ performs a Java-to-Java post-translation.
     Currently, this post-translation consists of the following steps.
     These steps only apply to the shallow embedding approach.")
   (xdoc::ol
    (xdoc::li
     "We fold @('return') statements into @('if') branches.
      See "
     (xdoc::seetopic "atj-post-translation-fold-returns" "here")
     ".")
    (xdoc::li
     "We eliminate tail recursions, replacing them with loops.
      See "
     (xdoc::seetopic "atj-post-translation-tailrec-elimination" "here")
     ".")
    (xdoc::li
     "We lift tests from conditionals to loops.
      See "
     (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
     ".")
    (xdoc::li
     "We eliminate unnecessary @('continue')s from loops.
      See "
     (xdoc::seetopic "atj-post-translation-remove-continue" "here")
     ".")
    (xdoc::li
     "We eliminate calls of the Java primitive array writing methods.
      See "
     (xdoc::seetopic "atj-post-translation-remove-array-write-calls" "here")
     ".")
    (xdoc::li
     "We simplify conditional expressions with true or false tests.
      See "
     (xdoc::seetopic "atj-post-translation-simplify-conds" "here")
     ".")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-post-translate-body ((name stringp)
                                 (params jparam-listp)
                                 (body jblockp)
                                 (tailrecp booleanp))
  :returns (new-body jblockp :hyp :guard)
  :short "Post-translate a Java method body generated from an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We always fold @('return')s into @('if')s.")
   (xdoc::p
    "If the method is tail-recursive,
     which is signaled by the @('tailrecp') flag,
     then we replace the tail recursion with a loop.
     It is critical that this step is performed
     after folding @('return')s into @('if')s,
     because tail recursion elimination
     looks for recursive calls in @('return')s.")
   (xdoc::p
    "The other post-translation steps are always performed.
     These are the post-translation steps that operate
     at the level of individual method bodies."))
  (b* ((body (atj-fold-returns body))
       (body (if tailrecp
                 (atj-elim-tailrec name params body)
               body))
       (body (atj-lift-loop-test body))
       (body (atj-remove-continue-in-jblock body))
       (body (atj-remove-array-write-calls body))
       (body (atj-simplify-conds-in-jblock body)))
    body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-post-translate-jcbody-elements ((elems jcbody-element-listp))
  :returns (new-elems jcbody-element-listp)
  :short "Post-translate a list of Java class body elements."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this consists of a single operation,
     but it may be extended in the future."))
  (atj-cache-const-methods elems))
