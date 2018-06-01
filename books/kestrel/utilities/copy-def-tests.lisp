; Character Utilities -- Tests
;
; Copyright (C) 2018, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

; Feel free to add more tests and add to the credits above!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "copy-def")

(defmacro local-test (&rest args)
  `(local (encapsulate () (local (progn ,@args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-test

 (defun foo (x) (cons x x))
 (defun bar (x) (cons x x))
 (mutual-recursion
  (defun f1 (x)
    (if (foo x) (bar x) (if (consp x) (f2 (cdr x)) x)))
  (defun f2 (x)
    (if (foo x) (bar x) (if (consp x) (f1 (cdr x)) x))))
 (include-book "misc/install-not-normalized" :dir :system)
 (install-not-normalized f1)
 (install-not-normalized f2)
 (copy-def f1)

; These are now redundant.

 (DEFTHM F1-COPY-DEF
   (EQUAL (F1-COPY X)
          (IF (FOO X)
              (BAR X)
              (IF (CONSP X) (F2-COPY (CDR X)) X)))
   :RULE-CLASSES
   ((:DEFINITION
     :INSTALL-BODY T
     :CLIQUE (F1-COPY F2-COPY)
     :CONTROLLER-ALIST ((F1-COPY T) (F2-COPY T)))))

 (DEFTHM F2-COPY-DEF
   (EQUAL (F2-COPY X)
          (IF (FOO X)
              (BAR X)
              (IF (CONSP X) (F1-COPY (CDR X)) X)))
   :RULE-CLASSES
   ((:DEFINITION
     :INSTALL-BODY T
     :CLIQUE (F1-COPY F2-COPY)
     :CONTROLLER-ALIST ((F1-COPY T) (F2-COPY T)))))

 (DEFTHM F1-IS-F1-COPY
   (EQUAL (F1 X) (F1-COPY X))
   :RULE-CLASSES NIL)

 (DEFTHM F2-IS-F2-COPY
   (EQUAL (F2 X) (F2-COPY X))
   :RULE-CLASSES NIL)
 )

