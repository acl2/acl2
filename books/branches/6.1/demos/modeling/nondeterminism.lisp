; A simple example of how to model nondeterminism in ACL2 using the
; encapsulate feature.

; Copyright David Rager 2012.

(in-package "ACL2")

(encapsulate

; Declare the signature of foo, so that foo can be exported.  Think of this as
; a C header file.

 (((foo) => *))

; Define a non-exported definition of foo, which will be thrown away after the
; scope of the encapsulate is exited.  This definition serves as a "witness" to
; ACL2, which allows us to soundly proclaim that a function named foo with the
; properties we will later specify can actually exist.

 (local (defun foo () t))

; Define the properties of foo that we want exported and to be available
; beyond the scope of the encapsulate.

 (defthm foo-result
   (booleanp (foo)))

 ) ; end encapsulate

(local 
 (defthm foo-returns-atom-lemma
   (implies (booleanp x)
            (atom x))))

; We now have a non-deterministic function named foo that is only known to
; return a t or nil.  This function is admitted into the logic, and we can
; reason about it, but we can not execute it.

(defthm foo-returns-atom
  (atom (foo))
  :hints (("Goal" :in-theory (disable atom))))

(include-book "make-event/eval" :dir :system) ; define must-fail

(must-fail
 (thm (equal (foo) t)))