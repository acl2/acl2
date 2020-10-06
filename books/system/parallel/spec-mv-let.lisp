(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defun foo (z)
  (declare (xargs :verify-guards nil
                  :guard (acl2-numberp z)))
  (spec-mv-let
   (x y)
   (mv 3 4)
   (mv-let (a b)
     (mv 5 7)
     (if (equal a z)
         (+ x y a b z)
       (+ a b)))))

(assert! (equal (foo 5) 24))
(assert! (equal (foo 1) 12))

(verify-guards foo)

(assert! (equal (foo 5) 24))
(assert! (equal (foo 1) 12))

(must-fail
; Incorrectly uses X in the false branch.
 (defun boozo (z)
   (spec-mv-let
    (x y)
    (mv 3 4)
    (mv-let (a b)
      (mv 5 7)
      (if (equal a z)
          (+ x y a b z)
        (+ a b x))))))

(must-fail
; Incorrectly uses x in the test
 (defun boozo (z)
   (spec-mv-let
    (x y)
    (mv 3 4)
    (mv-let (a b)
      (mv 5 7)
      (if (equal a x)
          (+ x y a b z)
        (+ a b))))))

(defun foo2 (z)

; Test that we can rebind speculated variables inside the branch that has to
; recompute the speculative variables' values.

  (declare (xargs :verify-guards nil
                  :guard (acl2-numberp z)))
  (spec-mv-let
   (x y)
   (mv 3 4)
   (mv-let (a b)
     (mv 5 7)
     (if (equal a z)
         (+ x y a b z)
       (mv-let (x y)
               (mv 10 11)
               (+ a b x y z))))))

(assert! (equal (foo2 5) 24))
(assert! (equal (foo2 4) 37))

(verify-guards foo2)

(assert! (equal (foo2 5) 24))
(assert! (equal (foo2 4) 37))

(must-fail

; Incorrectly uses "the-very-obscure-future", which is used in our raw Lisp
; definition of spec-mv-let.

 (defun boozo (the-very-obscure-future)
   (spec-mv-let
    (x y)
    (mv 3 4)
    (mv-let (a b)
      (mv 5 7)
      (if (equal the-very-obscure-future 4)
          (+ x y a b)
        (+ 7 8))))))

(must-fail
; Incorrectly omits a test for the spec-mv-let.
 (defun boozo (z)
   (spec-mv-let
    (x y)
    (mv 3 4)
    (mv-let (a b)
      (mv 5 7)
      (list (equal a z)
            (+ x y a b z))))))

(must-fail

; Incorrectly uses a "z" that we define to be ambiguous (if we decided to
; disambiguate the "z", it would have to refer to the given argument).  Note
; that the given error message is different for this definition than in the
; following one.

 (defun boozo (z)
   (spec-mv-let
    (z y)
    (mv 3 4)
    (mv-let (a b)
      (mv 5 7)
      (if (equal a z)
          (+ y a b)
        (+ a b))))))

(must-fail

; Incorrectly uses a "z" that we define to be ambiguous (if we decided to
; disambiguate the "z", it would have to refer to the given argument).  Note
; that the given error message is different for this definition than in the
; following one.

 (defun boozo (z)
   (spec-mv-let
    (z y)
    (mv 3 4)
    (mv-let (a b)
      (mv 5 7)
      (if (equal a 5)
          (+ y a b)
        (+ z a b))))))

(must-fail ; overlapping inner and outer variables
 (encapsulate
  ()
  (set-ignore-ok t)
  (defun foo3 ()
    (spec-mv-let
     (x)
     17
     (mv?-let (x)
              23
              (if t
                  (+ x x)
                "bad"))))))

(assert!
 (not (let ((a t)
            (xval nil))
        (spec-mv-let (yval)
                     xval
                     (mv?-let (xval)
                              a
                              (if xval
                                  yval
                                nil))))))
