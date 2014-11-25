; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; These tests are taken from Community Book
; books/defexec/dag-unification/dag-unification-st.lisp.

(cond ((and (mv-let (a1 a2)
                    (dag-mgu '(f x x) '(f (h y) z))
                    (equal (list a1 a2)
                           '(T ((Z H Y) (X H Y)))))
            (mv-let (a1 a2)
                    (dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h u) v)))
                    (equal (list a1 a2)
                           '(T ((V H (H Z)) (U H Z) (X H Z)))))
            (mv-let (a1 a2)
                    (dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h y) v)))
                    (equal (list a1 a2)
                           '(T ((V H U) (Y H Z) (X H Z)))))
            (mv-let (a1 a2)
                    (dag-mgu '(f y x) '(f (k x) y))
                    (equal (list a1 a2)
                           '(NIL NIL))))
       (print "SUCCESS"))
      (t (print "FAILED")))
