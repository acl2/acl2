; Simple Programming Language Imp Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SIMPL-IMP")

(include-book "interpreter")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; add x and y into z:

(defconst *add*
  (list (comm-asg "z" (aexp-add (aexp-var "x")
                                (aexp-var "y")))))

(assert-equal (omap::in "z" (exec (config *add* '(("x" . 1) ("y" . 2)))))
              '("z" . 3))

(assert-equal (omap::in "z" (exec (config *add* '(("x" . 63) ("y" . -12)))))
              '("z" . 51))

(assert-equal (omap::in "z" (exec (config *add* '(("x" . 4)))))
              '("z" . 4))

(assert-equal (omap::in "z" (exec (config *add* '(("y" . -64)))))
              '("z" . -64))

(assert-equal (omap::in "z" (exec (config *add* nil)))
              '("z" . 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; max of x and y into m:

(defconst *max*
  (list (comm-if (bexp-less (aexp-var "x")
                            (aexp-var "y"))
                 (list (comm-asg "m" (aexp-var "y")))
                 (list (comm-asg "m" (aexp-var "x"))))))

(assert-equal (omap::in "m" (exec (config *max* '(("x" . 284) ("y" . 399)))))
              '("m" . 399))

(assert-equal (omap::in "m" (exec (config *max* '(("x" . -23) ("y" . -1000)))))
              '("m" . -23))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; factorial of n into r:

(defconst *fact*
  (list (comm-asg "r" (aexp-const 1))
        (comm-while (bexp-less (aexp-const 0)
                               (aexp-var "n"))
                    (list (comm-asg "r" (aexp-mul (aexp-var "r")
                                                  (aexp-var "n")))
                          (comm-asg "n" (aexp-add (aexp-var "n")
                                                  (aexp-const -1)))))))

(assert-equal (omap::in "r" (exec (config *fact* '(("n" . 0)))))
              '("r" . 1))

(assert-equal (omap::in "r" (exec (config *fact* '(("n" . 1)))))
              '("r" . 1))

(assert-equal (omap::in "r" (exec (config *fact* '(("n" . 2)))))
              '("r" . 2))

(assert-equal (omap::in "r" (exec (config *fact* '(("n" . 3)))))
              '("r" . 6))

(assert-equal (omap::in "r" (exec (config *fact* '(("n" . 5)))))
              '("r" . 120))

(assert-equal (omap::in "r" (exec (config *fact* '(("n" . 10)))))
              '("r" . 3628800))
