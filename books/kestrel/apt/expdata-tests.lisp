; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "expdata")

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

(defmacro expdata (&rest args)
  `(apt::expdata ,@args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Schematic test 1.")

 (encapsulate
   (((oldp *) => *) ; old representation
    ((newp *) => *) ; new representation
    ((forth *) => *) ; conversion from old to new representation
    ((back *) => *) ; conversion from new to old representation
    ((a *) => *)   ; termination test
    ((b *) => *)   ; base of the recursion
    ((c * *) => *) ; combination of function argument with recursive call
    ((d *) => *)   ; decreasing of the function argument
    ((m *) => *)   ; measure of the function argument
    ((g *) => *))  ; guard of the function

   (set-ignore-ok t)
   (set-irrelevant-formals-ok t)

   (set-verify-guards-eagerness 1)

   (local (defun oldp (x) t)) ; all values
   (local (defun newp (x) t)) ; all values
   (local (defun forth (x) x)) ; identity conversion
   (local (defun back (x) x)) ; identity conversion

   (local (defun a (x) (zp x)))   ; 0 or not a natural number
   (local (defun b (x) nil))      ; anything, irrelevant
   (local (defun c (x y) nil))    ; anything, irrelevant
   (local (defun d (x) (1- x)))   ; decrement by 1
   (local (defun m (x) (nfix x))) ; argument, treated as natural number
   (local (defun g (x) (oldp x)))  ; all of the old representation

   ;; for the DEFSURJ applicability conditions:
   (defthm forth-image (implies (oldp x) (newp (forth x))))
   (defthm back-image (implies (newp x) (oldp (back x))))
   (defthm back-of-forth (implies (oldp x) (equal (back (forth x)) x)))

   ;; for the termination of F:
   (defthm o-p-of-m (o-p (m x)))
   (defthm o<-of-m (implies (not (a x)) (o< (m (d x)) (m x))))

   ;; for the guard verification of F:
   (defthm g-of-d (implies (and (g x) (not (a x))) (g (d x))))

   ;; for the EXPDATA applicability conditions:
   (defthm oldp-of-d (implies (and (oldp x) (not (a x))) (oldp (d x))))
   (defthm oldp-of-b (implies (and (oldp x) (a x)) (oldp (b x))))
   (defthm oldp-of-c (implies (and (oldp x) (oldp y)) (oldp (c x y))))
   (defthm oldp-when-g (implies (g x) (oldp x))))

 (defun f (x)
   (declare (xargs :guard (g x) :measure (m x)))
   (if (a x)
       (b x)
     (c x (f (d x)))))

 (defsurj surjmap newp oldp back forth)

 (expdata f (((x :result) surjmap)) :new-name f1)

 (must-be-redundant
  (defun f1 (x)
    (declare (xargs :guard (and (newp x) (g (back x)))
                    :measure (m (back x))
                    :ruler-extenders :all))
    (if (mbt$ (newp x))
        (if (a (back x))
            (forth (b (back x)))
          (forth (c (back x)
                    (back (f1 (forth (d (back x))))))))
      nil)))

 (must-be-redundant
  (defthm f-to-f1
    (implies (oldp x)
             (equal (f x)
                    (back (f1 (forth x)))))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Schematic test 2.")

 (encapsulate
   (((in-oldp *) => *) ; old input representation
    ((in-newp *) => *) ; new input representation
    ((in-forth *) => *) ; conversion from old to new input representation
    ((in-back *) => *) ; conversion from new to old input representation
    ((out-oldp *) => *) ; old output representation
    ((out-newp *) => *) ; new output representation
    ((out-forth *) => *) ; conversion from old to new output representation
    ((out-back *) => *) ; conversion from new to old output representation
    ((a *) => *)   ; termination test
    ((b *) => *)   ; base of the recursion
    ((c * *) => *) ; combination of function argument with recursive call
    ((d *) => *)   ; decreasing of the function argument
    ((m *) => *)   ; measure of the function argument
    ((g *) => *))  ; guard of the function

   (set-ignore-ok t)
   (set-irrelevant-formals-ok t)

   (set-verify-guards-eagerness 1)

   (local (defun in-oldp (x) t)) ; all values
   (local (defun in-newp (x) t)) ; all values
   (local (defun in-forth (x) x)) ; identity conversion
   (local (defun in-back (x) x)) ; identity conversion

   (local (defun out-oldp (x) t)) ; all values
   (local (defun out-newp (x) t)) ; all values
   (local (defun out-forth (x) x)) ; identity conversion
   (local (defun out-back (x) x)) ; identity conversion

   (local (defun a (x) (zp x)))   ; 0 or not a natural number
   (local (defun b (x) nil))      ; anything, irrelevant
   (local (defun c (x y) nil))    ; anything, irrelevant
   (local (defun d (x) (1- x)))   ; decrement by 1
   (local (defun m (x) (nfix x))) ; argument, treated as natural number
   (local (defun g (x) (in-oldp x)))  ; all of the old representation

   ;; for the input DEFSURJ applicability conditions:
   (defthm in-forth-image (implies (in-oldp x)
                                   (in-newp (in-forth x))))
   (defthm in-back-image (implies (in-newp x)
                                  (in-oldp (in-back x))))
   (defthm in-back-of-forth (implies (in-oldp x)
                                     (equal (in-back (in-forth x)) x)))

   ;; for the output DEFSURJ applicability conditions:
   (defthm out-forth-image (implies (out-oldp x)
                                    (out-newp (out-forth x))))
   (defthm out-back-image (implies (out-newp x)
                                   (out-oldp (out-back x))))
   (defthm out-back-of-forth (implies (out-oldp x)
                                      (equal (out-back (out-forth x)) x)))

   ;; for the termination of F:
   (defthm o-p-of-m (o-p (m x)))
   (defthm o<-of-m (implies (not (a x)) (o< (m (d x)) (m x))))

   ;; for the guard verification of F:
   (defthm g-of-d (implies (and (g x) (not (a x))) (g (d x))))

   ;; for the EXPDATA applicability conditions:
   (defthm oldp-of-d (implies (and (in-oldp x) (not (a x)))
                              (in-oldp (d x))))
   (defthm oldp-of-b (implies (and (in-oldp x) (a x))
                              (out-oldp (b x))))
   (defthm oldp-of-c (implies (and (in-oldp x) (out-oldp y))
                              (out-oldp (c x y))))
   (defthm oldp-when-g (implies (g x) (in-oldp x))))

 (defun f (x)
   (declare (xargs :guard (g x) :measure (m x)))
   (if (a x)
       (b x)
     (c x (f (d x)))))

 (defsurj in-surjmap in-newp in-oldp in-back in-forth)

 (defsurj out-surjmap out-newp out-oldp out-back out-forth)

 (expdata f ((x in-surjmap) (:result out-surjmap)) :new-name f1)

 (must-be-redundant
  (defun f1 (x)
    (declare (xargs :guard (and (in-newp x) (g (in-back x)))
                    :measure (m (in-back x))
                    :ruler-extenders :all))
    (if (mbt$ (in-newp x))
        (if (a (in-back x))
            (out-forth (b (in-back x)))
          (out-forth (c (in-back x)
                        (out-back (f1 (in-forth (d (in-back x))))))))
      nil)))

 (must-be-redundant
  (defthm f-to-f1
    (implies (in-oldp x)
             (equal (f x)
                    (out-back (f1 (in-forth x)))))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Transform from osets to lists.")

 (include-book "std/osets/top" :dir :system)

 ;; surjection from lists to osets:
 (defsurj lists-to-osets true-listp set::setp set::mergesort identity)

 ;; filter oset to keep only its integer elements:
 (define f ((x set::setp))
   :returns (new-x set::setp)
   (cond ((set::empty x) nil)
         (t (let ((e (set::head x)))
              (if (integerp e)
                  (set::insert e (f (set::tail x)))
                (f (set::tail x))))))
   :verify-guards :after-returns)

 ;; transform argument:
 (expdata f ((x lists-to-osets)))

 ;; transform result:
 (expdata f ((:result lists-to-osets)))

 ;; transform argument and result:
 (expdata f (((x :result) lists-to-osets))))
