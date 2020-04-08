; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "isodata")

(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-verify-guards-eagerness 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

(defmacro isodata (&rest args)
  `(apt::isodata ,@args))

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

   ;; for the DEFISO applicability conditions:
   (defthm forth-image (implies (oldp x) (newp (forth x))))
   (defthm back-image (implies (newp x) (oldp (back x))))
   (defthm back-of-forth (implies (oldp x) (equal (back (forth x)) x)))
   (defthm forth-of-back (implies (newp x) (equal (forth (back x)) x)))

   ;; for the termination of F:
   (defthm o-p-of-m (o-p (m x)))
   (defthm o<-of-m (implies (not (a x)) (o< (m (d x)) (m x))))

   ;; for the guard verification of F:
   (defthm g-of-d (implies (and (g x) (not (a x))) (g (d x))))

   ;; for the ISODATA applicability conditions:
   (defthm oldp-of-d (implies (and (oldp x) (not (a x))) (oldp (d x))))
   (defthm oldp-of-b (implies (and (oldp x) (a x)) (oldp (b x))))
   (defthm oldp-of-c (implies (and (oldp x) (oldp y)) (oldp (c x y))))
   (defthm oldp-when-g (implies (g x) (oldp x))))

 (defun f (x)
   (declare (xargs :guard (g x) :measure (m x)))
   (if (a x)
       (b x)
     (c x (f (d x)))))

 (defiso isomap oldp newp forth back)

 (apt::isodata f (((x :result) isomap)) :new-name f1)

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
  (defthm f-~>-f1
    (implies (oldp x)
             (equal (f x)
                    (back (f1 (forth x))))))))

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

   ;; for the input DEFISO applicability conditions:
   (defthm in-forth-image (implies (in-oldp x)
                                   (in-newp (in-forth x))))
   (defthm in-back-image (implies (in-newp x)
                                  (in-oldp (in-back x))))
   (defthm in-back-of-forth (implies (in-oldp x)
                                     (equal (in-back (in-forth x)) x)))
   (defthm in-forth-of-back (implies (in-newp x)
                                     (equal (in-forth (in-back x)) x)))

   ;; for the output DEFISO applicability conditions:
   (defthm out-forth-image (implies (out-oldp x)
                                    (out-newp (out-forth x))))
   (defthm out-back-image (implies (out-newp x)
                                   (out-oldp (out-back x))))
   (defthm out-back-of-forth (implies (out-oldp x)
                                      (equal (out-back (out-forth x)) x)))
   (defthm out-forth-of-back (implies (out-newp x)
                                      (equal (out-forth (out-back x)) x)))

   ;; for the termination of F:
   (defthm o-p-of-m (o-p (m x)))
   (defthm o<-of-m (implies (not (a x)) (o< (m (d x)) (m x))))

   ;; for the guard verification of F:
   (defthm g-of-d (implies (and (g x) (not (a x))) (g (d x))))

   ;; for the ISODATA applicability conditions:
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

 (defiso in-isomap in-oldp in-newp in-forth in-back)

 (defiso out-isomap out-oldp out-newp out-forth out-back)

 (apt::isodata f ((x in-isomap) (:result out-isomap)) :new-name f1)

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
  (defthm f-~>-f1
    (implies (in-oldp x)
             (equal (f x)
                    (out-back (f1 (in-forth x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check OLD input.")

 ;; OLD is not a symbol:
 (must-fail (isodata 78 ((arg (oldp newp forth back)))))
 (must-fail (isodata 78 ((arg iso))))

 ;; OLD does not exist:
 (must-fail (isodata fffffffff ((arg (oldp newp forth back)))))
 (must-fail (isodata fffffffff ((arg iso))))

 ;; OLD is not a function:
 (must-fail (isodata car-cdr-elim ((arg (oldp newp forth back)))))
 (must-fail (isodata car-cdr-elim ((arg iso))))

 ;; OLD does not resolve to a function:
 (must-fail (isodata gggggg{*} ((arg (oldp newp forth back)))))
 (must-fail (isodata gggggg{*} ((arg iso))))

 ;; OLD is in program mode:
 (must-succeed*
  (defun f (x) (declare (xargs :mode :program)) x)
  (must-fail (isodata f ((arg (oldp newp forth back)))))
  (must-fail (isodata f ((arg iso)))))

 ;; OLD is not defined:
 (must-fail (isodata cons ((arg (oldp newp forth back)))))
 (must-fail (isodata cons ((arg iso))))

 ;; OLD is mutually recursive:
 (must-fail (isodata pseudo-termp ((arg (oldp newp forth back)))))
 (must-fail (isodata pseudo-termp ((arg iso))))

 ;; OLD has :? as measure:
 (must-succeed*
  (encapsulate
    ()
    (local (defun m (x) (acl2-count x)))
    (local (defun f (x)
             (declare (xargs :measure (m x)))
             (if (atom x) nil (f (car x)))))
    (defun f (x)
      (declare (xargs :measure (:? x)))
      (if (atom x) nil (f (car x)))))
  (must-fail (isodata f ((arg (oldp newp forth back)))))
  (must-fail (isodata f ((arg iso)))))

 ;; OLD occurs in the contexts or arguments of a recursive call:
 (must-succeed*
  ;; :PREDICATE is NIL:
  (must-succeed*
   (defun f (x)
     (declare (xargs :guard (natp x)))
     (if (zp x)
         nil
       (and (f (1- x))
            (f (1- x)))))
   (must-fail (isodata f ((arg (oldp newp forth back)))))
   (must-fail (isodata f ((arg iso)))))
  ;; :PREDICATE is T:
  (must-succeed*
   (defun p (x)
     (and (natp x)
          (if (zp x)
              nil
            (and (p (1- x))
                 (p (1- x))))))
   (must-fail (isodata p ((((arg (oldp newp forth back)))))))
   (must-fail (isodata p ((((arg iso))))))))

 ;; OLD has stobjs:
 (must-succeed*
  (defun f (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((arg (oldp newp forth back)))))
  (must-fail (isodata f ((arg iso))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check ARGS/RES-ISO input.")

 (defun f (x y) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (and (natp x) (natp y))))
   (+ x y))

 (defun p (x y) (and (natp x) (natp y) (> x y))) ; OLD when :PREDICATE is T

 ;; not a list of doublets:
 (must-fail (isodata f 8))
 (must-fail (isodata f (1 2 3)))
 (must-fail (isodata f ((x (oldp newp forth back)) extra)))
 (must-fail (isodata p 8))
 (must-fail (isodata p (1 2 3)))
 (must-fail (isodata p ((x (oldp newp forth back)) extra)))

 ;; list of doublets, but not a singleton:
 (must-fail (isodata f ()))
 (must-fail (isodata f ((x iso) (y iso))))
 (must-fail (isodata f ((x (oldp newp forth back))
                        (y (oldp newp forth back)))))
 (must-fail (isodata p ()))
 (must-fail (isodata p ((x iso) (y iso))))
 (must-fail (isodata p ((x (oldp newp forth back))
                        (y (oldp newp forth back))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check ARGS/RES input.")

 (defun f (x y) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (and (natp x) (natp y))))
   (+ x y))

 (defun p (x y) (and (natp x) (natp y) (> x y))) ; OLD when :PREDICATE is T

 ;; ARGS/RES is not a formal argument of OLD or :RESULT
 ;; or a non-empty list of formal arguments of OLD and :RESULT:
 (must-succeed*
  (must-fail (isodata f ((z (oldp newp forth back)))))
  (must-fail (isodata f ((z iso))))
  (must-fail (isodata f (((a b) (oldp newp forth back)))))
  (must-fail (isodata f (((a b) iso))))
  (must-fail (isodata f ((nil (oldp newp forth back)))))
  (must-fail (isodata f ((nil iso))))
  (must-fail (isodata f (((x z) (oldp newp forth back)))))
  (must-fail (isodata f (((x z) iso))))
  (must-fail (isodata f ((:resultt iso))))
  (must-fail (isodata f ((z :result iso))))
  (must-fail (isodata p ((z (oldp newp forth back))) :predicate t))
  (must-fail (isodata p ((z iso)) :predicate t))
  (must-fail (isodata p (((a b) (oldp newp forth back))) :predicate t))
  (must-fail (isodata p (((a b) iso)) :predicate t))
  (must-fail (isodata p ((nil (oldp newp forth back))) :predicate t))
  (must-fail (isodata p ((nil iso)) :predicate t))
  (must-fail (isodata p (((x z) (oldp newp forth back))) :predicate t))
  (must-fail (isodata p (((x z) iso)) :predicate t))
  (must-fail (isodata p ((:resultt iso))))
  (must-fail (isodata p ((z :result iso)))))

 ;; ARGS/RES is a list of formal arguments of OLD and :RESULT with duplicates:
 (must-succeed*
  (must-fail (isodata f (((x y y) (oldp newp forth back)))))
  (must-fail (isodata f (((x y y) iso))))
  (must-fail (isodata f (((x :result y :result) iso))))
  (must-fail (isodata p (((x y x) (oldp newp forth back))) :predicate t))
  (must-fail (isodata p (((x y x) iso)) :predicate t))
  (must-fail (isodata p (((x :result y :result) iso))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check ISO input.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 ;; ISO is not a symbol, or a 4-tuple, or a 6-tuple whose 5th element is :HINTS:
 (must-succeed*
  (must-fail (isodata f ((x #\c))))
  (must-fail (isodata f ((x "iso"))))
  (must-fail (isodata f ((x (oldp)))))
  (must-fail (isodata f ((x (oldp newp)))))
  (must-fail (isodata f ((x (oldp newp forth)))))
  (must-fail (isodata f ((x (oldp newp forth back more)))))
  (must-fail (isodata f ((x (oldp newp forth back . more)))))
  (must-fail (isodata f ((x (oldp newp forth back :hints)))))
  (must-fail (isodata f ((x (oldp newp forth back
                                  :hintss (("Goal" :in-theory nil)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check OLDP input, when ISO is not a name.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 ;; OLDP is not a function name, macro name, or lambda expression:
 (must-succeed*
  (must-fail (isodata f ((x ("natp" newp forth back)))))
  (must-fail (isodata f ((x (fffffffff newp forth back)))))
  (must-fail (isodata f ((x (car-cdr-elim newp forth back)))))
  (must-fail (isodata f ((x ((lambda (x)) newp forth back)))))
  (must-fail (isodata f ((x ((lambda (x &y) x) newp forth back)))))
  (must-fail (isodata f ((x ((lambda (x x) x) newp forth back))))))

 ;; OLDP is a function in program mode:
 (must-succeed*
  (defun oldp (x) (declare (xargs :mode :program)) x)
  (must-fail (isodata f ((x (oldp newp forth back))))))

 ;; OLDP is a non-unary function:
 (must-fail (isodata f ((x (cons newp forth back)))))

 ;; OLDP is a function with stobjs:
 (must-succeed*
  (defun oldp (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (oldp newp forth back))))))

 ;; OLDP is a non-guard-verified function:
 (must-succeed*
  (defun oldp (x) (declare (xargs :verify-guards nil)) x)
  (must-fail (isodata f ((x (oldp newp forth back))))))

 ;; OLDP is a lambda expression in program mode:
 (must-fail (isodata f ((x ((lambda (x) (assert-event x)) newp forth back)))))

 ;; OLDP is a non-unary lambda expression:
 (must-fail (isodata f ((x ((lambda (x y) (+ x y)) newp forth back)))))

 ;; OLDP is a non-closed lambda expression:
 (must-fail (isodata f ((x ((lambda (x) (+ x y)) newp forth back)))))

 ;; OLDP is a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x ((lambda (state) (g state)) newp forth back))))))

 ;; OLDP is a lambda expression with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (must-fail
   (isodata f ((x ((lambda (x) (cons (g x) (g x))) newp forth back))))))

 ;; OLDP is a macro that abbreviates a non-unary lambda expression:
 (must-fail (isodata f ((x (list newp forth back)))))

 ;; OLDP is a macro that abbreviates a lambda expression in program mode:
 (must-fail (isodata f ((x (assert-event newp forth back)))))

 ;; OLDP is a macro that abbreviates a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
  (defmacro m (state) `(g ,state))
  (must-fail (isodata f ((x (m newp forth back))))))

 ;; OLDP is a macro that abbreviates a non-closed lambda expression:
 (must-succeed*
  (defmacro m (x) `(+ ,x y))
  (must-fail (isodata f ((x (m newp forth back))))))

 ;; OLDP is a macro that abbreviates a lambda expression
 ;; with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (defmacro m (x) `(g ,x))
  (must-fail (isodata f ((x (m newp forth back)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check NEWP input, when ISO is not a name.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 ;; NEWP is not a function name, macro name, or lambda expression:
 (must-succeed*
  (must-fail (isodata f ((x (natp "natp" forth back)))))
  (must-fail (isodata f ((x (natp fffffffff forth back)))))
  (must-fail (isodata f ((x (natp car-cdr-elim forth back)))))
  (must-fail (isodata f ((x (natp (lambda (x)) forth back)))))
  (must-fail (isodata f ((x (natp (lambda (x &y) x) forth back)))))
  (must-fail (isodata f ((x (natp (lambda (x x) x) forth back))))))

 ;; NEWP is a function in program mode:
 (must-succeed*
  (defun newp (x) (declare (xargs :mode :program)) x)
  (must-fail (isodata f ((x (natp newp forth back))))))

 ;; NEWP is a non-unary function:
 (must-fail (isodata f ((x (natp cons forth back)))))

 ;; NEWP is a function with stobjs:
 (must-succeed*
  (defun newp (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (natp newp forth back))))))

 ;; NEWP is a non-guard-verified function:
 (must-succeed*
  (defun newp (x) (declare (xargs :verify-guards nil)) x)
  (must-fail (isodata f ((x (natp newp forth back))))))

 ;; NEWP is a lambda expression in program mode:
 (must-fail (isodata f ((x (natp (lambda (x) (assert-event x)) forth back)))))

 ;; NEWP is a non-unary lambda expression:
 (must-fail (isodata f ((x (natp (lambda (x y) (+ x y)) forth back)))))

 ;; NEWP is a non-closed lambda expression:
 (must-fail (isodata f ((x (natp (lambda (x) (+ x y)) forth back)))))

 ;; NEWP is a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (natp (lambda (state) (g state)) forth back))))))

 ;; NEWP is a lambda expression with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (must-fail
   (isodata f ((x (natp (lambda (x) (cons (g x) (g x))) forth back))))))

 ;; NEWP is a macro that abbreviates a non-unary lambda expression:
 (must-fail (isodata f ((x (natp list forth back)))))

 ;; NEWP is a macro that abbreviates a lambda expression in program mode:
 (must-fail (isodata f ((x (natp assert-event forth back)))))

 ;; NEWP is a macro that abbreviates a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
  (defmacro m (state) `(g ,state))
  (must-fail (isodata f ((x (natp m forth back))))))

 ;; NEWP is a macro that abbreviates a non-closed lambda expression:
 (must-succeed*
  (defmacro m (x) `(+ ,x y))
  (must-fail (isodata f ((x (natp m forth back))))))

 ;; NEWP is a macro that abbreviates a lambda expression
 ;; with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (defmacro m (x) `(g ,x))
  (must-fail (isodata f ((x (natp m forth back)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check FORTH input, when ISO is not a name.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 ;; FORTH is not a function name, macro name, or lambda expression:
 (must-succeed*
  (must-fail (isodata f ((x (natp natp "natp" back)))))
  (must-fail (isodata f ((x (natp natp fffffffff back)))))
  (must-fail (isodata f ((x (natp natp car-cdr-elim back)))))
  (must-fail (isodata f ((x (natp natp (lambda (x)) back)))))
  (must-fail (isodata f ((x (natp natp (lambda (x &y) x) back)))))
  (must-fail (isodata f ((x (natp natp (lambda (x x) x) back))))))

 ;; FORTH is a function in program mode:
 (must-succeed*
  (defun forth (x) (declare (xargs :mode :program)) x)
  (must-fail (isodata f ((x (natp natp forth back))))))

 ;; FORTH is a non-unary function:
 (must-fail (isodata f ((x (natp natp cons back)))))

 ;; FORTH is a function with stobjs:
 (must-succeed*
  (defun forth (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (natp natp forth back))))))

 ;; FORTH is a non-guard-verified function:
 (must-succeed*
  (defun forth (x) (declare (xargs :verify-guards nil)) x)
  (must-fail (isodata f ((x (natp natp forth back))))))

 ;; FORTH is a lambda expression in program mode:
 (must-fail (isodata f ((x (natp natp (lambda (x) (assert-event x)) back)))))

 ;; FORTH is a non-unary lambda expression:
 (must-fail (isodata f ((x (natp natp (lambda (x y) (+ x y)) back)))))

 ;; FORTH is a non-closed lambda expression:
 (must-fail (isodata f ((x (natp natp (lambda (x) (+ x y)) back)))))

 ;; FORTH is a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (natp natp (lambda (state) (g state)) back))))))

 ;; FORTH is a lambda expression with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (must-fail
   (isodata f ((x (natp natp (lambda (x) (cons (g x) (g x))) back))))))

 ;; FORTH is a macro that abbreviates a non-unary lambda expression:
 (must-fail (isodata f ((x (natp natp list back)))))

 ;; FORTH is a macro that abbreviates a lambda expression in program mode:
 (must-fail (isodata f ((x (natp natp assert-event back)))))

 ;; FORTH is a macro that abbreviates a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
  (defmacro m (state) `(g ,state))
  (must-fail (isodata f ((x (natp natp m back))))))

 ;; FORTH is a macro that abbreviates a non-closed lambda expression:
 (must-succeed*
  (defmacro m (x) `(+ ,x y))
  (must-fail (isodata f ((x (natp natp m back))))))

 ;; FORTH is a macro that abbreviates a lambda expression
 ;; with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (defmacro m (x) `(g ,x))
  (must-fail (isodata f ((x (natp natp m back)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check BACK input, when ISO is not a name.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 ;; BACK is not a function name, macro name, or lambda expression:
 (must-succeed*
  (must-fail (isodata f ((x (natp natp identity "natp")))))
  (must-fail (isodata f ((x (natp natp identity fffffffff)))))
  (must-fail (isodata f ((x (natp natp identity car-cdr-elim)))))
  (must-fail (isodata f ((x (natp natp identity (lambda (x)))))))
  (must-fail (isodata f ((x (natp natp identity (lambda (x &y) x))))))
  (must-fail (isodata f ((x (natp natp identity (lambda (x x) x)))))))

 ;; BACK is a function in program mode:
 (must-succeed*
  (defun back (x) (declare (xargs :mode :program)) x)
  (must-fail (isodata f ((x (natp natp identity back))))))

 ;; BACK is a non-unary function:
 (must-fail (isodata f ((x (natp natp identity cons)))))

 ;; BACK is a function with stobjs:
 (must-succeed*
  (defun back (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (natp natp identity back))))))

 ;; BACK is a non-guard-verified function:
 (must-succeed*
  (defun back (x) (declare (xargs :verify-guards nil)) x)
  (must-fail (isodata f ((x (natp natp identity back))))))

 ;; BACK is a lambda expression in program mode:
 (must-fail
  (isodata f ((x (natp natp identity (lambda (x) (assert-event x)))))))

 ;; BACK is a non-unary lambda expression:
 (must-fail (isodata f ((x (natp natp identity (lambda (x y) (+ x y)))))))

 ;; BACK is a non-closed lambda expression:
 (must-fail (isodata f ((x (natp natp identity (lambda (x) (+ x y)))))))

 ;; BACK is a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) state)
  (must-fail (isodata f ((x (natp natp identity (lambda (state) (g state))))))))

 ;; BACK is a lambda expression with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (must-fail
   (isodata f ((x (natp natp identity (lambda (x) (cons (g x) (g x)))))))))

 ;; BACK is a macro that abbreviates a non-unary lambda expression:
 (must-fail (isodata f ((x (natp natp identity list)))))

 ;; BACK is a macro that abbreviates a lambda expression in program mode:
 (must-fail (isodata f ((x (natp natp identity assert-event)))))

 ;; BACK is a macro that abbreviates a lambda expression with stobjs:
 (must-succeed*
  (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
  (defmacro m (state) `(g ,state))
  (must-fail (isodata f ((x (natp natp identity m))))))

 ;; BACK is a macro that abbreviates a non-closed lambda expression:
 (must-succeed*
  (defmacro m (x) `(+ ,x y))
  (must-fail (isodata f ((x (natp natp identity m))))))

 ;; BACK is a macro that abbreviates a lambda expression
 ;; with non-guard-verified functions:
 (must-succeed*
  (defun g (x) (declare (xargs :verify-guards nil)) x)
  (defmacro m (x) `(g ,x))
  (must-fail (isodata f ((x (natp natp identity m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check ISO input when it is a name.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 (defiso nat-id-ng natp natp identity identity :guard-thms nil)

 ;; ISO is not a DEFISO:
 (must-fail (isodata f ((x nat-idd))))
 (must-fail (isodata f ((x natid))))

 ;; ISO has no guard theorems:
 (must-fail (isodata f ((x nat-id-ng)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Wildcard in OLD.")

 (defiso nat-id natp natp identity identity)

 (defiso acl2-number-id acl2-numberp acl2-numberp identity identity)

 (must-succeed* ; :PREDICATE is NIL
  (defun f{3} (x) (declare (xargs :guard (natp x))) (1+ x)) ; denoted by OLD
  (add-numbered-name-in-use f{3}) ; mark F{3} in use
  (add-numbered-name-in-use f{2}) ; wildcard won't resolve to this one
  (must-succeed (isodata f{*} ((x (natp natp identity identity)))))
  (must-succeed (isodata f{*} (((x :result) (natp natp identity identity)))))
  (must-succeed
   (isodata f{*} ((:result (acl2-numberp acl2-numberp identity identity)))))
  (must-succeed (isodata f{*} ((x nat-id))))
  (must-succeed (isodata f{*} (((x :result) nat-id))))
  (must-succeed (isodata f{*} ((:result acl2-number-id))))
  :with-output-off nil)

 (must-succeed* ; :PREDICATE is T
  (defun p{3} (x) (and (natp x) (> x 10))) ; denoted by OLD
  (add-numbered-name-in-use p{3}) ; mark P{3} in use
  (add-numbered-name-in-use p{2}) ; wildcard won't resolve to this one
  (must-succeed
   (isodata p{*} ((x (natp natp identity identity))) :predicate t))
  (must-succeed (isodata p{*} ((x nat-id)) :predicate t))
  :with-output-off nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check NEW-NAME input.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 ;; NEW-NAME is not a symbol:
 (must-fail (isodata f ((x (natp natp identity identity))) :new-name "g"))
 (must-fail (isodata f ((x nat-id)) :new-name "g"))

 ;; NEW-NAME is in the main Lisp package:
 (must-fail (isodata f ((x (natp natp identity identity))) :new-name cons))
 (must-fail (isodata f ((x nat-id)) :new-name cons))

 ;; NEW-NAME is a keyword (other than :AUTO):
 (must-fail (isodata f ((x (natp natp identity identity))) :new-name :g))
 (must-fail (isodata f ((x nat-id)) :new-name :g))

 ;; NEW-NAME is a name that already exists:
 (must-fail (isodata f ((x (natp natp identity identity))) :new-name len))
 (must-fail (isodata f ((x nat-id)) :new-name len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check THM-NAME input.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 ;; THM-NAME is not a symbol:
 (must-fail
  (isodata f ((x (natp natp identity identity))) :thm-name "f-~>-f{1}"))
 (must-fail
  (isodata f ((x nat-id)) :thm-name "f-~>-f{1}"))

 ;; THM-NAME is in the main Lisp package:
 (must-fail (isodata f ((x (natp natp identity identity))) :thm-name cons))
 (must-fail (isodata f ((x nat-id)) :thm-name cons))

 ;; THM-NAME is a keyword (other than :AUTO):
 (must-fail
  (isodata f ((x (natp natp identity identity))) :thm-name :f-~>-f{1}))
 (must-fail
  (isodata f ((x nat-id)) :thm-name :f-~>-f{1}))

 ;; THM-NAME yields an automatic name that already exists:
 (must-succeed*
  (defun f-~>-f{1} (x) x)
  (must-fail (isodata f ((x (natp natp identity identity))) :thm-name :auto))
  (must-fail (isodata f ((x nat-id)) :thm-name :auto)))

 ;; THM-NAME yields a default name that already exists:
 (must-succeed*
  (defun f-~>-f{1} (x) x)
  (must-fail (isodata f ((x (natp natp identity identity)))))
  (must-fail (isodata f ((x nat-id)))))

 ;; THM-NAME is a name that already exists:
 (must-fail
  (isodata f ((x (natp natp identity identity))) :thm-name car-cdr-elim))
 (must-fail
  (isodata f ((x nat-id)) :thm-name car-cdr-elim)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check the simple inputs.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 ;; PREDICATE is not a boolean:
 (must-fail (isodata f ((x (natp natp identity identity))) :predicate 4))
 (must-fail (isodata f ((x nat-id)) :predicate 4))

 ;; NEW-ENABLE is not in (T NIL :AUTO):
 (must-fail (isodata f ((x (natp natp identity identity))) :new-enable "t"))
 (must-fail (isodata f ((x nat-id)) :new-enable "t"))

 ;; THM-ENABLE is not a boolean:
 (must-fail (isodata f ((x (natp natp identity identity))) :thm-enable :auto))
 (must-fail (isodata f ((x nat-id)) :thm-enable :auto))

 ;; VERIFY-GUARDS is not in (T NIL :AUTO):
 (must-fail
  (isodata f ((x (natp natp identity identity))) :verify-guards :nil))
 (must-fail
  (isodata f ((x nat-id)) :verify-guards :nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check applicability condition hints.")

 (defun f (x) ; OLD when PREDICATE is NIL
   (declare (xargs :guard (natp x)))
   (if (zp x) 1 (* x (f (1- x)))))

 (defun p (x) (and (natp x) (> x 10))) ; OLD when PREDICATE is T

 (defiso nat-id natp natp identity identity)

 ;; hints for :OLDP-OF-REC-CALL-ARGS allowed only if OLD is recursive:
 (must-fail (isodata p ((x (natp natp identity identity)))
                     :predicate t
                     :hints (:oldp-of-rec-call-args-hints
                             (("Goal" :in-theory nil)))))
 (must-fail (isodata p ((x nat-id))
                     :predicate t
                     :hints (:oldp-of-rec-call-args-hints
                             (("Goal" :in-theory nil)))))

 ;; hints for :OLD-GUARD disallowed if VERIFY-GUARDS is NIL or PREDICATE is T:
 (must-succeed*
  (must-fail (isodata f ((x (natp natp identity identity)))
                      :verify-guards nil
                      :hints (:old-guard (("Goal" :in-theory nil)))))
  (must-fail (isodata p ((x (natp natp identity identity)))
                      :predicate t
                      :hints (:old-guard (("Goal" :in-theory nil))))))

 ;; hints for :OLD-GUARD-PRED disallowed
 ;; if VERIFY-GUARDS is NIL or PREDICATE is NIL:
 (must-succeed*
  (must-fail (isodata p ((x (natp natp identity identity)))
                      :predicate t
                      :verify-guards nil
                      :hints (:old-guard-pred (("Goal" :in-theory nil)))))
  (must-fail (isodata f ((x (natp natp identity identity)))
                      :verify-guards nil
                      :hints (:old-guard-pred (("Goal" :in-theory nil))))))

 ;; hints for :OLDP-OF-OLD disallowed
 ;; if ARGS/RES-ISO does not include :RESULT:
 (must-succeed*
  (must-fail (isodata p ((x (natp natp identity identity)))
                      :predicate t
                      :verify-guards nil
                      :hints (:oldp-of-old (("Goal" :in-theory nil)))))
  (must-fail (isodata f ((x (natp natp identity identity)))
                      :verify-guards nil
                      :hints (:old-of-old (("Goal" :in-theory nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Check the :PRINT input.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x))) (1+ x))

 (defun p (x) (and (natp x) (> x 10))) ; OLD when :PREDICATE is T

 (defiso nat-id natp natp identity identity)

 (defiso acl2-number-id acl2-numberp acl2-numberp identity identity)

 ;; not a print specifier:
 (must-fail (isodata f ((x (natp natp identity identity))) :print 88))
 (must-fail (isodata f (((x :result) (natp natp identity identity))) :print 88))
 (must-fail
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :print 88))
 (must-fail (isodata f ((x nat-id)) :print 88))
 (must-fail (isodata f (((x :result) nat-id)) :print 88))
 (must-fail (isodata f ((:result acl2-number-id)) :print 88))
 (must-fail
  (isodata p ((x (natp natp identity identity))) :predicate t :print #\t))
 (must-fail
  (isodata p (((x :result) (natp natp identity identity)))
           :predicate t :print #\t))
 (must-fail
  (isodata p ((:result (acl2-numberp acl2-numberp identity identity)))
           :predicate t :print #\t))
 (must-fail
  (isodata p ((x nat-id)) :predicate t :print #\t))
 (must-fail
  (isodata p (((x :result) nat-id)) :predicate t :print #\t))
 (must-fail
  (isodata p ((:result acl2-number-id)) :predicate t :print #\t))

 ;; default output:
 (must-succeed
  (isodata f ((x (natp natp identity identity))))
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) (natp natp identity identity))))
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity))))
  :with-output-off nil)
 (must-succeed
  (isodata f ((x nat-id)))
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) nat-id)))
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result acl2-number-id)))
  :with-output-off nil)
 (must-succeed
  (isodata p ((x (natp natp identity identity))) :predicate t)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x nat-id)) :predicate t)
  :with-output-off nil)

 ;; no output:
 (must-succeed
  (isodata f ((x (natp natp identity identity))) :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) (natp natp identity identity))) :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata f ((x nat-id)) :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) nat-id)) :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result acl2-number-id)) :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x (natp natp identity identity))) :predicate t :print nil)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x nat-id)) :predicate t :print nil)
  :with-output-off nil)

 ;; error output:
 (must-succeed
  (isodata f ((x (natp natp identity identity))) :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) (natp natp identity identity))) :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata f ((x nat-id)) :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) nat-id)) :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result acl2-number-id)) :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x (natp natp identity identity))) :predicate t :print :error)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x nat-id)) :predicate t :print :error)
  :with-output-off nil)

 ;; result output::
 (must-succeed
  (isodata f ((x (natp natp identity identity))) :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) (natp natp identity identity))) :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata f ((x nat-id)) :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) nat-id)) :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result acl2-number-id)) :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x (natp natp identity identity))) :predicate t :print :result)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x nat-id)) :predicate t :print :result)
  :with-output-off nil)

 ;; information output:
 (must-succeed
  (isodata f ((x (natp natp identity identity))) :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) (natp natp identity identity))) :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata f ((x nat-id)) :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) nat-id)) :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result acl2-number-id)) :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x (natp natp identity identity))) :predicate t :print :info)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x nat-id)) :predicate t :print :info)
  :with-output-off nil)

 ;; all output:
 (must-succeed
  (isodata f ((x (natp natp identity identity))) :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) (natp natp identity identity))) :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata f ((x nat-id)) :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata f (((x :result) nat-id)) :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata f ((:result acl2-number-id)) :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x (natp natp identity identity))) :predicate t :print :all)
  :with-output-off nil)
 (must-succeed
  (isodata p ((x nat-id)) :predicate t :print :all)
  :with-output-off nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Naming of NEW.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x))) (1+ x))

 (defun p (x) (and (natp x) (> x 10))) ; OLD when :PREDICATE is T

 (defiso nat-id natp natp identity identity)

 (defiso acl2-number-id acl2-numberp acl2-numberp identity identity)

 ;; default NEW name for F:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (+ 1 (IDENTITY X)) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f (((x :result) (natp natp identity identity))))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (IDENTITY (+ 1 (IDENTITY X))) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity))))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IDENTITY (+ 1 X))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f ((x nat-id)))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (+ 1 (IDENTITY X)) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f (((x :result) nat-id)))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (IDENTITY (+ 1 (IDENTITY X))) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f ((:result acl2-number-id)))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IDENTITY (+ 1 X))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))

 ;; default NEW name for P:
 (must-succeed*
  (isodata p ((x (natp natp identity identity))) :predicate t)
  (must-be-redundant
   (DEFUN P{1} (X)
     (DECLARE (XARGS :GUARD (NATP X) :VERIFY-GUARDS T :MODE :LOGIC))
     (AND (MBT$ (NATP X))
          (NATP (IDENTITY X))
          (< 10 (IDENTITY X)))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((p . (1))))))
 (must-succeed*
  (isodata p ((x nat-id)) :predicate t)
  (must-be-redundant
   (DEFUN P{1} (X)
     (DECLARE (XARGS :GUARD (NATP X) :VERIFY-GUARDS T :MODE :LOGIC))
     (AND (MBT$ (NATP X))
          (NATP (IDENTITY X))
          (< 10 (IDENTITY X)))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((p . (1))))))

 ;; automatic NEW name for F:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))) :new-name :auto)
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (+ 1 (IDENTITY X)) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f (((x :result) (natp natp identity identity))))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (IDENTITY (+ 1 (IDENTITY X))) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity))))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IDENTITY (+ 1 X))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f ((x nat-id)) :new-name :auto)
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (+ 1 (IDENTITY X)) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f (((x :result) nat-id)))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (IDENTITY (+ 1 (IDENTITY X))) NIL)))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))
 (must-succeed*
  (isodata f ((:result acl2-number-id)))
  (must-be-redundant
   (DEFUN F{1} (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IDENTITY (+ 1 X))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((f . (1))))))

 ;; automatic NEW name for P:
 (must-succeed*
  (isodata p ((x (natp natp identity identity))) :predicate t :new-name :auto)
  (must-be-redundant
   (DEFUN P{1} (X)
     (DECLARE (XARGS :GUARD (NATP X) :VERIFY-GUARDS T :MODE :LOGIC))
     (AND (MBT$ (NATP X))
          (NATP (IDENTITY X))
          (< 10 (IDENTITY X)))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((p . (1))))))
 (must-succeed*
  (isodata p ((x nat-id)) :predicate t :new-name :auto)
  (must-be-redundant
   (DEFUN P{1} (X)
     (DECLARE (XARGS :GUARD (NATP X) :VERIFY-GUARDS T :MODE :LOGIC))
     (AND (MBT$ (NATP X))
          (NATP (IDENTITY X))
          (< 10 (IDENTITY X)))))
  (assert-event ; numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state))
          '((p . (1))))))

 ;; explicitly named NEW for F:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))) :new-name g)
  (must-be-redundant
   (DEFUN G (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (+ 1 (IDENTITY X)) NIL)))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))
 (must-succeed*
  (isodata f (((x :result) (natp natp identity identity))) :new-name g)
  (must-be-redundant
   (DEFUN G (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (IDENTITY (+ 1 (IDENTITY X))) NIL)))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))
 (must-succeed*
  (isodata f ((:result (acl2-numberp acl2-numberp identity identity)))
           :new-name g)
  (must-be-redundant
   (DEFUN G (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IDENTITY (+ 1 X))))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))
 (must-succeed*
  (isodata f ((x nat-id)) :new-name g)
  (must-be-redundant
   (DEFUN G (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (+ 1 (IDENTITY X)) NIL)))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))
 (must-succeed*
  (isodata f (((x :result) nat-id)) :new-name g)
  (must-be-redundant
   (DEFUN G (X)
     (DECLARE (XARGS :GUARD (AND (NATP X) (NATP (IDENTITY X)))
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IF (MBT$ (NATP X)) (IDENTITY (+ 1 (IDENTITY X))) NIL)))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))
 (must-succeed*
  (isodata f ((:result acl2-number-id)) :new-name g)
  (must-be-redundant
   (DEFUN G (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T
                     :MODE :LOGIC))
     (IDENTITY (+ 1 X))))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))

 ;; explicitly named NEW for P:
 (must-succeed*
  (isodata p ((x (natp natp identity identity))) :predicate t :new-name q)
  (must-be-redundant
   (DEFUN Q (X)
     (DECLARE (XARGS :GUARD (NATP X) :VERIFY-GUARDS T :MODE :LOGIC))
     (AND (MBT$ (NATP X))
          (NATP (IDENTITY X))
          (< 10 (IDENTITY X)))))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil)))
 (must-succeed*
  (isodata p ((x nat-id)) :predicate t :new-name q)
  (must-be-redundant
   (DEFUN Q (X)
     (DECLARE (XARGS :GUARD (NATP X) :VERIFY-GUARDS T :MODE :LOGIC))
     (AND (MBT$ (NATP X))
          (NATP (IDENTITY X))
          (< 10 (IDENTITY X)))))
  (assert-event ; no numbered name has been recorded
   (equal (table-alist 'numbered-names-in-use (w state)) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Enabling of NEW.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 ;; by default, NEW is enabled iff OLD is:
 (must-succeed*
  (must-succeed*
   (isodata f ((x (natp natp identity identity))))
   (assert-event (fundef-enabledp 'f{1} state)))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x (natp natp identity identity))))
   (assert-event (not (fundef-enabledp 'f{1} state)))))
 (must-succeed*
  (must-succeed*
   (isodata f ((x nat-id)))
   (assert-event (fundef-enabledp 'f{1} state)))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x nat-id)))
   (assert-event (not (fundef-enabledp 'f{1} state)))))

 ;; enable NEW iff OLD is enabled:
 (must-succeed*
  (must-succeed*
   (isodata f ((x (natp natp identity identity))) :new-enable :auto)
   (assert-event (fundef-enabledp 'f{1} state)))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x (natp natp identity identity))) :new-enable :auto)
   (assert-event (not (fundef-enabledp 'f{1} state)))))
 (must-succeed*
  (must-succeed*
   (isodata f ((x nat-id)) :new-enable :auto)
   (assert-event (fundef-enabledp 'f{1} state)))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x nat-id)) :new-enable :auto)
   (assert-event (not (fundef-enabledp 'f{1} state)))))

 ;; enable NEW:
 (must-succeed*
  (must-succeed*
   (isodata f ((x (natp natp identity identity))) :new-enable t)
   (assert-event (fundef-enabledp 'f{1} state)))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x (natp natp identity identity))) :new-enable t)
   (assert-event (fundef-enabledp 'f{1} state))))
 (must-succeed*
  (must-succeed*
   (isodata f ((x nat-id)) :new-enable t)
   (assert-event (fundef-enabledp 'f{1} state)))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x nat-id)) :new-enable t)
   (assert-event (fundef-enabledp 'f{1} state))))

 ;; disable NEW:
 (must-succeed*
  (must-succeed*
   (isodata f ((x (natp natp identity identity))) :new-enable nil)
   (assert-event (not (fundef-enabledp 'f{1} state))))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x (natp natp identity identity))) :new-enable nil)
   (assert-event (not (fundef-enabledp 'f{1} state)))))
 (must-succeed*
  (must-succeed*
   (isodata f ((x nat-id)) :new-enable nil)
   (assert-event (not (fundef-enabledp 'f{1} state))))
  (must-succeed*
   (in-theory (disable f))
   (isodata f ((x nat-id)) :new-enable nil)
   (assert-event (not (fundef-enabledp 'f{1} state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Naming of OLD-TO-NEW.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x))) (1+ x))

 (defun p (x) (and (natp x) (> x 10))) ; OLD when :PREDICATE is T

 (defiso nat-id natp natp identity identity)

 ;; default OLD-TO-NEW name for F:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))))
  (must-be-redundant
   (DEFTHM F-~>-F{1}
     (IMPLIES (NATP X) (EQUAL (F X) (F{1} (IDENTITY X)))))))
 (must-succeed*
  (isodata f ((x nat-id)))
  (must-be-redundant
   (DEFTHM F-~>-F{1}
     (IMPLIES (NATP X) (EQUAL (F X) (F{1} (IDENTITY X)))))))

 ;; default OLD-TO-NEW name for P:
 (must-succeed*
  (isodata p ((x (natp natp identity identity))) :predicate t)
  (must-be-redundant
   (DEFTHM P-~>-P{1}
     (IMPLIES (NATP X) (EQUAL (P X) (P{1} (IDENTITY X)))))))
 (must-succeed*
  (isodata p ((x nat-id)) :predicate t)
  (must-be-redundant
   (DEFTHM P-~>-P{1}
     (IMPLIES (NATP X) (EQUAL (P X) (P{1} (IDENTITY X)))))))

 ;; automatic OLD-TO-NEW name for F:
 (must-succeed*
  (isodata f ((x (natp natp identity identity)))
           :thm-name :auto)
  (must-be-redundant
   (DEFTHM F-~>-F{1}
     (IMPLIES (NATP X) (EQUAL (F X) (F{1} (IDENTITY X)))))))
 (must-succeed*
  (isodata f ((x nat-id))
           :thm-name :auto)
  (must-be-redundant
   (DEFTHM F-~>-F{1}
     (IMPLIES (NATP X) (EQUAL (F X) (F{1} (IDENTITY X)))))))

 ;; automatic OLD-TO-NEW name for P:
 (must-succeed*
  (isodata p ((x (natp natp identity identity)))
           :predicate t
           :thm-name :auto)
  (must-be-redundant
   (DEFTHM P-~>-P{1}
     (IMPLIES (NATP X) (EQUAL (P X) (P{1} (IDENTITY X)))))))
 (must-succeed*
  (isodata p ((x nat-id))
           :predicate t
           :thm-name :auto)
  (must-be-redundant
   (DEFTHM P-~>-P{1}
     (IMPLIES (NATP X) (EQUAL (P X) (P{1} (IDENTITY X)))))))

 ;; explicitly named OLD-TO-NEW for F:
 (must-succeed*
  (isodata f ((x (natp natp identity identity)))
           :thm-name f{1}-correct-wrt-f)
  (must-be-redundant
   (DEFTHM F{1}-CORRECT-WRT-F
     (IMPLIES (NATP X) (EQUAL (F X) (F{1} (IDENTITY X)))))))
 (must-succeed*
  (isodata f ((x nat-id))
           :thm-name f{1}-correct-wrt-f)
  (must-be-redundant
   (DEFTHM F{1}-CORRECT-WRT-F
     (IMPLIES (NATP X) (EQUAL (F X) (F{1} (IDENTITY X)))))))

 ;; explicitly named OLD-TO-NEW for P:
 (must-succeed*
  (isodata p ((x (natp natp identity identity)))
           :predicate t
           :thm-name p{1}-correct-wrt-p)
  (must-be-redundant
   (DEFTHM P{1}-CORRECT-WRT-P
     (IMPLIES (NATP X) (EQUAL (P X) (P{1} (IDENTITY X)))))))
 (must-succeed*
  (isodata p ((x nat-id))
           :predicate t
           :thm-name p{1}-correct-wrt-p)
  (must-be-redundant
   (DEFTHM P{1}-CORRECT-WRT-P
     (IMPLIES (NATP X) (EQUAL (P X) (P{1} (IDENTITY X))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Enabling of OLD-TO-NEW.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 ;; by default, OLD-TO-NEW is enabled:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))))
  (assert-event (rune-enabledp '(:rewrite f-~>-f{1}) state)))
 (must-succeed*
  (isodata f ((x nat-id)))
  (assert-event (rune-enabledp '(:rewrite f-~>-f{1}) state)))

 ;; enable OLD-TO-NEW:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))) :thm-enable t)
  (assert-event (rune-enabledp '(:rewrite f-~>-f{1}) state)))
 (must-succeed*
  (isodata f ((x nat-id)) :thm-enable t)
  (assert-event (rune-enabledp '(:rewrite f-~>-f{1}) state)))

 ;; disable OLD-TO-NEW:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))) :thm-enable nil)
  (assert-event (not (rune-enabledp '(:rewrite f-~>-f{1}) state))))
 (must-succeed*
  (isodata f ((x nat-id)) :thm-enable nil)
  (assert-event (not (rune-enabledp '(:rewrite f-~>-f{1}) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Non-executability of NEW.")

 (defiso nat-id natp natp identity identity)

 ;; NEW is non-executable iff OLD is:
 (must-succeed*
  ;; :PREDICATE is NIL:
  (must-succeed*
   (must-succeed*
    (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; executable OLD
    (isodata f ((x (natp natp identity identity))))
    (assert-event (not (non-executablep 'f{1} (w state)))))
   (must-succeed*
    (defun-nx f (x) ; non-executable OLD
      (declare (xargs :guard (natp x)))
      (1+ x))
    (isodata f ((x (natp natp identity identity))))
    (assert-event (non-executablep 'f{1} (w state)))))
  ;; :PREDICATE is T:
  (must-succeed*
   (must-succeed*
    (defun p (x) (and (natp x) (> x 10))) ; executable OLD
    (isodata p ((x (natp natp identity identity))) :predicate t)
    (assert-event (not (non-executablep 'p{1} (w state)))))
   (must-succeed*
    (defun-nx p (x) (and (natp x) (> x 10))) ; non-executable OLD
    (isodata p ((x (natp natp identity identity))) :predicate t)
    (assert-event (non-executablep 'p{1} (w state))))))
 (must-succeed*
  ;; :PREDICATE is NIL:
  (must-succeed*
   (must-succeed*
    (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; executable OLD
    (isodata f ((x nat-id)))
    (assert-event (not (non-executablep 'f{1} (w state)))))
   (must-succeed*
    (defun-nx f (x) ; non-executable OLD
      (declare (xargs :guard (natp x)))
      (1+ x))
    (isodata f ((x nat-id)))
    (assert-event (non-executablep 'f{1} (w state)))))
  ;; :PREDICATE is T:
  (must-succeed*
   (must-succeed*
    (defun p (x) (and (natp x) (> x 10))) ; executable OLD
    (isodata p ((x nat-id)) :predicate t)
    (assert-event (not (non-executablep 'p{1} (w state)))))
   (must-succeed*
    (defun-nx p (x) (and (natp x) (> x 10))) ; non-executable OLD
    (isodata p ((x nat-id)) :predicate t)
    (assert-event (non-executablep 'p{1} (w state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Guard verification of NEW.")

 (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD

 (defiso nat-id natp natp identity identity)

 ;; by default, NEW is guard-verified if OLD is:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))))
  (assert-event (guard-verified-p 'f{1} (w state))))
 (must-succeed*
  (isodata f ((x nat-id)))
  (assert-event (guard-verified-p 'f{1} (w state))))

 ;; guard-verify NEW:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))) :verify-guards t)
  (assert-event (guard-verified-p 'f{1} (w state))))
 (must-succeed*
  (isodata f ((x nat-id)) :verify-guards t)
  (assert-event (guard-verified-p 'f{1} (w state))))

 ;; do not guard-verify NEW:
 (must-succeed*
  (isodata f ((x (natp natp identity identity))) :verify-guards nil)
  (assert-event (not (guard-verified-p 'f{1} (w state)))))
 (must-succeed*
  (isodata f ((x nat-id)) :verify-guards nil)
  (assert-event (not (guard-verified-p 'f{1} (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Guard of NEW when :PREDICATE is NIL.")

 (must-succeed*
  (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD
  (isodata f ((x (natp natp identity identity))))
  (assert-event (equal (guard 'f{1} nil (w state))
                       '(if (natp x) (natp (identity x)) 'nil))))

 (must-succeed*
  (defun f (x) (declare (xargs :guard (natp x))) (1+ x)) ; OLD
  (defiso nat-id natp natp identity identity)
  (isodata f ((x nat-id)))
  (assert-event (equal (guard 'f{1} nil (w state))
                       '(if (natp x) (natp (identity x)) 'nil)))))


(must-succeed*

 (test-title "Guard of NEW when :PREDICATE is T.")

 (must-succeed*
  (defun p (x) (and (natp x) (> x 10))) ; OLD
  (isodata p ((x (natp natp identity identity))) :predicate t)
  (assert-event (equal (guard 'p{1} nil (w state)) '(natp x))))

 (must-succeed*
  (defun p (x) (and (natp x) (> x 10))) ; OLD
  (defiso nat-id natp natp identity identity)
  (isodata p ((x nat-id)) :predicate t)
  (assert-event (equal (guard 'p{1} nil (w state)) '(natp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Isomorphism between naturals and integers.")

 (defun f (n) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp n)))
   (1+ n))

 (defun p (n) (and (natp n) (> n 10))) ; OLD when :PREDICATE is NIL

 (defun nat-to-int (n) ; FORTH
   (declare (xargs :guard (natp n)))
   (if (evenp n)
       (/ n 2)
     (- (/ (1+ n) 2))))

 (defun int-to-nat (i) ; BACK
   (declare (xargs :guard (integerp i)))
   (if (>= i 0)
       (* 2 i)
     (1- (- (* 2 i)))))

 (include-book "arithmetic-5/top" :dir :system)

 (must-succeed*
  (must-succeed
   (isodata f ((n (natp integerp nat-to-int int-to-nat)))))
  (must-succeed
   (isodata f (((:result n) (natp integerp nat-to-int int-to-nat)))))
  (must-succeed
   (isodata p ((n (natp integerp nat-to-int int-to-nat))) :predicate t)))

 (must-succeed*
  (defiso nat/int natp integerp nat-to-int int-to-nat)
  (must-succeed (isodata f ((n nat/int))))
  (must-succeed (isodata f (((:result n) nat/int))))
  (must-succeed (isodata p ((n nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "OLD with unused formals/locals.")

 (defiso nat-id natp natp identity identity)

 ;; unused formal:
 (must-succeed*
  (defun f (x y) ; OLD
    (declare (xargs :guard (and (natp x) (natp y))))
    (declare (ignore y))
    (+ x 4))
  (isodata f ((x (natp natp identity identity)))))
 (must-succeed*
  (defun f (x y) ; OLD
    (declare (xargs :guard (and (natp x) (natp y))))
    (declare (ignore y))
    (+ x 4))
  (isodata f ((x nat-id))))

 ;; unused local:
 (must-succeed*
  (defun f (x) ; OLD
    (declare (xargs :guard (natp x)))
    (let ((y 0))
      (declare (ignore y))
      (1+ x)))
  (isodata f ((x (natp natp identity identity)))))
 (must-succeed*
  (defun f (x) ; OLD
    (declare (xargs :guard (natp x)))
    (let ((y 0))
      (declare (ignore y))
      (1+ x)))
  (isodata f ((x nat-id))))

 ;; unused implicit local __FUNCTION__:
 (must-succeed*
  (define f (x) :guard (natp x) (1+ x) :enabled t)
  (isodata f ((x (natp natp identity identity)))))
 (must-succeed*
  (define f (x) :guard (natp x) (1+ x) :enabled t)
  (isodata f ((x nat-id)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Guard-unverifiable OLD when :PREDICATE is NIL.")

 (defun f (x) ; OLD
   (declare (xargs :guard (natp x) :verify-guards nil))
   (car x))

 (defiso nat-id natp natp identity identity)

 (isodata f ((x (natp natp identity identity))) :verify-guards nil)

 (isodata f ((x nat-id)) :verify-guards nil))

(must-succeed*

 (test-title "Guard-unverifiable OLD when :PREDICATE is T.")

 (defun p (x) ; OLD
   (declare (xargs :verify-guards nil))
   (and (> x 10) (natp x)))

 (defiso nat-id natp natp identity identity)

 (isodata p ((x (natp natp identity identity)))
          :predicate t :verify-guards nil)

 (isodata p ((x nat-id))
          :predicate t :verify-guards nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Use macro names instead of function names.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x)))
   (1+ x))

 (defun p (x) (and (natp x) (> x 10))) ; OLD when :PREDICATE is T

 ;; macro version of identity isomorphism between naturals:
 (must-succeed*
  (defmacro natmac (x) `(and (integerp ,x) (>= ,x 0)))
  (defmacro idmac (x) `(car (list ,x)))
  (must-succeed (isodata f ((x (natmac natmac idmac idmac)))))
  (must-succeed (isodata p ((x (natmac natmac idmac idmac))) :predicate t))
  (defiso nat-id natmac natmac idmac idmac)
  (must-succeed (isodata f ((x nat-id))))
  (must-succeed (isodata p ((x nat-id)) :predicate t)))

 ;; macro version of isomorphism between naturals and integers:
 (must-succeed*
  (defmacro nat-to-int (n) ; FORTH
    `(if (evenp ,n)
         (/ ,n 2)
       (- (/ (1+ ,n) 2))))
  (defmacro int-to-nat (i) ; BACK
    `(if (>= ,i 0)
         (* 2 ,i)
       (1- (- (* 2 ,i)))))
  (include-book "arithmetic-5/top" :dir :system)
  (must-succeed
   (isodata f ((x (natp integerp nat-to-int int-to-nat)))))
  (must-succeed
   (isodata p ((x (natp integerp nat-to-int int-to-nat))) :predicate t))
  (defiso nat/int natp integerp nat-to-int int-to-nat)
  (must-succeed
   (isodata f ((x nat/int))))
  (must-succeed
   (isodata p ((x nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Use lambda expressions instead of function names.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x)))
   (1+ x))

 (defun p (x) (and (natp x) (> x 10))) ; OLD when :PREDICATE is T

 ;; lambda expression version of identity isomorphism between naturals:
 (must-succeed*
  (must-succeed (isodata f ((x ((lambda (n) (natp n))
                                (lambda (m) (natp m))
                                (lambda (a) a)
                                (lambda (b) b))))))
  (must-succeed (isodata p ((x ((lambda (n) (natp n))
                                (lambda (m) (natp m))
                                (lambda (a) a)
                                (lambda (b) b))))
                         :predicate t))
  (defiso nat-id
    (lambda (n) (natp n))
    (lambda (m) (natp m))
    (lambda (a) a)
    (lambda (b) b))
  (must-succeed (isodata f ((x nat-id))))
  (must-succeed (isodata p ((x nat-id)) :predicate t)))

 ;; lambda expression version of isomorphism between naturals and integers:
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (must-succeed (isodata f ((x (natp
                                integerp
                                (lambda (n) (if (evenp n)
                                                (/ n 2)
                                              (- (/ (1+ n) 2))))
                                (lambda (i) (if (>= i 0)
                                                (* 2 i)
                                              (1- (- (* 2 i))))))))))
  (must-succeed (isodata p ((x (natp
                                integerp
                                (lambda (n) (if (evenp n)
                                                (/ n 2)
                                              (- (/ (1+ n) 2))))
                                (lambda (i) (if (>= i 0)
                                                (* 2 i)
                                              (1- (- (* 2 i))))))))
                               :predicate t))
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (must-succeed (isodata f ((x nat/int))))
  (must-succeed (isodata p ((x nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "OLD with multiple arguments.")

 (defun f (x y z) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (and (natp x) (natp y) (symbolp z))))
   (cons (+ x y) z))

 (defun p (x y z) ; OLD when :PREDICATE is T
   (and (natp x) (natp y) (> x y) (symbolp z)))

 ;; isomorphism between naturals:
 (must-succeed*
  (must-succeed (isodata f ((x (natp natp (lambda (a) a) (lambda (a) a))))))
  (must-succeed (isodata f ((y (natp natp (lambda (a) a) (lambda (a) a))))))
  (must-succeed (isodata p ((x (natp natp (lambda (a) a) (lambda (a) a))))
                         :predicate t))
  (must-succeed (isodata p ((y (natp natp (lambda (a) a) (lambda (a) a))))
                         :predicate t))
  (defiso nat-id natp natp (lambda (a) a) (lambda (a) a))
  (must-succeed (isodata f ((x nat-id))))
  (must-succeed (isodata f ((y nat-id))))
  (must-succeed (isodata p ((x nat-id)) :predicate t))
  (must-succeed (isodata p ((y nat-id)) :predicate t)))

 ;; isomorphism between naturals and integers:
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (must-succeed
   (isodata f ((x (natp
                   integerp
                   (lambda (n) (if (evenp n)
                                   (/ n 2)
                                 (- (/ (1+ n) 2))))
                   (lambda (i) (if (>= i 0)
                                   (* 2 i)
                                 (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata f ((y (natp
                   integerp
                   (lambda (n) (if (evenp n)
                                   (/ n 2)
                                 (- (/ (1+ n) 2))))
                   (lambda (i) (if (>= i 0)
                                   (* 2 i)
                                 (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata p ((x (natp
                   integerp
                   (lambda (n) (if (evenp n)
                                   (/ n 2)
                                 (- (/ (1+ n) 2))))
                   (lambda (i) (if (>= i 0)
                                   (* 2 i)
                                 (1- (- (* 2 i))))))))
            :predicate t))
  (must-succeed
   (isodata p ((y (natp
                   integerp
                   (lambda (n) (if (evenp n)
                                   (/ n 2)
                                 (- (/ (1+ n) 2))))
                   (lambda (i) (if (>= i 0)
                                   (* 2 i)
                                 (1- (- (* 2 i))))))))
            :predicate t))
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (must-succeed
   (isodata f ((x nat/int))))
  (must-succeed
   (isodata f ((y nat/int))))
  (must-succeed
   (isodata p ((x nat/int)) :predicate t))
  (must-succeed
   (isodata p ((y nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Change representation of multiple arguments.")

 (defun f (x y z) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (and (natp x) (natp y) (symbolp z))))
   (cons (+ x y) z))

 (defun p (x y z) ; OLD when :PREDICATE is T
   (and (natp x) (natp y) (> x y) (symbolp z)))

 ;; isomorphism between naturals:
 (must-succeed*
  (must-succeed
   (isodata f (((x) (natp natp (lambda (a) a) (lambda (a) a))))))
  (must-succeed
   (isodata f (((x y) (natp natp (lambda (a) a) (lambda (a) a))))))
  (must-succeed
   (isodata p (((x) (natp natp (lambda (a) a) (lambda (a) a)))) :predicate t))
  (must-succeed
   (isodata p (((x y) (natp natp (lambda (a) a) (lambda (a) a))))
            :predicate t
            ;; without the following :UNTRANSLATE T,
            ;; we get an implementation error from directed-untranslate:
            :untranslate t))
  :with-output-off nil)
 (must-succeed*
  (defiso nat-id natp natp (lambda (a) a) (lambda (a) a))
  (must-succeed
   (isodata f (((x) nat-id))))
  (must-succeed
   (isodata f (((x y) nat-id))))
  (must-succeed
   (isodata p (((x) nat-id)) :predicate t))
  (must-succeed
   (isodata p (((x y) nat-id))
            :predicate t
            ;; without the following :UNTRANSLATE T,
            ;; we get an implementation error from directed-untranslate:
            :untranslate t)))

 ;; isomorphism between naturals and integers:
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (must-succeed
   (isodata f (((x) (natp
                     integerp
                     (lambda (n) (if (evenp n)
                                     (/ n 2)
                                   (- (/ (1+ n) 2))))
                     (lambda (i) (if (>= i 0)
                                     (* 2 i)
                                   (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata f (((x y) (natp
                       integerp
                       (lambda (n) (if (evenp n)
                                       (/ n 2)
                                     (- (/ (1+ n) 2))))
                       (lambda (i) (if (>= i 0)
                                       (* 2 i)
                                     (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata p (((x) (natp
                     integerp
                     (lambda (n) (if (evenp n)
                                     (/ n 2)
                                   (- (/ (1+ n) 2))))
                     (lambda (i) (if (>= i 0)
                                     (* 2 i)
                                   (1- (- (* 2 i))))))))
            :predicate t))
  (must-succeed
   (isodata p (((x y) (natp
                       integerp
                       (lambda (n) (if (evenp n)
                                       (/ n 2)
                                     (- (/ (1+ n) 2))))
                       (lambda (i) (if (>= i 0)
                                       (* 2 i)
                                     (1- (- (* 2 i))))))))
            :predicate t
            ;; without the following :UNTRANSLATE T,
            ;; we get an implementation error from directed-untranslate:
            :untranslate t)))
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (must-succeed
   (isodata f (((x) nat/int))))
  (must-succeed
   (isodata f (((x y) nat/int))))
  (must-succeed
   (isodata p (((x) nat/int)) :predicate t))
  (must-succeed
   (isodata p (((x y) nat/int))
            :predicate t
            ;; without the following :UNTRANSLATE T,
            ;; we get an implementation error from directed-untranslate:
            :untranslate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Tail-recursive OLD.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x)))
   (if (zp x) nil (f (1- x))))

 (defun g (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard t))
   (if (atom x) 0 (g (car x))))

 (defun h (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x)))
   (if (zp x) 0 (h (1- x))))

 (defun p (x) ; OLD when :PREDICATE is T
   (and (natp x)
        (if (zp x) nil (p (1- x)))))

 ;; isomorphism between naturals:
 (must-succeed*
  (must-succeed
   (isodata f ((x (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata g ((:result (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata h (((x :result) (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata p ((x (natp natp (lambda (y) y) (lambda (y) y)))) :predicate t))
  (defiso nat-id natp natp (lambda (m) m) (lambda (m) m))
  (must-succeed
   (isodata f ((x (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata g ((:result (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata h (((x :result) (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata p ((x (natp natp (lambda (y) y) (lambda (y) y)))) :predicate t)))

 ;; isomorphism between naturals and integers:
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (must-succeed
   (isodata f ((x nat/int))))
  (must-succeed
   (isodata g ((:result nat/int))))
  (must-succeed
   (isodata h (((x :result) nat/int))))
  (must-succeed
   (isodata p ((x nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "OLD with one (non-tail-)recursive call.")

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x)))
   (if (zp x) 0 (1+ (f (1- x)))))

 (defun and$ (x y) (and x y)) ; does not macro-expand to IF

 (defun p (x) ; OLD when :PREDICATE is T
   (and (natp x)
        (if (zp x)
            nil
          (and$ x
                (p (1- x))))))

 ;; isomorphism between naturals:
 (must-succeed*
  (must-succeed
   (isodata f ((x (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata f (((x :result) (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata f ((:result (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata p ((x (natp natp (lambda (y) y) (lambda (y) y)))) :predicate t)))
 (must-succeed*
  (defiso nat-id natp natp (lambda (y) y) (lambda (y) y))
  (must-succeed
   (isodata f ((x nat-id))))
  (must-succeed
   (isodata p ((x nat-id)) :predicate t)))

 ;; isomorphism between naturals and integers:
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (must-succeed
   (isodata f ((x (natp
                   integerp
                   (lambda (n) (if (evenp n)
                                   (/ n 2)
                                 (- (/ (1+ n) 2))))
                   (lambda (i) (if (>= i 0)
                                   (* 2 i)
                                 (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata f (((x :result) (natp
                             integerp
                             (lambda (n) (if (evenp n)
                                             (/ n 2)
                                           (- (/ (1+ n) 2))))
                             (lambda (i) (if (>= i 0)
                                             (* 2 i)
                                           (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata f ((:result (natp
                         integerp
                         (lambda (n) (if (evenp n)
                                         (/ n 2)
                                       (- (/ (1+ n) 2))))
                         (lambda (i) (if (>= i 0)
                                         (* 2 i)
                                       (1- (- (* 2 i))))))))))
  (must-succeed
   (isodata p ((x (natp
                   integerp
                   (lambda (n) (if (evenp n)
                                   (/ n 2)
                                 (- (/ (1+ n) 2))))
                   (lambda (i) (if (>= i 0)
                                   (* 2 i)
                                 (1- (- (* 2 i))))))))
            :predicate t)))
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (must-succeed
   (isodata f ((x nat/int))))
  (must-succeed
   (isodata f (((x :result) nat/int))))
  (must-succeed
   (isodata f ((:result nat/int))))
  (must-succeed
   (isodata p ((x nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "OLD with two recursive calls.")

 (defun fib (n) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp n)))
   (if (zp n)
       1
     (if (eql n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))

 (defun and$ (x y) (and x y)) ; does not macro-expand to IF

 (defun p (x) ; OLD when :PREDICATE is T
   (and (natp x)
        (if (or (eql x 0)
                (eql x 1))
            nil
          (and$ (p (- x 1))
                (p (- x 2))))))

 ;; isomorphism between naturals:
 (must-succeed*
  (must-succeed
   (isodata fib ((n (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata fib (((n :result) (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata fib ((:result (natp natp (lambda (m) m) (lambda (m) m))))))
  (must-succeed
   (isodata p ((x (natp natp (lambda (y) y) (lambda (y) y)))) :predicate t)))
 (must-succeed*
  (defiso nat-id natp natp (lambda (y) y) (lambda (y) y))
  (must-succeed
   (isodata fib ((n nat-id))))
  (must-succeed
   (isodata fib (((n :result) nat-id))))
  (must-succeed
   (isodata fib ((:result nat-id))))
  (must-succeed
   (isodata p ((x nat-id)) :predicate t)))

 (defun forth (n)
   (declare (xargs :guard (natp n)))
   (if (evenp n)
       (/ n 2)
     (- (/ (1+ n) 2))))

 (defun back (i)
   (declare (xargs :guard (integerp i)))
   (if (>= i 0)
       (* 2 i)
     (1- (- (* 2 i)))))

 ;; isomorphism between naturals and integers:
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (must-succeed
   (isodata fib ((n (natp integerp forth back)))))
  (must-succeed
   (isodata fib ((:result (natp integerp forth back)))))
  (must-succeed
   (isodata fib (((n :result) (natp integerp forth back)))))
  (must-succeed
   (isodata p ((x (natp integerp forth back))) :predicate t)))
 (must-succeed*
  (include-book "arithmetic-5/top" :dir :system)
  (defiso nat/int natp integerp forth back)
  (must-succeed
   (isodata fib ((n nat/int))))
  (must-succeed
   (isodata fib ((:result nat/int))))
  (must-succeed
   (isodata fib (((n :result) nat/int))))
  (must-succeed
   (isodata p ((x nat/int)) :predicate t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Recursive OLD with a well-founded relation that is not O<.")

 ;; well-founded relation:
 (defun o-p$ (x) (o-p x))
 (defun o<$ (x y) (declare (xargs :guard (and (o<g x) (o<g y)))) (o< x y))
 (defthm o<$-is-well-founded-relation
   (and (implies (o-p$ x) (o-p (identity x)))
        (implies (and (o-p$ x)
                      (o-p$ y)
                      (o<$ x y))
                 (o< (identity x) (identity y))))
   :rule-classes :well-founded-relation)

 (defun f (x) ; OLD when :PREDICATE is NIL
   (declare (xargs :guard (natp x) :well-founded-relation o<$))
   (if (zp x)
       nil
     (f (1- x))))

 (defun p (x) ; OLD when :PREDICATE is T
   (and (natp x)
        (if (zp x)
            nil
          (p (1- x)))))

 (must-succeed
  (isodata f ((x (natp natp (lambda (a) a) (lambda (a) a))))))

 (must-succeed*
  (defiso nat-id natp natp (lambda (a) a) (lambda (a) a))
  (isodata f ((x nat-id))))

 (must-succeed
  (isodata p ((x (natp natp (lambda (a) a) (lambda (a) a)))) :predicate t))

 (must-succeed*
  (defiso nat-id natp natp (lambda (a) a) (lambda (a) a))
  (isodata p ((x nat-id)) :predicate t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Multi-value functions.")

 (include-book "arithmetic-5/top" :dir :system)

 ;;;;;;;;;;

 (defun f (x) ; OLD with just a top-level MV
   (declare (xargs :guard (natp x)))
   (mv (+ x x) (* x x)))

 (must-succeed*
  (defiso nat-id natp natp identity identity)
  (isodata f ((x nat-id))))

 (must-succeed*
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (isodata f ((x nat/int))))

 ;;;;;;;;;;

 (defun g (x) ; OLD with a top-level IF
   (declare (xargs :guard (natp x)))
   (if (evenp x)
       (mv (+ x x) (* x x))
     (mv (* x x) (+ x x))))

 (must-succeed*
  (defiso nat-id natp natp identity identity)
  (isodata g ((x nat-id))))

 (must-succeed*
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (isodata g ((x nat/int))))

 ;;;;;;;;;;

 (defun h (x) ; OLD with a top-level RETURN-LAST
   (declare (xargs :guard (natp x)))
   (prog2$ (cw "HELLO")
           (mv (+ x x) x)))

 (must-succeed*
  (defiso nat-id natp natp identity identity)
  (isodata h ((x nat-id))))

 (must-succeed*
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (isodata h ((x nat/int))))

 ;;;;;;;;;;

 (defun k (x) ; OLD with a top-level lambda
   (declare (xargs :guard (natp x)))
   (let ((y (1+ x)))
     (mv (* y y) y)))

 (must-succeed*
  (defiso nat-id natp natp identity identity)
  (isodata k ((x nat-id))))

 (must-succeed*
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (isodata k ((x nat/int))))

 ;;;;;;;;;;

 (defun j (x)
   (declare (xargs :guard (natp x) :verify-guards nil))
   (if (zp x)
       (mv t 0)
     (mv-let (1st 2nd)
       (j (1- x))
       (mv 1st (1+ 2nd)))))

 (defthm natp-of-mv-nth-1-of-j
   (natp (mv-nth 1 (j x))))

 (verify-guards j)

 (must-succeed*
  (defiso nat-id natp natp identity identity)
  (isodata j ((x nat-id))))

 (must-succeed*
  (defiso nat/int
    natp
    integerp
    (lambda (n) (if (evenp n)
                    (/ n 2)
                  (- (/ (1+ n) 2))))
    (lambda (i) (if (>= i 0)
                    (* 2 i)
                  (1- (- (* 2 i))))))
  (isodata j ((x nat/int))))

 ;;;;;;;;;;

 (defun i (x y z)
   (declare (xargs :guard (and (natp x) (natp y) (natp z))))
   (mv z x y))

 (must-succeed*
  (defiso nat-id natp natp identity identity)
  (isodata i (((x y z :result1 :result2 :result3) nat-id))))

 (must-succeed*
  (defun nat-to-int (n) ; FORTH
    (declare (xargs :guard (natp n)))
    (if (evenp n)
        (/ n 2)
      (- (/ (1+ n) 2))))
  (defun int-to-nat (i) ; BACK
    (declare (xargs :guard (integerp i)))
    (if (>= i 0)
        (* 2 i)
      (1- (- (* 2 i)))))
  (defiso nat/int natp integerp nat-to-int int-to-nat)
  (isodata i (((x y z :result1 :result2 :result3) nat/int)))
  (isodata i (((y :result3 z) nat/int))))

 :with-output-off nil)
