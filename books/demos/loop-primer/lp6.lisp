; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; (certify-book "lp6")

; See comment near the end of this file.
; cert_param: (non-acl2r)

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

(defun bags ()
  '((a b c)
    (d x e f)
    (g h i x)
    (j)
    (x k l)))

; -----------------------------------------------------------------
; LP6-1

(defthm lp6-1
  (equal (loop$ for bag in (bags) append bag)
         '(A B C D X E F G H I X J X K L))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP6-2

(defthm LP6-2
  (equal (loop$ for bag in (bags) when (member 'x bag) collect bag)
         '((D X E F) (G H I X) (X K L)))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP6-3

(defthm LP6-3
  (implies (warrant thereis$)
           (equal (loop$ for bag in (bags)
                         when (loop$ for e in bag thereis (equal e 'x))
                         collect bag)
                  '((D X E F) (G H I X) (X K L))))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP6-4

(defthm LP6-4
  (implies (warrant collect$ when$)
           (equal (loop$ for bag in (bags)
                         append
                         (loop$ for e in bag when (not (equal e 'x))
                                collect e))
                  '(A B C D E F G H I J K L)))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP6-5

(defthm LP6-5
  (implies (warrant thereis$)
           (equal (loop$ for bag in (bags)
                         when (loop$ for e in bag thereis (equal e 'x))
                         collect (car bag))
                  '(D G X)))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP6-6

(defthm LP6-6
  (implies (warrant thereis$)
           (equal (loop$ for bag in (bags)
                         collect
                         (loop$ for tail on bag
                                thereis
                                (if (equal (car tail) 'x) tail nil)))
                  '(NIL (X E F) (X) NIL (X K L))))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP6-7

(defthm LP6-7-solution-1
  (equal (loop$ for bag in (bags)
                as  i from 0 to (- (len (bags)) -1)
                sum
                (let ((n (len bag)))
                  (if (evenp i)
                      (* n n)
                      (- (* n n )))))
         17)
  :rule-classes nil)

(defthm LP6-7-solution-2
  (equal (let ((max (len (bags))))
           (loop$ for tail on (bags)
                  sum
                  (let* ((i (- max (len tail)))
                         (bag (car tail))
                         (n (len bag)))
                    (if (evenp i)
                        (* n n)
                        (- (* n n ))))))
         17)
  :rule-classes nil)

; -----------------------------------------------------------------

; LP6-8 The solution to this problem cannot be phrased as an elementary defthm
; event because the problem involves interrogating the current ACL2 world which
; is only accessible via the live STATE and you can't access the live state as
; an object in a theorem.  So we exhibit our solution in the following comment
; which just records an interaction in the top-level ACL2 read-eval-print loop.

; ACL2 !>(let ((world (w state)))
;   (loop$ for rune in (function-theory :here)
;          when (and (arity (cadr rune) world)
;                    (> (arity (cadr rune) world) 9))
;          collect (cadr rune)))
; (EVISCERATE EVISCERATE1-LST EVISCERATE1
;             UPDATE-BRR-DATA-1-BUILTIN MEMOIZE-FORM
;             SEARCH-FN SEARCH-FN-GUARD BUILD-STATE1)

; However, make-event can be used to create a suitable defthm.

(make-event
 (let* ((world (w state))
        (runes (function-theory :here))
        (names
         (loop$ for rune
                in runes
                when (let ((a (arity (cadr rune) world)))
                       (and a (> a 9)))
                collect (cadr rune))))
   `(defthm lp6-8
      (equal
       ',names
       '(FMT0 FMT0*
              EVISCERATE EVISCERATE1-LST EVISCERATE1
              UPDATE-BRR-DATA-1-BUILTIN MEMOIZE-FORM
              SEARCH-FN SEARCH-FN-GUARD BUILD-STATE1))
      :rule-classes nil)))

; -----------------------------------------------------------------
; LP6-9 The same comment as above applies here, so we exhibit our solution
; in a comment.

; ACL2 !>(loop$ for triple in (w state)
;        when (and (eq (cadr triple) 'theorem)
;                  (loop$ for fn in (all-fnnames (cddr triple))
;                         thereis (eq fn 'expt)))
;        collect (car triple))
; (APPLY$-PRIM-META-FN-EV-CONSTRAINT-462 RATIONALP-EXPT-TYPE-PRESCRIPTION
;                                        EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)

; Here is the make-event version.  We take the cdr, however, because there
; the "parallel" version of ACL2, ACL2(p) (see :DOC parallelism) has a
; different value for the car, as follows.

; ACL2: normal version
; car is APPLY$-PRIM-META-FN-EV-CONSTRAINT-464

; ACL2(p): ACL2 with parallelism (see :DOC parallelism)
; APPLY$-PRIM-META-FN-EV-CONSTRAINT-466

; Note that yet another variant of ACL2, which supports the real numbers (see
; :DOC real), has yet another value for the car.  It also has an additional
; value, REALP-EXPT-TYPE-PRESCRIPTION.  We avoid dealing with the cert_param
; comment near the top of this file, which excludes this book from ACL2(r)
; regressions.

; ACL2(r): ACL2 with the reals
; APPLY$-PRIM-META-FN-EV-CONSTRAINT-467

(make-event
 (let ((names (loop$ for triple in (w state)
                     when (and (eq (cadr triple) 'theorem)
                               (loop$ for fn
                                      in (all-fnnames (cddr triple))
                                      thereis (eq fn 'expt)))
                     collect (car triple))))
   `(defthm lp6-9
      (implies (warrant thereis$)
               (equal
                (cdr ',names) ; see comment above
                '(RATIONALP-EXPT-TYPE-PRESCRIPTION
                  EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)))
      :rule-classes nil)))
