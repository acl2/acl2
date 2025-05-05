; Tests of rewriter-basic-smt
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-stp)

(include-book "rewriter-basic-smt")
(include-book "kestrel/utilities/assert-with-stobjs" :dir :system)

(include-book "bv-rules-axe") ; to register known-booleans
(local (include-book "kestrel/bv/bvlt" :dir :system))
;(local (include-book "kestrel/bv/top" :dir :system))

;; todo: also translate the term?
;; todo: auto-generate this for each rewrietr?
(defmacro simplify-term-to-term-basic-smt-wrapper (term
                                                    &key
                                                    (assumptions 'nil)
                                                    (rule-alist 'nil)
                                                    (interpreted-function-alist 'nil)
                                                    (known-booleans '(known-booleans (w state)))
                                                    (normalize-xors 'nil)
                                                    (limits 'nil)
                                                    (memoizep 't)
                                                    (count-hits 'nil)
                                                    (print 't)
                                                    (monitor 'nil)
                                                    (fns-to-elide 'nil))
  `(simplify-term-to-term-basic-smt ,term
                                    ,assumptions
                                    ,rule-alist
                                    ,interpreted-function-alist
                                    ,known-booleans
                                    ,normalize-xors
                                    ,limits
                                    ,memoizep
                                    ,count-hits
                                    ,print
                                    ,monitor
                                    ,fns-to-elide
                                    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules used in the examples below:

(defthm rule
  (implies (axe-smt (equal (bvchop 32 x) (bvchop 32 y)))
           (not (bvlt 32 x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthmd if-same
  (equal (if test x x) x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: improve assert-equal-with-stobjs2 to (optionally) turn on guard-checking
(assert-equal-with-stobjs2
  (simplify-term-to-term-basic-smt-wrapper '(not (bvlt '32 (bvplus '32 x y) (bvplus '32 y x)))
                                           :rule-alist (make-rule-alist! '(rule) (w state))
                                           :monitor '(rule))

  *t*
  :stobjs (state))

;; this one fails to apply the rule, because the hyp is not provable
(assert-equal-with-stobjs2
  (simplify-term-to-term-basic-smt-wrapper '(not (bvlt '32 (bvplus '32 x y) (bvplus '32 y z))) ; note the z!
                                           :rule-alist (make-rule-alist! '(rule) (w state))
                                           :monitor '(rule))
  '(not (bvlt '32 (bvplus '32 x y) (bvplus '32 y z)))
  :stobjs (state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; using a condition in the then-branch
(assert-equal-with-stobjs2
  (simplify-term-to-term-basic-smt-wrapper '(if (equal (bvplus '32 x z) (bvplus '32 z y)) ; implies that x and y have the same low 32 bits
                                                (not (bvlt '32 x y))
                                              't)
                                           :rule-alist (make-rule-alist! '(rule if-same) (w state))
                                           :memoizep nil ; todo: try t
                                           )
  *t*
  :stobjs (state))

;; no change because the (negated) info in the hyp doesn't help us in the else branch
(assert-equal-with-stobjs2
  (simplify-term-to-term-basic-smt-wrapper '(if (equal (bvplus '32 x z) (bvplus '32 z y)) ; implies that x and y have the same low 32 bits
                                                't
                                              (not (bvlt '32 x y)))
                                           :rule-alist (make-rule-alist! '(rule if-same) (w state))
                                           :memoizep nil ; todo: try t
                                           )
  '(if (equal (bvplus '32 x z) (bvplus '32 z y)) ; implies that x and y have the same low 32 bits
       't
     (not (bvlt '32 x y)))
  :stobjs (state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; using a condition in the else-branch
(assert-equal-with-stobjs2
  (simplify-term-to-term-basic-smt-wrapper '(if (not (equal (bvplus '32 x z) (bvplus '32 z y))) ; implies that x and y do not have the same low 32 bits
                                                't
                                              (not (bvlt '32 x y)))
                                           :rule-alist (make-rule-alist! '(rule if-same) (w state))
                                           :memoizep nil ; todo: try t
                                           )
  *t*
  :stobjs (state))

;; no change because the info in the hyp doesn't help us in the then branch
(assert-equal-with-stobjs2
  (simplify-term-to-term-basic-smt-wrapper '(if (not (equal (bvplus '32 x z) (bvplus '32 z y))) ; implies that x and y do not have the same low 32 bits
                                                (not (bvlt '32 x y))
                                              't)
                                           :rule-alist (make-rule-alist! '(rule if-same) (w state))
                                           :memoizep nil ; todo: try t
                                           )
  '(if (not (equal (bvplus '32 x z) (bvplus '32 z y))) ; implies that x and y have the same low 32 bits
       (not (bvlt '32 x y))
     't)
  :stobjs (state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: can we do something like this, without causing a loop?  maybe a variant of axe-smt that says "don't rewrite"
(defthmd rule2
  (implies (axe-smt (bvlt 32 x y))
           (bvlt 32 x y))
  :hints (("Goal" :in-theory (enable bvlt))))
