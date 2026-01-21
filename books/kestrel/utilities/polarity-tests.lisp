; Tests of polarity-based rewriting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "polarity")
(include-book "kestrel/utilities/deftest" :dir :system)

;; Test want-to-strengthen:
(deftest
  ;; I define my own version of < so that linear arithmetic doesn't know about it:
  (defund my-< (x y) (< x y))
  ;; Unlike <=, this is not a macro:
  (defund my-<= (x y) (<= x y))

  ;; Given the assumption of (integerp x), the LHS and RHS of this rule are
  ;; equivalent.  Without the hyp, the RHS is stronger.  Whether we prefer the
  ;; LHS or the RHS may depend on the "polarity" of the term.  If it's a hyp,
  ;; we prefer the stronger form (gives more information).  If it's a
  ;; conclusion, we prefer the weaker form (easier to prove, all else being equal).
  (defthmd polarity-rule
    (implies (and (syntaxp (want-to-strengthen (my-< x 3))) ; a bit gross to have to reiterate the LHS here
                  (integerp x)
                  )
             (equal (my-< x 3)
                    (my-<= x 2)))
    :hints (("Goal" :in-theory (enable my-< my-<=))))

  ;; fails (polarity-rule is disabled)
  (must-fail
    (defthmd polarity-test
      (implies (and (integerp x)
                    (my-< x 3))
               (my-<= x 2))))

  ;; works (note the hint).  polarity-rule strenghtens the hyp.
  (defthmd polarity-test
    (implies (and (integerp x)
                  (my-< x 3))
             (my-<= x 2))
    :hints (("Goal" :in-theory (enable polarity-rule)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test want-to-weaken:
(deftest
  ;; I define my own version of < so that linear arithmetic doesn't know about it:
  (defund my-< (x y) (< x y))
  ;; Unlike <=, this is not a macro:
  (defund my-<= (x y) (<= x y))

  ;; Given the assumption of (integerp x), the LHS and RHS of this rule are
  ;; equivalent.  Without the hyp, the RHS is stronger.  Whether we prefer the
  ;; LHS or the RHS may depend on the "polarity" of the term.  If it's a hyp,
  ;; we prefer the stronger form (gives more information).  If it's a
  ;; conclusion, we prefer the weaker form (easier to prove, all else being equal).
  (defthmd polarity-rule2
    (implies (and (syntaxp (want-to-weaken (my-<= x 2))) ; a bit gross to have to reiterate the LHS here
                  (integerp x)
                  )
             (equal (my-<= x 2)
                    (my-< x 3)))
    :hints (("Goal" :in-theory (enable my-< my-<=))))

  ;; fails (polarity-rule2 is disabled)
  (must-fail
    (defthmd polarity-test2
      (implies (and (integerp x)
                    (my-< x 3))
               (my-<= x 2))))

  ;; works (note the hint).  polarity-rule2 weakens the conclusion.
  (defthmd polarity-test2
    (implies (and (integerp x)
                  (my-< x 3))
             (my-<= x 2))
    :hints (("Goal" :in-theory (enable polarity-rule2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test error checking:
(deftest
  ;; I define my own version of < so that linear arithmetic doesn't know about it:
  (defund my-< (x y) (< x y))

  (defthmd polarity-rule-bad
    (implies (and (syntaxp (want-to-strengthen (XXX x 3)))
                  (integerp x)
                  )
             (equal (my-< x 3)
                    (<= x 2)))
    :hints (("Goal" :in-theory (enable my-<))))

  ;; throws a hard error, as intended (can't translate the call to XXX):
  (must-fail
    (defthm polarity-test-bad
      (implies (and (integerp x)
                    (my-< x 3))
               (<= x 2))
      :hints (("Goal" :in-theory (enable polarity-rule-bad))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest
  (defstub foo (x) t)
  (skip-proofs
   (defthm true-lisp-of-foo
     (true-listp (foo x))))
  ;; When trying to prove consp, this back-chains to try to prove true-listp,
  ;; which may sometimes be good.
  (defthm not-consp-when-true-listp-weaken
    (implies (and (syntaxp (want-to-weaken (consp x)))
                  (true-listp x))
             (equal (consp x)
                    (not (equal nil x)))))
  ;; This fails without not-consp-when-true-listp-weaken
  (defthm test
    (implies (not (consp (foo x)))
             (equal (foo x) nil))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;TODO: Clean these up.  Uncomment these if appropriate (use must-fail):

;; (defthm integerp-hack
;;   (implies (integerp x)
;;            (equal (< x 3)
;;                   (<= x 2))))

;; (defstub foo (x) t)


;; ;fires, and we want it to
;; (thm
;;  (implies (and (integerp x)
;;                (foo x)
;;                )
;;           (<= 3 x)))

;; ;fires, but we don't want it to
;; (thm
;;  (implies (and (integerp x)
;;                (<= 3 x)
;;                )
;;           (foo x)))

;; (in-theory (disable integerp-hack))

;; (defthm integerp-hack-with-polarity
;;   (implies (and (syntaxp (term-appears-as-a-hyp '(< x '3) mfc state))
;;                 (integerp x)
;;                 )
;;            (equal (< x 3)
;;                   (<= x 2))))

;; ;fires, and we want it to
;; (thm
;;  (implies (and (integerp x)
;;                (foo x)
;;                )
;;           (<= 3 x)))

;; ;does not fire, and indeed we don't want it to!
;; (thm
;;  (implies (and (integerp x)
;;                (<= 3 x)
;;                )
;;           (foo x)))

;;
;; test of the new version
;;

;; (local
;;  (defthmd polarity-test-theorem4
;;    (implies (and (syntaxp (want-to-strengthen (my-< x 3)))  ; a bit gross to have to reiterate the LHS here
;;                  (integerp x)
;;                  )
;;             (equal (my-< x 3)
;;                    (<= x 2)))
;;    :hints (("Goal" :in-theory (enable my-< my-<=)))))

;; (local
;;  (defthmd polarity-test4
;;   (implies (and (integerp z)
;;                 (my-<  (+ z 5) 3))
;;            (<=  (+ z 5) 2))
;;   ;; fails without the hint:
;;   :hints (("Goal" :in-theory (enable polarity-test-theorem4)))))

;; ;TODO: Test make defthm-strengthen and defthm-weaken
