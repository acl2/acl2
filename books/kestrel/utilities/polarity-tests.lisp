; Tests of polarity-based rewriting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "polarity")
(include-book "kestrel/utilities/deftest" :dir :system)

;;;
;;; Tests for the polarity utility
;;;

(deftest
  ;; I define my own < so that linear arithmetic doesn't know about it
  (defund my-< (x y) (< x y))
  (defund my-<= (x y) (<= x y))

  (defthmd polarity-test-theorem
    (implies (and (syntaxp (want-to-strengthen (my-< x 3))) ; a bit gross to have to reiterate the LHS here
                  (integerp x)
                  )
             (equal (my-< x 3)
                    (<= x 2)))
    :hints (("Goal" :in-theory (enable my-< my-<=))))

;this fails without the hint
  (defthmd polarity-test
    (implies (and (integerp x)
                  (my-< x 3))
             (<= x 2))
    :hints (("Goal" :in-theory (enable polarity-test-theorem))))

  ;; Test3

  (defthmd polarity-test-theorem3
    (implies (and (syntaxp (want-to-strengthen (XXXXXXXXXXX x 3)))
                  (integerp x)
                  )
             (equal (my-< x 3)
                    (<= x 2)))
    :hints (("Goal" :in-theory (enable my-< my-<=)))))

;;TODO: Uncomment these if appropriate (use must-fail):

;; ;; This now gives a hard error, as intended:
;; (local
;;  (defthm polarity-test3
;;   (implies (and (integerp x)
;;                 (my-< x 3))
;;            (<= x 2))
;;   :hints (("Goal" :in-theory (enable polarity-test-theorem3)))))


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

(deftest
  (defstub foo (x) t)
  (skip-proofs
   (defthm true-lisp-of-foo
     (true-listp (foo x))))
  ;; When trying to prove consp, this back-chains to try to prove true-listp,
  ;; which may be good.
  (defthm not-consp-when-true-listp-weaken
    (implies (and (syntaxp (want-to-weaken (consp x)))
                  (true-listp x))
             (equal (consp x)
                    (not (equal nil x)))))
  ;; This fails without not-consp-when-true-listp-weaken
  (defthm test
    (implies (not (consp (foo x)))
             (equal (foo x) nil))))
