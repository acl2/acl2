(in-package "ACL2")

#|

Author: Sandip Ray
Date: Sat Nov 18 11:38:39 2006

In this book, I explore how defexec can be used for functions that are uniquely
defined in a particular domain.  In fact, my macro defpun-exec should have been
able to handle such things.  But it does not, because I do not support gdomain
yet.  I can change that, but before doing that we need to do something with
defpun.  It is really the macro defpun that's a little bit problematic here.
It does not allow the user to write intermediate lemmas and hints.  However, I
show how, if it did, we could have used the macro itself via defexec.

|#


(include-book "misc/defpun" :dir :system)

(include-book "std/testing/must-fail" :dir :system)

;; This one fails.  So I wrap this in must-fail.

(must-fail
 (defpun fact (x)
   (declare (xargs :gdomain (natp x)
                   :measure (nfix x)))
   (if (equal x 0) 1 (* x (fact (- x 1))))))

;; If I look at the translation, then here's what I get, and the final
;; verify-guards fails.  Here I show how I could introduce all the events.

;; ACL2 !>:trans1 (defpun fact (x)
;;    (declare (xargs :gdomain (natp x)
;;                    :measure (nfix x)))
;;    (if (equal x 0) 1 (* x (fact (- x 1))))))

;;  (ENCAPSULATE
;;       NIL
;;       (DEFUN THE-FACT (X)
;;              (DECLARE (XARGS :MEASURE (IF (NATP X) (NFIX X) 0)
;;                              :GUARD (NATP X)
;;                              :VERIFY-GUARDS NIL))
;;              (IF (NATP X)
;;                  (IF (EQUAL X 0)
;;                      1 (* X (THE-FACT (- X 1))))
;;                  'UNDEF))
;;       (ENCAPSULATE ((FACT (X) T))
;;                    (LOCAL (DEFUN-NONEXEC FACT (X) (THE-FACT X)))
;;                    (DEFTHM FACT-DEF
;;                            (IMPLIES (NATP X)
;;                                     (EQUAL (FACT X)
;;                                            (IF (EQUAL X 0)
;;                                                1 (* X (FACT (- X 1))))))
;;                            :RULE-CLASSES :DEFINITION))
;;       (DEFTHM FACT-IS-UNIQUE
;;               (IMPLIES (NATP X)
;;                        (EQUAL (FACT X) (THE-FACT X))))
;;       (IN-THEORY (DISABLE FACT-IS-UNIQUE))
;;       (VERIFY-GUARDS THE-FACT))
;; ACL2 !>

(DEFUN THE-FACT (X)
  (DECLARE (XARGS :MEASURE (IF (NATP X) (NFIX X) 0)
                  :GUARD (NATP X)
                  :VERIFY-GUARDS NIL))
  (IF (NATP X)
      (IF (EQUAL X 0)
          1 (* X (THE-FACT (- X 1))))
      'UNDEF))

(ENCAPSULATE
 ((FACT (X) T))
 (LOCAL (DEFUN-NONEXEC FACT (X) (THE-FACT X)))
 (DEFTHM FACT-DEF
   (IMPLIES (NATP X)
            (EQUAL (FACT X)
                   (IF (EQUAL X 0)
                       1 (* X (FACT (- X 1))))))
   :RULE-CLASSES :DEFINITION))

(DEFTHM FACT-IS-UNIQUE
  (IMPLIES (NATP X)
           (EQUAL (FACT X) (THE-FACT X))))

(IN-THEORY (DISABLE FACT-IS-UNIQUE))

;; Here is the lemma I needed to get the verify-guards below to work.  However,
;; I don't understand why they did it with verify-guards since defpun as I
;; understand it, was for the logic.  This provides a way of course to execute
;; the-fact, but so what?  The paper does not seem to explain that.  (Talk to
;; J?)  Anyhow this lemma is all that is necessary to "admit" the defpun above.

(defthm natp-x-implies-natp-the-fact
  (implies (natp x)
           (natp (the-fact x)))
  :rule-classes :type-prescription)

(VERIFY-GUARDS THE-FACT)

;; OK, but as I mentioned in my previous comment above, I did not quite see
;; what verify-guards does with the-fact.  We can execute the-fact above, for
;; sure, but so what?  I guess they had the following in mind, but did not do
;; it since they did not have mbe at the time.  (Talk to J.)  Here I define
;; executable-fact and can execute it.


(defexec executable-fact (x)
  (declare (xargs :guard (natp x)
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive.  Instead, added exec-xargs below.
;                 :measure (nfix x)
                  :verify-guards nil)
           (exec-xargs :measure (nfix x)))
  (mbe :logic (fact x)
       :exec (if (equal x 0) 1 (* x (executable-fact (- x 1))))))

(defthm natp-x-implies-natp-executable-fact
  (implies (natp x)
           (natp (executable-fact x)))
  :rule-classes :type-prescription
 :hints (("Goal"
           :induct (the-fact x))))

(verify-guards executable-fact)
