; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/all-fnnames" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/all-fnnames
  :parents (std/system/term-queries)
  :short "Theorems about @(tsee all-fnnames)."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, these are theorems about @(tsee all-fnnames1),
     because @(tsee all-fnnames), as well as @(tsee all-fnnames-lst),
     is a macro that abbreviates @(tsee all-fnnames1).")
   (xdoc::p
    "We also include the following theorem
     from @('[books]/system/all-fnnames.lisp'):")
   (xdoc::@def "true-listp-all-fnnames"))

  (defthm true-listp-of-all-fnnames1-type
    (implies (true-listp acc)
             (true-listp (all-fnnames1 flg x acc)))
    :rule-classes :type-prescription)

  (defthm symbol-listp-of-all-fnnames1
    (implies (and (symbol-listp acc)
                  (if flg (pseudo-term-listp x) (pseudo-termp x)))
             (symbol-listp (all-fnnames1 flg x acc))))

  (defthm all-fnnames1-includes-acc
    (subsetp-equal acc (acl2::all-fnnames1 flg x acc)))

  ;; the monotonicity theorem needs a stronger induction hypothesis
  ;; that holds for all accumulators, hence the quantification:

  (local
   (defun-sk all-fnnames1-monotonic-acc-assertion (flg x)
     (forall (acc1 acc2)
             (implies (subsetp-equal acc1 acc2)
                      (subsetp-equal (acl2::all-fnnames1 flg x acc1)
                                     (acl2::all-fnnames1 flg x acc2))))
     :rewrite :direct))

  (local
   (defthm all-fnnames1-monotonic-acc-lemma
     (all-fnnames1-monotonic-acc-assertion flg x)))

  (defthm all-fnnames1-monotonic-acc
    (implies (subsetp-equal acc1 acc2)
             (subsetp-equal (acl2::all-fnnames1 flg x acc1)
                            (acl2::all-fnnames1 flg x acc2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable all-fnnames1))
