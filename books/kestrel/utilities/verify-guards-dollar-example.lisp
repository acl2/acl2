; An example of the need for verify-guards$
;
; Copyright (C) 2017-2021 Kestrel Institute
; Copyright (C) 2017, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Matt Kaufmann

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This file shows an example of when verify-guards$ succeeds even though
;; verify-guards fails.

;; Eric reported this to Matt on 3/1/17.  Matt doesn't think verify-guards
;; should be changed to make this example succeed, because hints attach to
;; individual goals in the waterfall, not to the preprocessing done in
;; producing guards proof obilgations.  There is a precedent: hints on "Goal"
;; do not apply to forcing rounds.  This may be a precedent that is
;; unappealing, but it's a precedent that, together with the point above about
;; goals in the waterfall, is good enough for Matt.

(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "verify-guards-dollar")

;;normalization will replace this with nil
(defun empty () (declare (xargs :guard t)) nil)

(defun foo (x)
  (declare (xargs :normalize nil
                  :guard (true-listp x)))
  (if (member (empty) x)
      (foo (cdr x))
    0))

(defun foo-copy (x)
  (declare (xargs :normalize nil
                  :verify-guards nil
                  :guard (true-listp x)))
  (if (member (empty) x)
      (foo-copy (cdr x))
    0))

(defthm foo-becomes-foo-copy
  (equal (foo x)
         (foo-copy x)))

;(set-gag-mode nil)

;;this fails!  Note this output:
;;
;; "The non-trivial part of the guard conjecture for FOO-COPY, given the :executable-counterpart of EMPTY and primitive type reasoning, is"
;;
;; but (:E EMPTY) is not in the theory supplied to the verify-guards (I deliberately used a very restricted theory!).

(must-fail
 (verify-guards foo-copy
   :hints (("Goal"
            :use (:instance (:guard-theorem foo))
            :in-theory '(foo-becomes-foo-copy)
            :do-not '(generalize eliminate-destructors)
            :do-not-induct t))))

;; These work:

(deftest
  (verify-guards$ foo-copy
                  :hints (("Goal"
                           :use (:instance (:guard-theorem foo))
                           :in-theory '(foo-becomes-foo-copy)
                           :do-not '(generalize eliminate-destructors)
                           :do-not-induct t))))

(deftest
  (verify-guards$ foo-copy
                  :hints (("Goal"
                           :use (:instance (:guard-theorem foo))
                           :in-theory '(foo-becomes-foo-copy)
                           :do-not '(generalize eliminate-destructors)
                           :do-not-induct t))
                  :otf-flg t
                  :guard-debug t))
