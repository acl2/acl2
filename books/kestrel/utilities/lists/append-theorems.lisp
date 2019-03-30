; List Utilities -- Theorems about APPEND
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "nthcdr-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection append-theorems
  :parents (list-utilities append)
  :short "Some theorems about the built-in function @(tsee append)."
  :long
  (xdoc::topstring-p
   "The theorem @('equal-of-appends-decompose') is useful
    to decompose the equality of two @(tsee append)s
    into equalities of the appended lists,
    under the assumptions that the first two lists have the same length.")

  (defrule equal-of-appends-decompose
    (implies (equal (len a) (len b))
             (equal (equal (append a a1)
                           (append b b1))
                    (and (equal (true-list-fix a)
                                (true-list-fix b))
                         (equal a1 b1))))
    :use ((:instance lemma
           (a (true-list-fix a))
           (b (true-list-fix b))))

    :prep-lemmas
    ((defruled lemma
       (implies (and (true-listp a)
                     (true-listp b)
                     (equal (len a) (len b)))
                (equal (equal (append a a1)
                              (append b b1))
                       (and (equal a b)
                            (equal a1 b1))))
       :use ((:instance lemma-lemma
              (x (append a a1))
              (y (append b b1))
              (n (len a))))

       :prep-lemmas
       ((defruled lemma-lemma
          (implies (equal x y)
                   (equal (nthcdr n x)
                          (nthcdr n y))))))))

  (defrule append-when-not-consp-2
    (implies (and (true-listp y)
                  (not (consp y)))
             (equal (append x y)
                    (true-list-fix x)))
    :enable append))
