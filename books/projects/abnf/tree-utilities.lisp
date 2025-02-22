; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022-2025 Provable Inc. (https://www.provable.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Added by Matt K. 7/13/2024 because of failed proof of the guard conjecture
; for CHECK-TREE-NUM-RANGE in ACL2(r):
; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "projects/abnf/notation/semantics" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/defunit" :dir :system)
(include-book "kestrel/fty/maybe-string-result" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/nat-result" :dir :system)
(include-book "kestrel/fty/string-result" :dir :system)

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)

(local (include-book "std/typed-lists/nat-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tree-utilities
  :parents (abnf)
  :short "Some utilities to manipulate ABNF trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide utilities to manipulate ABNF trees,
     more specifically to check and decompose them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defunit pass
  :short "Fixtype consisting of a single `pass' indicator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee pass-result) to indicate that
     no error occurred but no other information was produced,
     other than all the checks passed."))
  :value :pass
  :pred passp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult pass-result
  :short "Fixtype of errors and the `pass' indicator."
  :ok pass
  :pred pass-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple2
  :short "Fixtype of 2-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list))
  :pred tree-list-tuple2p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple2-result
  :short "Fixtype of errors and 2-tuples of lists of ABNF trees."
  :ok tree-list-tuple2
  :pred tree-list-tuple2-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple3
  :short "Fixtype of 3-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list))
  :pred tree-list-tuple3p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple3-result
  :short "Fixtype of errors and 3-tuples of lists of ABNF trees."
  :ok tree-list-tuple3
  :pred tree-list-tuple3-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple4
  :short "Fixtype of 4-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list))
  :pred tree-list-tuple4p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple4-result
  :short "Fixtype of errors and 4-tuples of lists of ABNF trees."
  :ok tree-list-tuple4
  :pred tree-list-tuple4-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple5
  :short "Fixtype of 5-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list)
   (5th tree-list))
  :pred tree-list-tuple5p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple5-result
  :short "Fixtype of errors and 5-tuples of lists of ABNF trees."
  :ok tree-list-tuple5
  :pred tree-list-tuple5-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple6
  :short "Fixtype of 6-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list)
   (5th tree-list)
   (6th tree-list))
  :pred tree-list-tuple6p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple6-result
  :short "Fixtype of errors and 6-tuples of lists of ABNF trees."
  :ok tree-list-tuple6
  :pred tree-list-tuple6-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple7
  :short "Fixtype of 7-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list)
   (5th tree-list)
   (6th tree-list)
   (7th tree-list))
  :pred tree-list-tuple7p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple7-result
  :short "Fixtype of errors and 7-tuples of lists of ABNF trees."
  :ok tree-list-tuple7
  :pred tree-list-tuple7-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple8
  :short "Fixtype of 8-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list)
   (5th tree-list)
   (6th tree-list)
   (7th tree-list)
   (8th tree-list))
  :pred tree-list-tuple8p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple8-result
  :short "Fixtype of errors and 8-tuples of lists of ABNF trees."
  :ok tree-list-tuple8
  :pred tree-list-tuple8-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple9
  :short "Fixtype of 9-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list)
   (5th tree-list)
   (6th tree-list)
   (7th tree-list)
   (8th tree-list)
   (9th tree-list))
  :pred tree-list-tuple9p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple9-result
  :short "Fixtype of errors and 9-tuples of lists of ABNF trees."
  :ok tree-list-tuple9
  :pred tree-list-tuple9-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-list-tuple10
  :short "Fixtype of 10-tuples of lists of ABNF trees."
  ((1st tree-list)
   (2nd tree-list)
   (3rd tree-list)
   (4th tree-list)
   (5th tree-list)
   (6th tree-list)
   (7th tree-list)
   (8th tree-list)
   (9th tree-list)
   (10th tree-list))
  :pred tree-list-tuple10p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult tree-list-tuple10-result
  :short "Fixtype of errors and 10-tuples of lists of ABNF trees."
  :ok tree-list-tuple10
  :pred tree-list-tuple10-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-info-for-error ((tree treep))
  :returns info
  :short "Information about a tree for an error result."
  :long
  (xdoc::topstring
   (xdoc::p
    "When an ABNF tree does not satisfy certain conditions,
     it is useful to return some information about the tree
     in the error result.
     Since ABNF trees may be large,
     in general we do not want to put the whole tree into the error result.
     Instead, we want to put some summary information.
     This function calculates that information."))
  (tree-case tree
             :leafterm (list :leafterm tree.get)
             :leafrule (list :leafrule tree.get)
             :nonleaf (list :nonleaf tree.rulename? (len tree.branches)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-leafterm ((tree treep))
  :returns (nats nat-list-resultp)
  :short "Check if an ABNF tree is a leaf tree,
          returning its list of natural numbers if sucessful."
  (if (tree-case tree :leafterm)
      (tree-leafterm->get tree)
    (reserrf (list :required :leafterm
                   :found (tree-info-for-error tree))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf? ((tree treep))
  :returns (rulename? acl2::maybe-string-resultp)
  :short "Check if an ABNF tree is a non-leaf tree,
          returning its rule name (or @('nil') if absent) if successful."
  (if (tree-case tree :nonleaf)
      (b* ((rulename? (tree-nonleaf->rulename? tree)))
        (if rulename?
            (rulename->get rulename?)
          nil))
    (reserrf (list :required :nonleaf
                   :found (tree-info-for-error tree))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-num-seq ((tree treep) (nats nat-listp))
  :returns (pass pass-resultp)
  :short "Check if an ABNF tree is a leaf tree
          whose natural numbers match a given sequence of natural numbers."
  (b* ((nats (nat-list-fix nats))
       ((okf tree-nats) (check-tree-leafterm tree)))
    (if (equal tree-nats nats)
        :pass
      (reserrf (list :required (list :seq nats)
                     :found (tree-info-for-error tree)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-num-range ((tree treep) (min natp) (max natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF is a leaf tree
          with a single natural number in a given range,
          returning that natural number if successful."
  (b* ((min (nfix min))
       (max (nfix max))
       (error (reserrf (list :required (list :range (list min max))
                             :found (tree-info-for-error tree))))
       ((okf nats) (check-tree-leafterm tree))
       ((unless (and (consp nats) (endp (cdr nats)))) error)
       (nat (car nats))
       ((unless (and (<= min nat) (<= nat max))) error))
    nat)
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-num-range
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-num-range-bounds
    (implies (not (reserrp nat))
             (and (<= (nfix min) nat)
                  (<= nat (nfix max))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-num-range-2 ((tree treep)
                                (min1 natp) (max1 natp)
                                (min2 natp) (max2 natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF is a leaf tree
          with a single natural number in one of two given ranges,
          returning that natural number if successful."
  (b* ((min1 (nfix min1))
       (max1 (nfix max1))
       (min2 (nfix min2))
       (max2 (nfix max2))
       (error (reserrf (list :required (list :ranges
                                             (list min1 max1)
                                             (list min2 max2))
                             :found (tree-info-for-error tree))))
       ((okf nats) (check-tree-leafterm tree))
       ((unless (and (consp nats) (endp (cdr nats)))) error)
       (nat (car nats))
       ((unless (or (and (<= min1 nat) (<= nat max1))
                    (and (<= min2 nat) (<= nat max2))))
        error))
    nat)
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-num-range-2
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-num-range-2-bounds
    (implies (not (reserrp nat))
             (or (and (<= (nfix min1) nat)
                      (<= nat (nfix max1)))
                 (and (<= (nfix min2) nat)
                      (<= nat (nfix max2)))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-num-range-3 ((tree treep)
                                (min1 natp) (max1 natp)
                                (min2 natp) (max2 natp)
                                (min3 natp) (max3 natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF is a leaf tree
          with a single natural number in one of three given ranges,
          returning that natural number if successful."
  (b* ((min1 (nfix min1))
       (max1 (nfix max1))
       (min2 (nfix min2))
       (max2 (nfix max2))
       (min3 (nfix min3))
       (max3 (nfix max3))
       (error (reserrf (list :required (list :ranges
                                             (list min1 max1)
                                             (list min2 max2)
                                             (list min3 max3))
                             :found (tree-info-for-error tree))))
       ((okf nats) (check-tree-leafterm tree))
       ((unless (and (consp nats) (endp (cdr nats)))) error)
       (nat (car nats))
       ((unless (or (and (<= min1 nat) (<= nat max1))
                    (and (<= min2 nat) (<= nat max2))
                    (and (<= min3 nat) (<= nat max3))))
        error))
    nat)
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-num-range-3
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-num-range-3-bounds
    (implies (not (reserrp nat))
             (or (and (<= (nfix min1) nat)
                      (<= nat (nfix max1)))
                 (and (<= (nfix min2) nat)
                      (<= nat (nfix max2)))
                 (and (<= (nfix min3) nat)
                      (<= nat (nfix max3)))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-num-range-4 ((tree treep)
                                (min1 natp) (max1 natp)
                                (min2 natp) (max2 natp)
                                (min3 natp) (max3 natp)
                                (min4 natp) (max4 natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF is a leaf tree
          with a single natural number in one of four given ranges,
          returning that natural number if successful."
  (b* ((min1 (nfix min1))
       (max1 (nfix max1))
       (min2 (nfix min2))
       (max2 (nfix max2))
       (min3 (nfix min3))
       (max3 (nfix max3))
       (min4 (nfix min4))
       (max4 (nfix max4))
       (error (reserrf (list :required (list :ranges
                                             (list min1 max1)
                                             (list min2 max2)
                                             (list min3 max3)
                                             (list min4 max4))
                             :found (tree-info-for-error tree))))
       ((okf nats) (check-tree-leafterm tree))
       ((unless (and (consp nats) (endp (cdr nats)))) error)
       (nat (car nats))
       ((unless (or (and (<= min1 nat) (<= nat max1))
                    (and (<= min2 nat) (<= nat max2))
                    (and (<= min3 nat) (<= nat max3))
                    (and (<= min4 nat) (<= nat max4))))
        error))
    nat)
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-num-range-4
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-num-range-4-bounds
    (implies (not (reserrp nat))
             (or (and (<= (nfix min1) nat)
                      (<= nat (nfix max1)))
                 (and (<= (nfix min2) nat)
                      (<= nat (nfix max2)))
                 (and (<= (nfix min3) nat)
                      (<= nat (nfix max3)))
                 (and (<= (nfix min4) nat)
                      (<= nat (nfix max4)))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-ichars ((tree treep) (chars acl2::stringp))
  :returns (pass pass-resultp)
  :short "Check if an ABNF tree is a leaf tree
          whose natural numbers case-insensitively match
          a string of ACL2 characters."
  (b* (((okf nats) (check-tree-leafterm tree)))
    (if (nats-match-insensitive-chars-p nats (str::explode chars))
        :pass
      (reserrf (list :required :ichars (str-fix chars)
                     :found (tree-info-for-error tree)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-schars ((tree treep) (chars acl2::stringp))
  :returns (pass pass-resultp)
  :short "Check if an ABNF tree is a leaf tree
          whose natural numbers case-sensitively match
          a string of ACL2 characters."
  (b* (((okf nats) (check-tree-leafterm tree)))
    (if (nats-match-sensitive-chars-p nats (str::explode chars))
        :pass
      (reserrf (list :required :schars (str-fix chars)
                     :found (tree-info-for-error tree)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-list-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root,
          returning the list of lists of subtrees if successful."
  (if (and (tree-case tree :nonleaf)
           (equal (tree-nonleaf->rulename? tree)
                  (if (acl2::maybe-string-fix rulename?)
                      (rulename (acl2::maybe-string-fix rulename?))
                    nil)))
      (tree-nonleaf->branches tree)
    (reserrf (if (tree-case tree :nonleaf)
                 (list :required (acl2::maybe-string-fix rulename?)
                       :found (tree-nonleaf->rulename? tree))
               (list :required :nonleaf (acl2::maybe-string-fix rulename?)
                     :found (tree-fix tree)))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf
    (implies (not (reserrp sub))
             (< (tree-list-list-count sub)
                (tree-count tree)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-1 ((treess tree-list-listp))
  :returns (sub tree-list-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          one list of subtrees,
          returning that list of subtrees if successful."
  (if (and (consp treess)
           (endp (cdr treess)))
      (tree-list-fix (car treess))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-1
    (implies (not (reserrp sub))
             (< (tree-list-count sub)
                (tree-list-list-count treess)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-2 ((treess tree-list-listp))
  :returns (sub tree-list-tuple2-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          two lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (endp (cddr treess)))
      (tree-list-tuple2 (car treess)
                        (cadr treess))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-2
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple2->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple2->2nd sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-3 ((treess tree-list-listp))
  :returns (sub tree-list-tuple3-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          three lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (endp (cdddr treess)))
      (tree-list-tuple3 (car treess)
                        (cadr treess)
                        (caddr treess))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-3
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple3->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple3->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple3->3rd sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-4 ((treess tree-list-listp))
  :returns (sub tree-list-tuple4-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          four lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (endp (cddddr treess)))
      (tree-list-tuple4 (car treess)
                        (cadr treess)
                        (caddr treess)
                        (cadddr treess))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-4
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple4->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple4->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple4->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple4->4th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-5 ((treess tree-list-listp))
  :returns (sub tree-list-tuple5-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          five lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (consp (cddddr treess))
           (endp (cdr (cddddr treess))))
      (tree-list-tuple5 (car treess)
                        (cadr treess)
                        (caddr treess)
                        (cadddr treess)
                        (car (cddddr treess)))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-5
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple5->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple5->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple5->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple5->4th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple5->5th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-6 ((treess tree-list-listp))
  :returns (sub tree-list-tuple6-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          six lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (consp (cddddr treess))
           (consp (cdr (cddddr treess)))
           (endp (cddr (cddddr treess))))
      (tree-list-tuple6 (car treess)
                        (cadr treess)
                        (caddr treess)
                        (cadddr treess)
                        (car (cddddr treess))
                        (cadr (cddddr treess)))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-6
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple6->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple6->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple6->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple6->4th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple6->5th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple6->6th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-7 ((treess tree-list-listp))
  :returns (sub tree-list-tuple7-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          seven lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (consp (cddddr treess))
           (consp (cdr (cddddr treess)))
           (consp (cddr (cddddr treess)))
           (endp (cdddr (cddddr treess))))
      (tree-list-tuple7 (car treess)
                        (cadr treess)
                        (caddr treess)
                        (cadddr treess)
                        (car (cddddr treess))
                        (cadr (cddddr treess))
                        (caddr (cddddr treess)))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-7
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple7->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple7->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple7->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple7->4th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple7->5th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple7->6th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple7->7th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-8 ((treess tree-list-listp))
  :returns (sub tree-list-tuple8-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          eight lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (consp (cddddr treess))
           (consp (cdr (cddddr treess)))
           (consp (cddr (cddddr treess)))
           (consp (cdddr (cddddr treess)))
           (endp (cddddr (cddddr treess))))
      (tree-list-tuple8 (car treess)
                        (cadr treess)
                        (caddr treess)
                        (cadddr treess)
                        (car (cddddr treess))
                        (cadr (cddddr treess))
                        (caddr (cddddr treess))
                        (cadddr (cddddr treess)))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-8
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple8->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->4th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->5th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->6th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->7th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple8->8th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-9 ((treess tree-list-listp))
  :returns (sub tree-list-tuple9-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          nine lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (consp (cddddr treess))
           (consp (cdr (cddddr treess)))
           (consp (cddr (cddddr treess)))
           (consp (cdddr (cddddr treess)))
           (consp (cddddr (cddddr treess)))
           (endp (cdr (cddddr (cddddr treess)))))
      (tree-list-tuple9 (car treess)
                        (cadr treess)
                        (caddr treess)
                        (cadddr treess)
                        (car (cddddr treess))
                        (cadr (cddddr treess))
                        (caddr (cddddr treess))
                        (cadddr (cddddr treess))
                        (car (cddddr (cddddr treess))))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-9
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple9->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->4th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->5th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->6th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->7th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->8th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple9->9th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-list-10 ((treess tree-list-listp))
  :returns (sub tree-list-tuple10-resultp)
  :short "Check if a list of lists of ABNF trees consists of
          ten lists of subtrees,
          returning those lists of subtrees if successful."
  (if (and (consp treess)
           (consp (cdr treess))
           (consp (cddr treess))
           (consp (cdddr treess))
           (consp (cddddr treess))
           (consp (cdr (cddddr treess)))
           (consp (cddr (cddddr treess)))
           (consp (cdddr (cddddr treess)))
           (consp (cddddr (cddddr treess)))
           (consp (cdr (cddddr (cddddr treess))))
           (endp (cddr (cddddr (cddddr treess)))))
      (tree-list-tuple10 (car treess)
                         (cadr treess)
                         (caddr treess)
                         (cadddr treess)
                         (car (cddddr treess))
                         (cadr (cddddr treess))
                         (caddr (cddddr treess))
                         (cadddr (cddddr treess))
                         (car (cddddr (cddddr treess)))
                         (cadr (cddddr (cddddr treess))))
    (reserrf (list :found (len treess))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-list-10
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple10->1st sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->2nd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->3rd sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->4th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->5th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->6th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->7th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->8th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->9th sub))
                     (tree-list-list-count treess))
                  (< (tree-list-count (tree-list-tuple10->10th sub))
                     (tree-list-list-count treess))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-list-1 ((trees tree-listp))
  :returns (sub tree-resultp)
  :short "Check if a list of ABNF trees consists of one subtree,
          returning that subtree if successful."
  (if (and (consp trees)
           (endp (cdr trees)))
      (tree-fix (car trees))
    (reserrf (list :found (len trees))))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-list-1
    (implies (not (reserrp sub))
             (< (tree-count sub)
                (tree-list-count trees)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-1 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of one list of subtrees,
          returning the list of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-1 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-1
    (implies (not (reserrp sub))
             (< (tree-list-count sub)
                (tree-count tree)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-2 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple2-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of two lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-2 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-2
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple2->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple2->2nd sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-3 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple3-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of three lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-3 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-3
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple3->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple3->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple3->3rd sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-4 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple4-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of four lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-4 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-4
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple4->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple4->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple4->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple4->4th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-5 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple5-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of five lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-5 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-5
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple5->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple5->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple5->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple5->4th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple5->5th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-6 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple6-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of six lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-6 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-6
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple6->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple6->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple6->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple6->4th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple6->5th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple6->6th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-7 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple7-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of seven lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-7 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-7
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple7->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple7->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple7->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple7->4th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple7->5th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple7->6th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple7->7th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-8 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple8-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of eight lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-8 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-8
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple8->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->4th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->5th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->6th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->7th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple8->8th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-9 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple9-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of nine lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-9 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-9
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple9->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->4th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->5th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->6th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->7th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->8th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple9->9th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-10 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-list-tuple10-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of ten lists of subtrees,
          returning those lists of subtrees if successful."
  (b* (((okf treess) (check-tree-nonleaf tree rulename?)))
    (check-tree-list-list-10 treess))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-10
    (implies (not (reserrp sub))
             (and (< (tree-list-count (tree-list-tuple10->1st sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->2nd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->3rd sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->4th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->5th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->6th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->7th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->8th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->9th sub))
                     (tree-count tree))
                  (< (tree-list-count (tree-list-tuple10->10th sub))
                     (tree-count tree))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-1-1 ((tree treep) (rulename? acl2::maybe-stringp))
  :returns (sub tree-resultp)
  :short "Check if an ABNF tree has a given rule name or no rule name as root
          and a list of one list of one subtree,
          returning the subtree if successful."
  (b* (((okf trees) (check-tree-nonleaf-1 tree rulename?)))
    (check-tree-list-1 trees))
  :hooks (:fix)
  ///

  (defret tree-count-of-check-tree-nonleaf-1-1
    (implies (not (reserrp sub))
             (< (tree-count sub)
                (tree-count tree)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-num-seq ((tree treep)
                                    (rulename? acl2::maybe-stringp)
                                    (nats nat-listp))
  :returns (pass pass-resultp)
  :short "Check if an ABNF tree is a non-leaf tree
          with a given optional rule name or no rule name as root
          and a list of one list of one subtree,
          where the subtree is a leaf tree
          whose natural numbers match a given sequence of natural numbers."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree rulename?)))
    (check-tree-num-seq tree nats))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-num-range ((tree treep)
                                      (rulename? acl2::maybe-stringp)
                                      (min natp) (max natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF tree is a non-leaf tree
          with a given optional rule name or no rule name as root
          and a list of one list of one subtree,
          where the subtree is a leaf tree with
          a single natural number in a range,
          returning that natural number if successful."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree rulename?)))
    (check-tree-num-range tree min max))
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-nonleaf-num-range
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-nonleaf-num-range-bounds
    (implies (not (reserrp nat))
             (and (<= (nfix min) nat)
                  (<= nat (nfix max))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-num-range-2 ((tree treep)
                                        (rulename? acl2::maybe-stringp)
                                        (min1 natp) (max1 natp)
                                        (min2 natp) (max2 natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF tree is a non-leaf tree
          with a given optional rule name or no rule name as root
          and a list of one list of one subtree,
          where the subtree is a leaf tree with
          a single natural number in one of two given ranges,
          returning that natural number if successful."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree rulename?)))
    (check-tree-num-range-2 tree min1 max1 min2 max2))
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-nonleaf-num-range-2
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-nonleaf-num-range-2-bounds
    (implies (not (reserrp nat))
             (or (and (<= (nfix min1) nat)
                      (<= nat (nfix max1)))
                 (and (<= (nfix min2) nat)
                      (<= nat (nfix max2)))))
    :rule-classes nil
    :hints
    (("Goal" :use (:instance check-tree-num-range-2-bounds
                             (tree (check-tree-nonleaf-1-1 tree rulename?)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-num-range-3 ((tree treep)
                                        (rulename? acl2::maybe-stringp)
                                        (min1 natp) (max1 natp)
                                        (min2 natp) (max2 natp)
                                        (min3 natp) (max3 natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF tree is a non-leaf tree
          with a given optional rule name or no rule name as root
          and a list of one list of one subtree,
          where the subtree is a leaf tree with
          a single natural number in one of three given ranges,
          returning that natural number if successful."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree rulename?)))
    (check-tree-num-range-3 tree min1 max1 min2 max2 min3 max3))
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-nonleaf-num-range-3
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-nonleaf-num-range-3-bounds
    (implies (not (reserrp nat))
             (or (and (<= (nfix min1) nat)
                      (<= nat (nfix max1)))
                 (and (<= (nfix min2) nat)
                      (<= nat (nfix max2)))
                 (and (<= (nfix min3) nat)
                      (<= nat (nfix max3)))))
    :rule-classes nil
    :hints
    (("Goal" :use (:instance check-tree-num-range-3-bounds
                             (tree (check-tree-nonleaf-1-1 tree rulename?)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-nonleaf-num-range-4 ((tree treep)
                                        (rulename? acl2::maybe-stringp)
                                        (min1 natp) (max1 natp)
                                        (min2 natp) (max2 natp)
                                        (min3 natp) (max3 natp)
                                        (min4 natp) (max4 natp))
  :returns (nat nat-resultp)
  :short "Check if an ABNF tree is a non-leaf tree
          with a given optional rule name or no rule name as root
          and a list of one list of one subtree,
          where the subtree is a leaf tree with
          a single natural number in one of four given ranges,
          returning that natural number if successful."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree rulename?)))
    (check-tree-num-range-4 tree min1 max1 min2 max2 min3 max3 min4 max4))
  :hooks (:fix)
  ///

  (defret natp-of-check-tree-nonleaf-num-range-4
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret check-tree-nonleaf-num-range-4-bounds
    (implies (not (reserrp nat))
             (or (and (<= (nfix min1) nat)
                      (<= nat (nfix max1)))
                 (and (<= (nfix min2) nat)
                      (<= nat (nfix max2)))
                 (and (<= (nfix min3) nat)
                      (<= nat (nfix max3)))
                 (and (<= (nfix min4) nat)
                      (<= nat (nfix max4)))))
    :rule-classes nil
    :hints
    (("Goal" :use (:instance check-tree-num-range-4-bounds
                             (tree (check-tree-nonleaf-1-1 tree rulename?)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Convenience function, tree=>string
; Takes an treep and returns an acl2::stringp.
; (More convenient for interactive use than tree->string,
; which returns an abnf::stringp which is a list of nats or rulenames.)

(defthm utf8-bytes-are-8bit
  (implies (acl2::ustring? x)
           (unsigned-byte-listp 8 (acl2::ustring=>utf8 x))))

(define tree=>string ((tree treep))
  :returns (fringe? acl2::string-resultp)
  :short "ACL2 string from the fringe of the ABNF tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a tree that with no rulename leaves
     (satisfies @(see tree-terminatedp)), this is
     similar to @('tree->string'). But instead of returning a list of numbers,
     those numbers are interpreted as Unicode codepoints and converted to
     UTF-8; then those byte values are converted to characters using code-char
     and assembled into an ACL2 string.")
   (xdoc::p
    "Another difference is that @('tree->string') can have rulenames as
     leaves.  This function will return a @('reserrp') if the tree has any
     rulename leaves.")
   (xdoc::p
    "If any number in the fringe is not a valid codepoint, return a reserrp."))
  (b* ((abnf-string (tree->string tree))
       ((unless (nat-listp abnf-string))
        (reserrf (cons "Nonterminal leaves detected" abnf-string)))
       ((unless (acl2::ustring? abnf-string))
        (reserrf (cons "Not a valid list of unicode codepoints" abnf-string)))
       (utf8-bytes (acl2::ustring=>utf8 abnf-string)))
    (nats=>string utf8-bytes)))
