; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/basic/pos-fix" :dir :system)
(include-book "std/lists/prefixp" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "arithmetic"))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/true-list-listp-theorems" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/basic/fix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lists
  :parents (library-extensions)
  :short "Library extensions for lists."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled car-of-repeat
  :short "Theorem about @(tsee car) applied to @(tsee repeat)."
  (equal (car (repeat n x))
         (if (zp n) nil x))
  :induct t
  :enable repeat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define append-all ((lists true-list-listp))
  :returns (list true-listp)
  :short "Append all the lists in a list, in that order."
  (cond ((endp lists) nil)
        (t (append (mbe :logic (true-list-fix (car lists))
                        :exec (car lists))
                   (append-all (cdr lists))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-repeatp ((x true-listp))
  :returns (yes/no booleanp)
  :short "Check if all the elements of a list are the same."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether it is a repetition of the same element,
     zero or more times."))
  (or (endp x)
      (endp (cdr x))
      (and (equal (car x) (cadr x))
           (list-repeatp (cdr x))))

  ///

  (defrule list-repeatp-of-repeat
    (list-repeatp (repeat n x))
    :induct t
    :enable (repeat car-of-repeat))

  (defrule list-repeatp-of-cdr
    (implies (list-repeatp x)
             (list-repeatp (cdr x))))

  (defrule list-repeatp-of-take
    (implies (and (list-repeatp list)
                  (<= (nfix n) (len list)))
             (list-repeatp (take n list)))
    :induct t
    :enable take)

  (defrule list-repeatp-of-nthcdr
    (implies (list-repeatp list)
             (list-repeatp (nthcdr n list)))
    :induct t
    :enable nthcdr)

  (defruled take-when-list-repeatp
    (implies (and (list-repeatp list)
                  (<= (nfix n) (len list)))
             (equal (take n list)
                    (repeat n (car list))))
    :induct t
    :enable (take repeat))

  (defruled nth-when-list-repeatp
    (implies (and (list-repeatp list)
                  (< (nfix n) (len list)))
             (equal (nth n list)
                    (car list)))
    :induct t
    :enable nth)

  (defruled take-of-nthcdr-when-list-repeatp
    (implies (and (list-repeatp list)
                  (posp n)
                  (<= (* 2 n) (len list)))
             (equal (take n (nthcdr n list))
                    (take n list)))
    :use ((:instance take-when-list-repeatp)
          (:instance take-when-list-repeatp (list (nthcdr n list))))
    :enable (nth-when-list-repeatp nfix)
    :disable list-repeatp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist list-list-repeatp (x)
  :guard (true-list-listp x)
  :short "Lift @(tsee list-repeatp) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is check whether each list in the list of lists
     is a repetition of the same element.
     But different lists in the list of lists may differ,
     i.e. they may be repetitions of different elements.
     This is different from saying that
     all the element of the lists in the list of lists are the same."))
  (list-repeatp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist all-of-len-p (x len)
  :guard (and (true-list-listp x)
              (natp len))
  :short "Check if all the lists in a list of lists have a given length."
  (equal (len x) (nfix len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist all-prefixp (x list)
  :guard (and (true-list-listp x)
              (true-listp list))
  :short "Check if all the lists in a list of lists are prefixes of a list."
  (prefixp x list)

  ///

  (defruled all-prefixp-when-prefixp-of-whole
    (implies (and (all-prefixp x whole1)
                  (prefixp whole1 whole2))
             (all-prefixp x whole2))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-split ((list true-listp) (chunk posp))
  :guard (integerp (/ (len list) chunk))
  :returns (lists true-list-listp)
  :short "Split a list into chunks (sublists) of a given length each."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be a whole number of chunks in the list."))
  (b* (((when (endp list)) nil)
       (chunk (mbe :logic (pos-fix chunk) :exec chunk))
       (sublist (take chunk list))
       (sublists (list-split (nthcdr chunk list) chunk)))
    (cons sublist sublists))
  :measure (len list)
  :hints (("Goal" :in-theory (enable nfix)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))

  ///

  (defrule len-of-list-split
    (implies (and (posp chunk)
                  (integerp (/ (len list) chunk)))
             (equal (len (list-split list chunk))
                    (/ (len list) chunk)))
    :induct t
    :enable (fix nfix lt-to-zero-when-divided-by-pos))

  (defrule consp-of-list-split
    (equal (consp (list-split list chunk))
           (consp list))
    :induct t)

  (defrule all-of-len-p-of-list-split
    (implies (posp chunk)
             (all-of-len-p (list-split list chunk) chunk))
    :induct t
    :enable (all-of-len-p))

  (defruled car-of-list-split
    (implies (consp list)
             (equal (car (list-split list chunk))
                    (take (pos-fix chunk) list)))
    :expand ((list-split list chunk)))

  (defruled car-of-car-of-list-split
    (implies (and (consp list)
                  (posp chunk))
             (equal (car (car (list-split list chunk)))
                    (car list)))
    :enable (car-of-list-split take))

  (defrule list-list-repeat-of-list-split
    (implies (and (list-repeatp list)
                  (posp n)
                  (integerp (/ (len list) n)))
             (list-list-repeatp (list-split list n)))
    :induct t
    :enable (list-list-repeatp nfix posp pos-gte-pos-divisor))

  (defrule list-repeatp-of-list-split
    (implies (and (list-repeatp list)
                  (posp n)
                  (integerp (/ (len list) n)))
             (list-repeatp (list-split list n)))
    :induct t
    :enable (list-repeatp
             car-of-list-split
             take-of-nthcdr-when-list-repeatp
             nfix)
    :hints ('(:use (:instance pos-gte-twice-divisor (x (len list)) (y n))))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define append-list-to-lists ((list true-listp) (lists true-list-listp))
  :returns (lists1 true-list-listp)
  :short "Append a list to each list in a list of lists."
  (cond ((endp lists) nil)
        (t (cons (append list (true-list-fix (car lists)))
                 (append-list-to-lists list (cdr lists)))))

  ///

  (defret len-of-append-list-to-lists
    (equal (len lists1)
           (len lists))
    :hints (("Goal" :induct t)))

  (defret consp-of-append-list-to-lists
    (equal (consp lists1)
           (consp lists))
    :hints (("Goal" :induct t)))

  (defret append-list-to-lists-iff
    (iff lists1 (true-list-fix lists))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define car-list ((lists true-list-listp))
  :returns (cars true-listp)
  :short "Take the first element of each list in a list of lists,
          returning the list of first elements in the same order."
  (cond ((endp lists) nil)
        (t (cons (car (car lists)) (car-list (cdr lists)))))

  ///

  (defret len-of-car-list
    (equal (len cars)
           (len lists))
    :hints (("Goal" :induct t)))

  (defret consp-of-car-list
    (equal (consp cars)
           (consp lists))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cdr-list ((lists true-list-listp))
  :returns (cdrs true-list-listp)
  :short "Remove the first element from each list in a list of lists,
          returning the list of shortened lists in the same order."
  (cond ((endp lists) nil)
        (t (cons (cdr (mbe :logic (true-list-fix (car lists))
                           :exec (car lists)))
                 (cdr-list (cdr lists)))))

  ///

  (defret len-of-cdr-list
    (equal (len cdrs)
           (len lists))
    :hints (("Goal" :induct t)))

  (defret consp-of-cdr-list
    (equal (consp cdrs)
           (consp lists))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define repeat-each ((n natp) (list true-listp))
  :returns (new-list true-listp)
  :short "Repeat each element of a list a given number of times,
          consecutively and in place."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each element of the list is replaced by @('n') consecutive copies of it,
     preserving the order of the elements.
     For instance, repeating each element of @('(a b c)') three times
     yields @('(a a a b b b c c c)')."))
  (cond ((endp list) nil)
        (t (append (repeat n (car list))
                   (repeat-each n (cdr list)))))

  ///

  (defret len-of-repeat-each
    (equal (len new-list)
           (* (nfix n) (len list)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-list-suffix ((list true-listp) (suffix true-listp))
  :returns (mv (suffixp booleanp) (prefix true-listp))
  :short "Check whether a list is a suffix of another list,
          returning the prefix if so."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('suffix') is a suffix of @('list'),
     the first result is @('t') and
     the second result is the prefix,
     i.e. the list that, with @('suffix') appended to it, yields @('list').
     Otherwise, the first result is @('nil'),
     and the second result is @('nil') too,
     but in this case the second result is irrelevant
     and should not be used.")
   (xdoc::p
    "For instance, @('(c)') is a suffix of @('(a b c)'),
     with prefix @('(a b)');
     but @('(x)') is not a suffix of @('(a b c)')."))
  (b* (((when (equal (true-list-fix list)
                     (true-list-fix suffix)))
        (mv t nil))
       ((when (endp list))
        (mv nil nil))
       ((mv suffixp prefix)
        (check-list-suffix (cdr list) suffix)))
    (if suffixp
        (mv t (cons (car list) prefix))
      (mv nil nil)))

  ///

  (defret check-list-suffix-decomposition
    (implies suffixp
             (equal (append prefix (true-list-fix suffix))
                    (true-list-fix list)))
    :hints (("Goal" :induct t)))

  (defruled check-list-suffix-alt-def
    (equal (check-list-suffix list suffix)
           (b* ((list (true-list-fix list))
                (suffix (true-list-fix suffix))
                (n (- (len list) (len suffix))))
             (if (and (<= (len suffix) (len list))
                      (equal suffix (nthcdr n list)))
                 (mv t (take n list))
               (mv nil nil))))
    :induct t
    :expand ((len list))
    :enable (nthcdr take))

  (theory-invariant
   (incompatible (:definition check-list-suffix)
                 (:rewrite check-list-suffix-alt-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-list-suffixes ((lists true-list-listp) (suffixes true-list-listp))
  :guard (equal (len lists) (len suffixes))
  :returns (mv (suffixesp booleanp) (prefixes true-list-listp))
  :short "Check whether each list in a list of lists has,
          as a suffix, the corresponding list in another list of lists,
          returning the prefixes if so."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee check-list-suffix) to two lists of lists,
     which must have the same length,
     checking each list against the corresponding suffix.
     If they all succeed, the first result is @('t')
     and the second result is the list of prefixes, in the same order;
     otherwise the first result is @('nil')
     and the second result is @('nil') but is irrelevant."))
  (b* (((when (endp lists)) (mv t nil))
       ((unless (mbt (consp suffixes))) (mv nil nil))
       ((mv suffixp prefix)
        (check-list-suffix (car lists) (car suffixes)))
       ((unless suffixp) (mv nil nil))
       ((mv suffixesp prefixes)
        (check-list-suffixes (cdr lists) (cdr suffixes)))
       ((unless suffixesp) (mv nil nil)))
    (mv t (cons prefix prefixes)))

  ///

  (defret len-of-check-list-suffixes
    (implies suffixesp
             (equal (len prefixes)
                    (len lists)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-prefix-join ((lists true-list-listp))
  :returns (mv (joinp booleanp) (join true-listp))
  :short "Least upper bound of a list of lists,
          with respect to the prefix partial order on lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lists are partially ordered by the prefix relation:
     a list is less than or equal to another list
     when the former is a prefix of the latter
     (each list being a prefix of itself).
     The join, i.e. least upper bound, of a list of lists
     is the shortest list that has all of the given lists as prefixes.
     It exists if and only if the given lists form a chain,
     i.e. they are totally ordered by the prefix relation,
     in which case the join is the longest of the given lists.
     The first result says whether the join exists;
     if it does, the second result is the join,
     otherwise the second result is @('nil') but is irrelevant.")
   (xdoc::p
    "We go through the list of lists in order,
     but the order is irrelevant to the result.
     If the list of lists is empty,
     the join is the empty list,
     which is the bottom of the partial order.
     If the list of lists is a singleton,
     the join is its only element.
     If the list of lists has two or more elements,
     we recursively calculate the join of the @(tsee cdr),
     and we compare the @(tsee car) with it:
     if neither is a prefix of the other, there is no join;
     otherwise the join is the longer of the two."))
  (b* (((when (endp lists)) (mv t nil))
       ((when (endp (cdr lists)))
        (mv t (true-list-fix (car lists))))
       ((mv joinp cdr-join) (list-prefix-join (cdr lists)))
       ((unless joinp) (mv nil nil))
       (car-list (true-list-fix (car lists))))
    (cond ((prefixp car-list cdr-join) (mv t cdr-join))
          ((prefixp cdr-join car-list) (mv t car-list))
          (t (mv nil nil))))

  ///

  (defret list-prefix-join-upper-bound
    (implies (and joinp
                  (member-equal l lists))
             (prefixp l join))
    :hints (("Goal" :induct t)))

  (defret list-prefix-join-upper-bound-all
    (implies joinp
             (all-prefixp lists join))
    :hints (("Goal"
             :induct t
             :in-theory (enable all-prefixp-when-prefixp-of-whole))))

  (in-theory (disable list-prefix-join-upper-bound
                      list-prefix-join-upper-bound-all))

  (defrule prefixp-of-car-when-list-prefix-join-of-cons
    (implies (mv-nth 0 (list-prefix-join (cons a x)))
             (prefixp a (mv-nth 1 (list-prefix-join (cons a x))))))

  (defrule all-prefixp-of-cdr-when-list-prefix-join-of-cons
    (implies (mv-nth 0 (list-prefix-join (cons a x)))
             (all-prefixp x (mv-nth 1 (list-prefix-join (cons a x)))))
    :use (:instance list-prefix-join-upper-bound-all (lists (cons a x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-to-singletons ((list true-listp))
  :returns (sing-list true-list-listp)
  :short "Turn a list into a list of singleton lists of the original elements,
          in the same order."
  :long
  (xdoc::topstring
   (xdoc::p
    "For instance, @('(a b c)') is turned into @('((a) (b) (c))')."))
  (cond ((endp list) nil)
        (t (cons (list (car list)) (list-to-singletons (cdr list)))))

  ///

  (defret len-of-list-to-singletons
    (equal (len sing-list) (len list))
    :hints (("Goal" :induct t)))

  (defret all-of-len-p-1-of-list-to-singletons
    (all-of-len-p sing-list 1)
    :hints (("Goal" :induct t))))
