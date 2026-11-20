; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "normalization")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ stream-safe
  :parents (normalization)
  :short "The Stream-Safe Text Format and the Stream-Safe Text Process."
  :long
  (xdoc::topstring
   (xdoc::p
    "To put text in a normalization form (see @(see normalization)),
     the non-starters between two starters have to be sorted,
     so they all have to be held in memory at once.
     The Unicode Standard puts no bound on how many there can be.
     [UAX #15, Section 13] defines a format of text in which
     there are at most 30 of them in a row,
     and a process that puts any text in that format.")
   (xdoc::p
    "Text is in Stream-Safe Text Format [UAX #15, UAX15-D3]
     if its Normalization Form KD (NFKD: see @(tsee nfkd))
     has no more than 30 non-starters in a row.
     The count is taken in the NFKD form, not in the text as written:
     a code point of the text can be replaced, in that form,
     by several non-starters, or by none.
     See @(tsee stream-safe-p).")
   (xdoc::p
    "The Stream-Safe Text Process [UAX #15, UAX15-D4]
     goes through the text once
     and inserts U+034F COMBINING GRAPHEME JOINER (CGJ),
     which is a starter with no decomposition,
     where a run of non-starters would become too long.
     See @(tsee stream-safe-process).")
   (xdoc::p
    "We prove, for every supported version of Unicode,
     that the process gives text in Stream-Safe Text Format,
     and that it leaves text in that format unchanged;
     so applying the process a second time changes nothing.
     See @(see stream-safe-theorems).
     We do not prove what [UAX #15, Section 13] says
     about the process and the normalization forms.")
   (xdoc::p
    "A starter is a code point
     whose canonical combining class is 0 (see @(tsee starter-p));
     a non-starter is any other code point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stream-safe-constants
  :short "The constants of the Stream-Safe Text Format
          [UAX #15, Section 13]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the largest number of non-starters in a row
     in text that is in Stream-Safe Text Format,
     and the code point U+034F COMBINING GRAPHEME JOINER,
     which the Stream-Safe Text Process inserts."))

  (defconst *stream-safe-limit* 30)

  (defconst *combining-grapheme-joiner* #x34F))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leading-non-starter-count ((cps code-point-listp) (ver versionp))
  :returns (count natp :rule-classes (:rewrite :type-prescription))
  :short "The number of non-starters at the start of a list of code points,
          in a version of Unicode."
  (cond ((endp cps) 0)
        ((starter-p (car cps) ver) 0)
        (t (+ 1 (leading-non-starter-count (cdr cps) ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define non-starter-count-after ((count natp)
                                 (cps code-point-listp)
                                 (ver versionp))
  :returns (new-count natp :rule-classes (:rewrite :type-prescription))
  :short "The number of non-starters in a row
          at the end of a list of code points,
          given the number of them just before the list,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the list has no starters,
     this is the given number plus the length of the list.
     Otherwise it is the number of non-starters at the end of the list,
     and the given number does not matter.")
   (xdoc::p
    "This is how step 3.d of the Stream-Safe Text Process
     [UAX #15, UAX15-D4] updates its count of non-starters,
     with the decomposition of a code point as the list."))
  (cond ((endp cps) (lnfix count))
        ((starter-p (car cps) ver)
         (non-starter-count-after 0 (cdr cps) ver))
        (t (non-starter-count-after (+ 1 (lnfix count)) (cdr cps) ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define non-starter-runs-within-p ((count natp)
                                   (cps code-point-listp)
                                   (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points
          has no more than 30 non-starters in a row,
          given the number of them just before the list,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The non-starters at the start of the list
     are counted together with the ones just before the list,
     whose number is the first argument."))
  (cond ((endp cps) t)
        ((starter-p (car cps) ver)
         (non-starter-runs-within-p 0 (cdr cps) ver))
        (t (and (< (lnfix count) *stream-safe-limit*)
                (non-starter-runs-within-p (+ 1 (lnfix count))
                                           (cdr cps)
                                           ver))))
  :hooks nil ; done below

  ///

  (fty::deffixequiv non-starter-runs-within-p
    :hints (("Goal"
             :induct (non-starter-runs-within-p count cps ver)
             :expand ((non-starter-runs-within-p count
                                                 (code-point-list-fix cps)
                                                 ver)
                      (non-starter-runs-within-p (nfix count) cps ver))
             :in-theory (enable non-starter-runs-within-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stream-safe-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points is in Stream-Safe Text Format,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its Normalization Form KD (NFKD)
     has no more than 30 non-starters in a row [UAX #15, UAX15-D3].")
   (xdoc::p
    "It is the same to check this
     on the compatibility decomposition of the list,
     before it is put in canonical order:
     see @(see stream-safe-theorems)."))
  (non-starter-runs-within-p 0 (nfkd cps ver) ver)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stream-safe-process-from ((count natp)
                                  (cps code-point-listp)
                                  (ver versionp))
  :returns (new-cps code-point-listp)
  :short "The Stream-Safe Text Process on a list of code points,
          given the number of non-starters in a row just before the list,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is step 3 of the process [UAX #15, UAX15-D4].
     For each code point of the list:")
   (xdoc::ol
    (xdoc::li
     "We take the NFKD form of the code point.")
    (xdoc::li
     "If the count plus the number of non-starters
      at the start of that form is greater than 30,
      we put U+034F COMBINING GRAPHEME JOINER in the result,
      and we set the count to 0.")
    (xdoc::li
     "We put the code point in the result.")
    (xdoc::li
     "If that form has no starters,
      we add its length to the count;
      otherwise we set the count
      to the number of non-starters at the end of that form.
      See @(tsee non-starter-count-after)."))
   (xdoc::p
    "The count is the number of non-starters in a row
     at the end of the NFKD form of the result so far."))
  (b* ((count (lnfix count))
       ((when (endp cps)) nil)
       (cp (code-point-fix (car cps)))
       (decomposed (nfkd (list cp) ver))
       (insert (> (+ count (leading-non-starter-count decomposed ver))
                  *stream-safe-limit*))
       (count-before (if insert 0 count))
       (count-after (non-starter-count-after count-before decomposed ver))
       (rest (stream-safe-process-from count-after (cdr cps) ver)))
    (if insert
        (list* *combining-grapheme-joiner* cp rest)
      (cons cp rest)))
  :measure (len cps)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define stream-safe-process ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :short "The Stream-Safe Text Process on a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the process of [UAX #15, UAX15-D4]:
     it starts with a count of 0 (step 2),
     and goes through the code points of the list (step 3:
     see @(tsee stream-safe-process-from)).
     The result for the empty list is the empty list (step 1)."))
  (stream-safe-process-from 0 cps ver)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection non-starter-counts-and-canonical-ordering
  :short "Canonical ordering does not change
          where the starters and the non-starters of a list are."
  :long
  (xdoc::topstring
   (xdoc::p
    "Canonical ordering only exchanges adjacent non-starters
     [Unicode, D108, D109].
     So the three functions that count non-starters in a row
     give the same results on a list and on its canonical order."))

  ;; Putting a non-starter in its place in a list
  ;; is the same, for the counts, as putting it at the start of the list.
  ;; The count changes as we go through the list,
  ;; so we use an induction in which it does.

  (local
   (define insert-induct ((count natp)
                          (cp code-point-p)
                          (cps code-point-listp)
                          (ver versionp))
     :returns (irrelevant null)
     (b* (((when (endp cps)) nil)
          (next-ccc (canonical-combining-class (car cps) ver)))
       (if (and (not (equal next-ccc 0))
                (< next-ccc (canonical-combining-class cp ver)))
           (insert-induct (+ 1 (lnfix count)) cp (cdr cps) ver)
         nil))
     :measure (len cps)
     :hooks nil))

  (defrulel leading-non-starter-count-of-canonical-order-insert
    (implies (not (starter-p cp ver))
             (equal (leading-non-starter-count
                     (canonical-order-insert cp cps ver)
                     ver)
                    (+ 1 (leading-non-starter-count cps ver))))
    :induct (canonical-order-insert cp cps ver)
    :enable (canonical-order-insert
             leading-non-starter-count
             starter-p))

  (defrulel non-starter-count-after-of-canonical-order-insert
    (implies (not (starter-p cp ver))
             (equal (non-starter-count-after
                     count
                     (canonical-order-insert cp cps ver)
                     ver)
                    (non-starter-count-after (+ 1 (nfix count)) cps ver)))
    :induct (insert-induct count cp cps ver)
    :enable (insert-induct
             canonical-order-insert
             non-starter-count-after
             starter-p))

  (defrulel non-starter-runs-within-p-of-canonical-order-insert
    (implies (not (starter-p cp ver))
             (equal (non-starter-runs-within-p
                     count
                     (canonical-order-insert cp cps ver)
                     ver)
                    (and (< (nfix count) *stream-safe-limit*)
                         (non-starter-runs-within-p (+ 1 (nfix count))
                                                    cps
                                                    ver))))
    :induct (insert-induct count cp cps ver)
    :enable (insert-induct
             canonical-order-insert
             non-starter-runs-within-p
             starter-p))

  (defrule leading-non-starter-count-of-canonical-order
    (equal (leading-non-starter-count (canonical-order cps ver) ver)
           (leading-non-starter-count cps ver))
    :induct (canonical-order cps ver)
    :enable (canonical-order
             leading-non-starter-count
             starter-p))

  (defrule non-starter-count-after-of-canonical-order
    (equal (non-starter-count-after count (canonical-order cps ver) ver)
           (non-starter-count-after count cps ver))
    :induct (non-starter-count-after count cps ver)
    :enable (canonical-order
             non-starter-count-after
             starter-p))

  (defrule non-starter-runs-within-p-of-canonical-order
    (equal (non-starter-runs-within-p count (canonical-order cps ver) ver)
           (non-starter-runs-within-p count cps ver))
    :induct (non-starter-runs-within-p count cps ver)
    :enable (canonical-order
             non-starter-runs-within-p
             starter-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stream-safe-theorems
  :short "Theorems about the Stream-Safe Text Format
          and the Stream-Safe Text Process."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of code points is in Stream-Safe Text Format
     exactly when its compatibility decomposition
     has no more than 30 non-starters in a row:
     it is not necessary to put the decomposition in canonical order.")
   (xdoc::p
    "The result of the Stream-Safe Text Process
     is in Stream-Safe Text Format.
     This relies on a fact about the tables,
     which we check on every code point, for each version:
     the compatibility decomposition of a single code point
     has no more than 30 non-starters in a row.
     (Otherwise no insertion between code points could be enough.)
     It also relies on two facts about U+034F COMBINING GRAPHEME JOINER,
     proved by evaluation for each version:
     it is a starter, and it has no decomposition.")
   (xdoc::p
    "The process leaves unchanged
     a list that is in Stream-Safe Text Format.
     So applying the process twice
     is the same as applying it once."))

  (defruled stream-safe-p-in-terms-of-decompose
    (equal (stream-safe-p cps ver)
           (non-starter-runs-within-p 0 (decompose cps t ver) ver))
    :enable (stream-safe-p
             nfkd))

  ;; The check of a list that is made of two lists.

  (defrulel non-starter-runs-within-p-of-append
    (equal (non-starter-runs-within-p count (append cps1 cps2) ver)
           (and (non-starter-runs-within-p count cps1 ver)
                (non-starter-runs-within-p
                 (non-starter-count-after count cps1 ver)
                 cps2
                 ver)))
    :induct (non-starter-runs-within-p count cps1 ver)
    :enable (non-starter-runs-within-p
             non-starter-count-after))

  ;; If a list passes the check with some count before it,
  ;; it passes with any count that leaves room
  ;; for the non-starters at the start of the list.
  ;; If a list passes with a count that is not over the limit,
  ;; the count leaves room for those non-starters,
  ;; and the count after the list is not over the limit either.

  (local
   (define two-counts-induct ((count1 natp)
                              (count2 natp)
                              (cps code-point-listp)
                              (ver versionp))
     :returns (irrelevant null)
     (cond ((endp cps) nil)
           ((starter-p (car cps) ver) nil)
           (t (two-counts-induct (+ 1 (lnfix count1))
                                 (+ 1 (lnfix count2))
                                 (cdr cps)
                                 ver)))
     :hooks nil))

  (defruledl non-starter-runs-within-p-with-other-count
    (implies (and (non-starter-runs-within-p count1 cps ver)
                  (<= (+ (nfix count2) (leading-non-starter-count cps ver))
                      *stream-safe-limit*))
             (non-starter-runs-within-p count2 cps ver))
    :induct (two-counts-induct count1 count2 cps ver)
    :enable (two-counts-induct
             non-starter-runs-within-p
             leading-non-starter-count
             nfix
             fix))

  (defruledl non-starter-runs-within-p-when-within-from-0
    (implies (and (syntaxp (not (equal count ''0)))
                  (non-starter-runs-within-p 0 cps ver)
                  (<= (+ (nfix count) (leading-non-starter-count cps ver))
                      *stream-safe-limit*))
             (non-starter-runs-within-p count cps ver))
    :enable non-starter-runs-within-p-with-other-count)

  (defruledl leading-non-starter-count-when-non-starter-runs-within-p
    (implies (and (non-starter-runs-within-p count cps ver)
                  (natp count)
                  (<= count *stream-safe-limit*))
             (<= (+ count (leading-non-starter-count cps ver))
                 *stream-safe-limit*))
    :rule-classes :linear
    :induct (non-starter-runs-within-p count cps ver)
    :enable (non-starter-runs-within-p
             leading-non-starter-count
             nfix
             fix))

  (defruledl non-starter-count-after-when-non-starter-runs-within-p
    (implies (and (non-starter-runs-within-p count cps ver)
                  (natp count)
                  (<= count *stream-safe-limit*))
             (<= (non-starter-count-after count cps ver)
                 *stream-safe-limit*))
    :rule-classes :linear
    :induct (non-starter-runs-within-p count cps ver)
    :enable (non-starter-runs-within-p
             non-starter-count-after
             nfix
             fix))

  ;; We check, on every code point, for each version,
  ;; that its compatibility decomposition
  ;; has no more than 30 non-starters in a row.

  (local
   (define decomposition-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (non-starter-runs-within-p 0 (decomposition cp t ver) ver)))

  (local
   (std::deflist decomposition-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (decomposition-ok x ver)))

  (defrulel decomposition-ok-listp-of-all-code-points
    (decomposition-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable decomposition-ok-listp-of-cons)

  (defrule non-starter-runs-within-p-of-compatibility-decomposition
    (non-starter-runs-within-p 0 (decomposition cp t ver) ver)
    :enable decomposition-ok
    :use (:instance decomposition-ok-when-member-equal-of-decomposition-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver))))

  ;; The combining grapheme joiner.

  (defrulel starter-p-of-combining-grapheme-joiner
    (starter-p *combining-grapheme-joiner* ver)
    :enable (starter-p
             canonical-combining-class
             canonical-combining-class-map))

  (defrulel decomposition-of-combining-grapheme-joiner
    (equal (decomposition *combining-grapheme-joiner* t ver)
           (list *combining-grapheme-joiner*))
    :enable (decomposition
             compatibility-decompositions))

  ;; The NFKD form of a single code point.

  (defrulel nfkd-of-list
    (equal (nfkd (list cp) ver)
           (canonical-order (decomposition cp t ver) ver))
    :enable (nfkd
             decompose))

  ;; The two theorems about the process, for any count.

  (defrulel non-starter-runs-within-p-of-decompose-of-stream-safe-process-from
    (non-starter-runs-within-p
     count
     (decompose (stream-safe-process-from count cps ver) t ver)
     ver)
    :induct (stream-safe-process-from count cps ver)
    :enable (stream-safe-process-from
             decompose
             non-starter-runs-within-p
             non-starter-runs-within-p-when-within-from-0))

  (defrulel stream-safe-process-from-when-non-starter-runs-within-p
    (implies (and (non-starter-runs-within-p count (decompose cps t ver) ver)
                  (natp count)
                  (<= count *stream-safe-limit*))
             (equal (stream-safe-process-from count cps ver)
                    (code-point-list-fix cps)))
    :induct (stream-safe-process-from count cps ver)
    :enable (stream-safe-process-from
             decompose
             leading-non-starter-count-when-non-starter-runs-within-p
             non-starter-count-after-when-non-starter-runs-within-p
             nfix))

  ;; The theorems about the process.

  (defrule stream-safe-p-of-stream-safe-process
    (stream-safe-p (stream-safe-process cps ver) ver)
    :enable (stream-safe-process
             stream-safe-p-in-terms-of-decompose))

  (defrule stream-safe-process-when-stream-safe-p
    (implies (stream-safe-p cps ver)
             (equal (stream-safe-process cps ver)
                    (code-point-list-fix cps)))
    :enable (stream-safe-process
             stream-safe-p-in-terms-of-decompose))

  (defrule stream-safe-process-of-stream-safe-process
    (equal (stream-safe-process (stream-safe-process cps ver) ver)
           (stream-safe-process cps ver))))
