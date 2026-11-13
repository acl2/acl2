; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/zip-step-defs")
(include-book "../set-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "../internal/tree"))
(local (include-book "../set"))

(local (include-book "internal/zipper"))
(local (include-book "internal/zip-step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cursor
  :parents (tset)
  :short "A @(see tset) with a marked position."
  :long
  (xdoc::topstring
   (xdoc::p
     "A cursor is a set together with a position in it. A position is either
      an entry or a hole. The entries are the elements of the set. The holes
      are the gaps around them: one before the least element, one between each
      two adjacent elements, and one after the greatest element. So a set of
      @($n$) elements has @($n$) entries and @($n+1$) holes, and the empty set
      has a single hole.")
   (xdoc::p
     "A cursor is modelled by four values: whether it is at an entry (@(tsee
      entryp)), the set of elements @(tsee before) it, the @(tsee entry) it is
      at (if any), and the set of elements @(tsee after) it. These uniquely
      identify the cursor (see @(tsee cursor-extensionality)), and the cursor
      operations are specified by their effect on them.")
   (xdoc::p
     "The typical use of a cursor is to traverse a set in order. A traversal
      starts from @(tsee seek-min), reads each @(tsee entry), moves with @(tsee
      next), and stops when the cursor is no longer at an entry. Its measure is
      @(tsee nexts). For example, the following collects the elements of a set
      into a list, when called on @('(seek-min set)').")
   (xdoc::codeblock
     "(define walk ((cursor cursorp))"
     "  :guard (or (entryp cursor)"
     "             (endp cursor))"
     "  (if (not (entryp cursor))"
     "      nil"
     "    (cons (entry cursor)"
     "          (walk (next cursor))))"
     "  :measure (nexts cursor))")
   (xdoc::p
     "The guard says that the traversal is at an entry or has reached the hole
      after every element. This holds of @(tsee seek-min) and is preserved by
      @(tsee next). It does not hold of @(tsee begin), which is a hole.")
   (xdoc::p
     "To traverse in the reverse order, use @(tsee seek-max), @(tsee prev), and
      @(tsee prevs), with @(tsee beginp) in the guard.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursorp (x)
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Recognizer for @(see cursor)s."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(n)$).")
  (and (zipp x)
       (setp (zip-plug x))))

;;;;;;;;;;;;;;;;;;;;

(defruled cursorp-compound-recognizer
  (implies (cursorp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable cursorp)

(add-to-ruleset break-abstraction '(cursorp-compound-recognizer))

(defruled zipp-when-cursorp-forward-chaining
  (implies (cursorp cursor)
           (zipp cursor))
  :rule-classes :forward-chaining
  :enable cursorp)

(add-to-ruleset break-abstraction '(zipp-when-cursorp-forward-chaining))

(defruled setp-of-zip-plug-when-cursorp-forward-chaining
  (implies (cursorp cursor)
           (setp (zip-plug cursor)))
  :rule-classes :forward-chaining
  :enable cursorp)

(add-to-ruleset break-abstraction
                '(setp-of-zip-plug-when-cursorp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define begin ((set setp))
  :type-prescription :none
  :returns (cursor cursorp
                   :hints (("Goal" :in-theory (enable* cursorp
                                                       break-abstraction))))
  :parents (cursor)
  :short "Construct a @(see cursor) at the hole before every element of a
          @(see tset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a hole, not the least entry. A traversal starts from @(tsee
      seek-min).")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the first hole."))
  (zip-begin (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define end ((set setp))
  :type-prescription :none
  :returns (cursor cursorp
                   :hints (("Goal" :in-theory (enable* cursorp
                                                       break-abstraction))))
  :parents (cursor)
  :short "Construct a @(see cursor) at the hole after every element of a
          @(see tset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a hole, not the greatest entry. A reverse traversal starts from
      @(tsee seek-max).")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the last hole."))
  (zip-end (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule begin-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (begin set0)
                  (begin set1)))
  :rule-classes :congruence
  :enable begin)

(defrule end-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (end set0)
                  (end set1)))
  :rule-classes :congruence
  :enable end)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursor-fix ((cursor cursorp))
  :type-prescription :none
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Fixer for @(see cursor)s."
  (mbe :logic (if (cursorp cursor)
                  cursor
                (begin (empty)))
       :exec cursor)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule cursor-fix-when-cursorp
  (implies (cursorp cursor)
           (equal (cursor-fix cursor)
                  cursor))
  :enable cursor-fix)

(defruled cursor-fix-when-not-cursorp
  (implies (not (cursorp cursor))
           (equal (cursor-fix cursor)
                  (begin (empty))))
  :enable cursor-fix)

(defrule cursor-fix-when-not-cursorp-cheap
  (implies (not (cursorp cursor))
           (equal (cursor-fix cursor)
                  (begin (empty))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by cursor-fix-when-not-cursorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursor-equiv
  ((x cursorp)
   (y cursorp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Equivalence up to @(tsee cursor-fix)."
  (equal (cursor-fix x)
         (cursor-fix y))
  :inline t

  ///
  (defequiv cursor-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule cursor-fix-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (cursor-fix cursor0)
                  (cursor-fix cursor1)))
  :rule-classes :congruence
  :enable cursor-equiv)

(defrule cursor-fix-under-cursor-equiv
  (cursor-equiv (cursor-fix cursor)
                cursor)
  :enable cursor-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled zipp-of-cursor-fix
  (zipp (cursor-fix cursor))
  :enable cursorp
  :use cursorp-of-cursor-fix
  :disable cursorp-of-cursor-fix)

(add-to-ruleset break-abstraction '(zipp-of-cursor-fix))

(defruled zip-fix-of-cursor-fix
  (equal (zip-fix (cursor-fix cursor))
         (cursor-fix cursor))
  :enable zipp-of-cursor-fix)

(add-to-ruleset break-abstraction '(zip-fix-of-cursor-fix))

(defruled setp-of-zip-plug-of-cursor-fix
  (setp (zip-plug (cursor-fix cursor)))
  :use (:instance setp-of-zip-plug-when-cursorp-forward-chaining
                  (cursor (cursor-fix cursor))))

(add-to-ruleset break-abstraction '(setp-of-zip-plug-of-cursor-fix))

(defruled bstp-of-zip-plug-of-cursor-fix
  (bstp (zip-plug (cursor-fix cursor)))
  :use setp-of-zip-plug-of-cursor-fix
  :enable bstp-when-setp-forward-chaining)

(add-to-ruleset break-abstraction '(bstp-of-zip-plug-of-cursor-fix))

(defruled cursor-fix-of-zip-begin-of-fix
  (equal (cursor-fix (zip-begin (fix set)))
         (zip-begin (fix set)))
  :use cursorp-of-begin
  :enable begin)

(add-to-ruleset break-abstraction '(cursor-fix-of-zip-begin-of-fix))

(defruled cursor-fix-of-zip-end-of-fix
  (equal (cursor-fix (zip-end (fix set)))
         (zip-end (fix set)))
  :use cursorp-of-end
  :enable end)

(add-to-ruleset break-abstraction '(cursor-fix-of-zip-end-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy cursor-extra-rules
  '(cursor-fix-when-not-cursorp))
