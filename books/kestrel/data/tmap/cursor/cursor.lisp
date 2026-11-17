; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/zip-step-defs")
(include-book "../map-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../internal/tree"))
(local (include-book "../map"))

(local (include-book "internal/zipper"))
(local (include-book "internal/zip-step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cursor
  :parents (tmap)
  :short "A @(see tmap) with a marked position."
  :long
  (xdoc::topstring
   (xdoc::p
     "A cursor is a map together with a position in it. A position is either
      an entry or a hole. The entries are the key-value pairs of the map, in
      the order of their keys. The holes are the gaps around them: one before
      the least key, one between each two adjacent keys, and one after the
      greatest key. So a map of @($n$) keys has @($n$) entries and @($n+1$)
      holes, and the empty map has a single hole.")
   (xdoc::p
     "A cursor is modelled by five values: whether it is at an entry (@(tsee
      entryp)), the map of entries @(tsee before) it, the key and the value of
      the entry it is at, if any (@(tsee entry-key) and @(tsee entry-val)), and
      the map of entries @(tsee after) it. These uniquely identify the cursor
      (see @(tsee cursor-extensionality)), and the cursor operations are
      specified by their effect on them.")
   (xdoc::p
     "The typical use of a cursor is to traverse a map in the order of its
      keys. A traversal starts from @(tsee seek-min), reads each @(tsee
      entry-key) and @(tsee entry-val), moves with @(tsee next), and stops when
      the cursor is no longer at an entry. Its measure is @(tsee nexts). For
      example, the following collects the keys of a map into a list, when
      called on @('(seek-min map)').")
   (xdoc::codeblock
     "(define walk ((cursor cursorp))"
     "  :guard (or (entryp cursor)"
     "             (endp cursor))"
     "  (if (not (entryp cursor))"
     "      nil"
     "    (cons (entry-key cursor)"
     "          (walk (next cursor))))"
     "  :measure (nexts cursor))")
   (xdoc::p
     "The guard says that the traversal is at an entry or has reached the hole
      after every entry. This holds of @(tsee seek-min) and is preserved by
      @(tsee next). It does not hold of @(tsee begin), which is a hole.")
   (xdoc::p
     "To traverse in the reverse order, use @(tsee seek-max), @(tsee prev), and
      @(tsee prevs), with @(tsee beginp) in the guard.")
   (xdoc::p
     "To traverse only the entries at or above a key, start from the @(tsee
      seek) of that key, taking one @(tsee step-forward) if it is at a
      hole.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursorp (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Recognizer for @(see cursor)s."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(n)$).")
  (and (zipp x)
       (mapp (zip-plug x))))

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

(defruled mapp-of-zip-plug-when-cursorp-forward-chaining
  (implies (cursorp cursor)
           (mapp (zip-plug cursor)))
  :rule-classes :forward-chaining
  :enable cursorp)

(add-to-ruleset break-abstraction
                '(mapp-of-zip-plug-when-cursorp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define begin ((map mapp))
  :returns (cursor cursorp
                   :hints (("Goal" :in-theory (enable* cursorp
                                                       break-abstraction))))
  :parents (cursor)
  :short "Construct a @(see cursor) at the hole before every entry of a
          @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a hole, not the least entry. A traversal starts from @(tsee
      seek-min).")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the first hole."))
  (zip-begin (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define end ((map mapp))
  :returns (cursor cursorp
                   :hints (("Goal" :in-theory (enable* cursorp
                                                       break-abstraction))))
  :parents (cursor)
  :short "Construct a @(see cursor) at the hole after every entry of a
          @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a hole, not the greatest entry. A reverse traversal starts from
      @(tsee seek-max).")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the last hole."))
  (zip-end (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule begin-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (begin map0)
                  (begin map1)))
  :rule-classes :congruence
  :enable begin)

(defrule end-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (end map0)
                  (end map1)))
  :rule-classes :congruence
  :enable end)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursor-fix ((cursor cursorp))
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

(defruled mapp-of-zip-plug-of-cursor-fix
  (mapp (zip-plug (cursor-fix cursor)))
  :use (:instance mapp-of-zip-plug-when-cursorp-forward-chaining
                  (cursor (cursor-fix cursor))))

(add-to-ruleset break-abstraction '(mapp-of-zip-plug-of-cursor-fix))

(defruled bstp-of-zip-plug-of-cursor-fix
  (bstp (zip-plug (cursor-fix cursor)))
  :use mapp-of-zip-plug-of-cursor-fix
  :enable bstp-when-mapp-forward-chaining)

(add-to-ruleset break-abstraction '(bstp-of-zip-plug-of-cursor-fix))

(defruled cursor-fix-of-zip-begin-of-fix
  (equal (cursor-fix (zip-begin (fix map)))
         (zip-begin (fix map)))
  :use cursorp-of-begin
  :enable begin)

(add-to-ruleset break-abstraction '(cursor-fix-of-zip-begin-of-fix))

(defruled cursor-fix-of-zip-end-of-fix
  (equal (cursor-fix (zip-end (fix map)))
         (zip-end (fix map)))
  :use cursorp-of-end
  :enable end)

(add-to-ruleset break-abstraction '(cursor-fix-of-zip-end-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy cursor-extra-rules
  '(cursor-fix-when-not-cursorp))
