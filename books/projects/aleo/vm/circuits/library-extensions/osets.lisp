; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::intersect-of-insert
  (implies (and (setp x)
                (setp y))
           (equal (set::intersect (set::insert a x) y)
                  (if (set::in a y)
                      (set::insert a (set::intersect x y))
                    (set::intersect x y))))
  :enable (set::intersect
           set::insert
           set::head
           set::tail
           set::emptyp
           set::setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::difference-of-same
  (equal (set::difference x x) nil)
  :use (:instance set::double-containment (x (set::difference x x)) (y nil))
  :prep-lemmas
  ((defrule lemma
     (set::subset (set::difference x x) nil)
     :enable set::pick-a-point-subset-strategy)))
