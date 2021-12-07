; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "kestrel/utilities/omaps/core" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled consp-of-omap-in-to-set-in-of-omap-keys
  (iff (consp (in key map))
       (set::in key (keys map)))
  :enable in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-restrict
  (equal (keys (restrict keys map))
         (set::intersect keys (keys map)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy)
  :prep-lemmas
  ((defrule lemma1
     (implies (set::in x (keys (restrict keys map)))
              (set::in x (keys map)))
     :enable restrict)
   (defrule lemma2
     (implies (set::in x (keys (restrict keys map)))
              (set::in x keys))
     :enable restrict)
   (defrule lemma3
     (implies (and (set::in x (keys map))
                   (set::in x keys))
              (set::in x (keys (restrict keys map))))
     :enable restrict)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-mfix
  (equal (keys (mfix map))
         (keys map))
  :enable keys)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-update*
  (equal (keys (update* new old))
         (set::union (keys new) (keys old)))
  :enable update*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule consp-of-in-of-update*
  (equal (consp (in key (update* map1 map2)))
         (or (consp (in key map1))
             (consp (in key map2))))
  :enable (in update*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-update*
  (equal (in key (update* map1 map2))
         (if (consp (in key map1))
             (in key map1)
           (in key map2)))
  :enable (update* in))
