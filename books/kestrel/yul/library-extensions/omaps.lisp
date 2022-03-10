; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set-in-keys-to-in
  (iff (set::in key (keys map))
       (in key map))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-of-restrict-1
  (implies (set::in key keys)
           (equal (in key (restrict keys map))
                  (in key map)))
  :enable restrict)

(defruled in-of-restrict-2
  (equal (in key (restrict keys map))
         (and (set::in key keys)
              (in key map)))
  :enable restrict)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-keys-when-in
  (implies (equal (in a m)
                  (cons a b))
           (set::in a (keys m)))
  :enable keys)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-values-when-in
  (implies (equal (in a m)
                  (cons a b))
           (set::in b (values m)))
  :enable values)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun omap-induction (map)
  (cond ((empty map) nil)
        (t (omap-induction (tail map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun omap-induction2 (map1 map2)
  (cond ((empty map1) nil)
        ((empty map2) nil)
        (t (omap-induction2 (tail map1) (tail map2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule value-of-update-when-not-in
  (implies (not (consp (in key map)))
           (equal (values (update key val map))
                  (set::insert val (values map))))
  :induct (omap-induction map)
  :enable values
  :expand (values (update key val map)))
