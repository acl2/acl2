; Yul Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "kestrel/utilities/omaps/core" :dir :system)

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
