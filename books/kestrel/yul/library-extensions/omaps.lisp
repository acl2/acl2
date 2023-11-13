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

(defun omap-induction2 (map1 map2)
  (cond ((empty map1) nil)
        ((empty map2) nil)
        (t (omap-induction2 (tail map1) (tail map2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule value-of-update-when-not-in
  (implies (not (consp (in key map)))
           (equal (values (update key val map))
                  (set::insert val (values map))))
  :induct (size map)
  :enable (values size)
  :expand (values (update key val map)))
