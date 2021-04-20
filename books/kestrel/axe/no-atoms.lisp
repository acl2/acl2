; Recognize a list with no atoms (e.g., dag args that are all constants)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-dargp-less-than")

;;;
;;; no-atoms
;;;

;; TODO: DEPRECATE THIS IN FAVOR OF ALL-CONSP

(defund no-atoms (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      t
    (if (atom (first items))
        nil
      (no-atoms (rest items)))))

(defthm no-atoms-when-all-myquotep
  (implies (all-myquotep items)
           (no-atoms items))
  :hints (("Goal" :in-theory (enable no-atoms))))

(defthm all-myquotep-when-no-atoms-and-all-dargp-cheap
  (implies (and (no-atoms items)
                (all-dargp items))
           (all-myquotep items))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable no-atoms))))

(defthmd all-dargp-less-than-when-no-atoms
  (implies (no-atoms items)
           (equal (all-dargp-less-than items bound)
                  (all-myquotep items)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than all-dargp no-atoms))))

(defthm all-dargp-less-than-when-no-atoms-cheap
  (implies (no-atoms items)
           (equal (all-dargp-less-than items bound)
                  (all-myquotep items)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than all-dargp no-atoms))))
