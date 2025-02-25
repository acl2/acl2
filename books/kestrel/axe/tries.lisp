; A datatype for counting rewrite attempts (aka, "tries").
;
; Copyright (C) 2019-2025 Kestrel Institute
; Copyright (C) 2019-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A datatype for counting how much work the Rewriter has done (how many times
;; rewrite rules have been tried).  Either nil (meaning we are not counting
;; tries), or a natural number.  Note that the count is for all rules together
;; (todo: consider more fine-grained counting).  We keep triesp disabled to
;; avoid case splits in proofs.

(defund triesp (x)
  (declare (xargs :guard t))
  (or (natp x)
      (null x)))

(thm (triesp nil)) ;; ensures that nil satisfies TRIESP, so we can do things like (or tries ...)

(defthm triesp-forward
  (implies (triesp x)
           (or (natp x)
               (null x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable triesp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro zero-tries () 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline increment-tries (tries)
  (declare (xargs :guard (triesp tries)))
  (if tries (+ 1 tries) tries))

(defthm triesp-of-increment-tries
  (implies (triesp x)
           (triesp (increment-tries x)))
  :hints (("Goal" :in-theory (enable triesp increment-tries))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: consider dropping this and making a version that we only call if tries is non-nil?
(defund-inline subtract-tries (tries1 tries2)
  (declare (xargs :guard (and (triesp tries1)
                              (triesp tries2))))

  (if (and tries1
           tries2)
      (- tries1 tries2)
    0))

(defthm integerp-of-subtract-tries-type
  (implies (and (triesp tries1)
                (triesp tries2))
           (integerp (subtract-tries tries1 tries2)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable subtract-tries))))

(defthmd integerp-of-subtract-tries
  (implies (and (triesp tries1)
                (triesp tries2))
           (integerp (subtract-tries tries1 tries2)))
  :hints (("Goal" :in-theory (enable subtract-tries))))

(defthmd rationalp-of-subtract-tries
  (implies (and (triesp tries1)
                (triesp tries2))
           (rationalp (subtract-tries tries1 tries2)))
  :hints (("Goal" :in-theory (enable subtract-tries))))
