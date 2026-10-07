; Objectives for rewriting (prove, disprove, or either)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;Recognizes a rewrite-objective: t, nil, or :?
(defund rewrite-objectivep (obj)
  (declare (xargs :guard t))
  (or (eq t obj)   ; trying to prove the thing is true
      (eq nil obj) ; trying to prove the thing is false
      (eq ':? obj)  ; not targeting true or false
      ))

(defthm rewrite-objectivep-forward-to-symbolp
  (implies (rewrite-objectivep obj)
           (symbolp obj))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rewrite-objectivep))))

(defund-inline flip-objective (obj)
  (declare (xargs :guard (rewrite-objectivep obj)))
  (if (eq t obj)
      nil
    (if (eq nil obj)
        t
      ;; must be :?
      obj)))

(defthm rewrite-objectivep-of-flip-objective
  (implies (rewrite-objectivep obj)
           (rewrite-objectivep (flip-objective obj)))
  :hints (("Goal" :in-theory (enable flip-objective))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rewrite-objective-listp (objs)
  (declare (xargs :guard t))
  (if (atom objs)
      (null objs)
    (and (rewrite-objectivep (first objs))
         (rewrite-objective-listp (rest objs)))))

(defthm rewrite-objective-listp-forward-to-symbol-listp
  (implies (rewrite-objective-listp objs)
           (symbol-listp objs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rewrite-objective-listp symbol-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Nil is the strongest thing we can say (it implies anything):
(defmacro rewrite-objective-strengthen () nil)

;; T is the weakest thing we can say (it tells us nothing):
(defmacro rewrite-objective-weaken () t)

(defmacro rewrite-objective-? () :?)

;; Sanity check:
(thm
 (and (rewrite-objectivep (rewrite-objective-strengthen))
      (rewrite-objectivep (rewrite-objective-weaken))
      (rewrite-objectivep (rewrite-objective-?))))
