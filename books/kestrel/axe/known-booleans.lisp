; A tool to track functions that are known to return only t or nil
;
; Copyright (C) 2016-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "tools/er-soft-logic" :dir :system)

;; A table for tracking functions that are known to be booleans. This allows
;; for stronger reasoning, e.g., replacing boolean terms with T when they are
;; in a set of assumptions that are known (to be non-nil).  Similar reasoning
;; is used when making Axe rules; if the conclusion is a known boolean, Axe
;; makes a rule that rewrites it to T.

;; Note that the soundness of Axe depends on this table being correct.  So we
;; check that a function does in fact always return a boolean before adding it
;; to the table.

;; TODO: Can we somehow protect the table from a user modifying it?

(defun all-t (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      t
    (and (eq t (first items))
         (all-t (rest items)))))

;; Any key for which there is a binding in the table is taken to be a known
;; boolean.
(defund known-booleans (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let* ((alist (table-alist :known-booleans-table wrld)))
    (if (not (alistp alist))
        (er hard? 'known-booleans "Invalid known-boolean table: ~x0" alist)
      (let ((known-booleans (strip-cars alist))
            (vals (strip-cdrs alist)))
        (if (not (and (symbol-listp known-booleans)
                      (all-t vals)))
            (er hard? 'known-booleans "Invalid known-boolean table: ~x0" alist)
          known-booleans)))))

(defthm true-listp-of-known-booleans
  (true-listp (known-booleans wrld))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable known-booleans))))

(defthm symbol-listp-of-known-booleans
  (symbol-listp (known-booleans wrld))
  :hints (("Goal" :in-theory (enable known-booleans))))

;; TODO: unify
(defmacro make-event-quiet2 (&rest args)
  `(with-output
     :off ,(remove1 'error *valid-output-names*)
     :gag-mode nil
     ;; todo: don't add :on-behalf-of if it already exists
     (make-event ,@args :on-behalf-of :quiet)))

;Returns (mv erp event state) where event is a table event. TODO: Allow hints
;to be passed in (but really the fact should be proved as a type-precription
;rule before calling this).  We need to be careful that the table entries will
;be merged when including books from diverse places.
;; TODO: Disallow adding IMPLIES as a known boolean?
(defun add-known-boolean-fn (fn state)
  (declare (xargs :guard (symbolp fn) ;todo: strengthen
                  :stobjs state))
  (b* ((w (w state))
       ((when (not (function-symbolp fn w)))
        (er-soft-logic 'add-known-boolean "~x0 is not a defined function." fn))
       ((when (not (logicp fn w)))
        (er-soft-logic 'add-known-boolean "~x0 is not in logic mode." fn))
       (old-known-booleans (known-booleans (w state)))
       ((when (member-eq fn old-known-booleans))
        ;; TODO: Maybe return :redundant?
        (prog2$ (cw "~x0 is already a known boolean.~%" fn)
                (mv nil '(value-triple :invisible) state)))
       (formals (fn-formals fn (w state))))
    (mv nil
        `(progn (defthm ,(pack$ fn '$-known-booleans-justification)
                  (booleanp (,fn ,@formals))
                  :rule-classes nil)
                ;; If the theorem fails, the table event will not be processed.
                (table :known-booleans-table
                       ',fn t)
                (value-triple ',fn))
        state)))

(defmacro add-known-boolean (fn)
  `(make-event-quiet2 (add-known-boolean-fn ',fn state)
                     ;;:check-expansion t
               ))

;; We can add built-in ACL2 functions freely to this list:

(add-known-boolean not)
(add-known-boolean equal)
(add-known-boolean =) ; but we should usually replace = with equal
(add-known-boolean unsigned-byte-p)
(add-known-boolean signed-byte-p)
(add-known-boolean natp)
(add-known-boolean integerp)
(add-known-boolean posp)
(add-known-boolean rationalp)
(add-known-boolean complex-rationalp)
(add-known-boolean acl2-numberp)
(add-known-boolean consp)
(add-known-boolean atom) ; but we should usually open to expose consp
(add-known-boolean endp) ; but we should usually open to expose consp
(add-known-boolean booleanp)
(add-known-boolean true-listp)
(add-known-boolean iff)
(add-known-boolean <)
(add-known-boolean alistp)
(add-known-boolean symbol-alistp)
(add-known-boolean logbitp)
(add-known-boolean evenp)
(add-known-boolean oddp)
(add-known-boolean bitp)

;; See tests in known-booleans-tests.lisp
