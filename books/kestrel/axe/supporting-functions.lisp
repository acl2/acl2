; Getting the functions that support the definitions of other functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that this book "knows" about the function dag-val-with-axe-evaluator.

(include-book "safe-unquote")
(include-book "kestrel/world-light/fn-definedp" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/world-light/function-symbolsp" :dir :system)
(local (include-book "tools/flag" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(mutual-recursion
 ;; This is dag-aware
 (defund get-called-fns-aux (term acc)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-listp acc))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       acc
     (let* ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           acc
         (if (consp fn) ;tests for lambda
             (get-called-fns-aux (third fn) (get-called-fns-aux-lst (fargs term) acc))
           (if (and (eq 'dag-val-with-axe-evaluator fn)
                    (quotep (third (fargs term))) ;think about this
                    (symbol-alistp (unquote (third (fargs term)))))
               ;check for consistent definitions!  ffixme
               (union-equal (strip-cars (safe-unquote (third (fargs term)))) acc)
             (get-called-fns-aux-lst (fargs term) (add-to-set-eq fn acc))))))))

 ;; This is dag-aware
 (defund get-called-fns-aux-lst (terms acc)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-listp acc))))
   (if (endp terms)
       acc
     (get-called-fns-aux (car terms) (get-called-fns-aux-lst (cdr terms) acc)))))

(local (make-flag get-called-fns-aux))

;todo: see GET-FNS-IN-TERM and all-fnnames
(local
  (defthm-flag-get-called-fns-aux
    (defthm symbol-listp-of-get-called-fns-aux
      (implies (and (pseudo-termp term)
                    (symbol-listp acc))
               (symbol-listp (get-called-fns-aux term acc)))
      :flag get-called-fns-aux)
    (defthm symbol-listp-of-get-called-fns-aux-lst
      (implies (and (pseudo-term-listp terms)
                    (symbol-listp acc))
               (symbol-listp (get-called-fns-aux-lst terms acc)))
      :flag get-called-fns-aux-lst)
    :hints (("Goal" :in-theory (enable get-called-fns-aux
                                       get-called-fns-aux-lst)))))

(verify-guards get-called-fns-aux :hints (("Goal" :expand ((pseudo-termp term)))))

(defund get-called-fns (term)
  (declare (xargs :guard (pseudo-termp term)))
  (get-called-fns-aux term nil))

(defthm symbol-listp-of-get-called-fns
  (implies (pseudo-termp term)
           (symbol-listp (get-called-fns term)))
  :hints (("Goal" :in-theory (enable get-called-fns))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;ffixme what about primitives and recursion and mutual recursion and constrained functions?
;TODO Would be nice to track the call chain so we can report it in the error message.
(defund get-immediate-supporting-fns (fn-name throw-errorp wrld)
  (declare (xargs :guard (and (symbolp fn-name)
                              (plist-worldp wrld)
                              (function-symbolp fn-name wrld))))
  (if (member-eq fn-name *acl2-primitives*)
      (er hard? 'get-immediate-supporting-fns "Trying to get the body of the ACL2 primitive ~x0.  Consider adding it to the base evaluator.  Or investigate why a function that calls this function (transitively) is suddenly appearing." fn-name)
    (if (not (fn-definedp fn-name wrld))
        ;; an undefined function has no supporters
        (prog2$ (cw "(Note: Undefined function ~x0 is present in DAG.)~%" fn-name)
                nil)
      (let* ((body (fn-body fn-name throw-errorp wrld))
             (called-fns (get-called-fns body)))
        (if (not (function-symbolsp called-fns wrld))
            (prog2$ (er hard? 'get-immediate-supporting-fns "Unknown function(s) among those returned by get-called-fns: ~x0." called-fns)
                    nil)
          called-fns)))))

(defthm symbol-listp-of-get-immediate-supporting-fns
  (symbol-listp (get-immediate-supporting-fns fn-name throw-errorp wrld))
  :hints (("Goal" :in-theory (enable get-immediate-supporting-fns))))

(defthm function-symbolsp-of-get-immediate-supporting-fns
  (function-symbolsp (get-immediate-supporting-fns fn-name throw-errorp wrld) wrld)
  :hints (("Goal" :in-theory (enable get-immediate-supporting-fns))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this is a worklist algorithm
(defund get-all-supporting-fns-aux (count ;for termination
                                    fns   ;the worklist
                                    done-list
                                    throw-errorp acc wrld)
  (declare (xargs :guard (and (natp count)
                              (symbol-listp fns)
                              (symbol-listp done-list)
                              (plist-worldp wrld)
                              (function-symbolsp fns wrld)
                              (symbol-listp acc))))
  (if (zp count)
      (er hard? 'get-all-supporting-fns-aux "limit reached.")
    (if (endp fns)
        acc
      (let* ((fn (first fns)))
        (if (or (member-eq fn done-list)
                (eq fn 'bad-atom<=) ;new: Perhaps this can never actually be executed (we could still add it to the evaluator...)
                )
            (get-all-supporting-fns-aux (+ -1 count) (rest fns) done-list throw-errorp acc wrld)
          (get-all-supporting-fns-aux (+ -1 count)
                                      (append (get-immediate-supporting-fns fn throw-errorp wrld) (rest fns))
                                      (cons fn done-list)
                                      throw-errorp
                                      (add-to-set-eq fn acc)
                                      wrld))))))

(defthm symbol-listp-of-get-all-supporting-fns-aux
  (implies (and (symbol-listp acc)
                (symbol-listp fn-names))
           (symbol-listp (get-all-supporting-fns-aux count fn-names fn-names-to-stop-at throw-errorp acc wrld)))
  :hints (("Goal" :in-theory (enable get-all-supporting-fns-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;this includes the function itself
;; (defun get-all-supporting-fns (fn-name wrld)
;;   (get-all-supporting-fns-aux (list fn-name) nil nil wrld))

;; (defun get-non-built-in-supporting-fns (fn-name wrld)
;;   (set-difference-eq (get-all-supporting-fns fn-name wrld) *acl2-primitives*))

;; (defun get-all-supporting-fns-list (fn-names wrld)
;;   (get-all-supporting-fns-aux fn-names nil nil wrld))

;; ;ffixme this will suck in stuff below the bv/array fns - redo the above code to stop when it hits such a fn!
;; (defun get-non-built-in-supporting-fns-list (fn-names wrld)
;;   (set-difference-eq (get-all-supporting-fns-list fn-names wrld) *acl2-primitives*))

;will include fn-names themselves, if they are not built-ins.
;now throws an error if any of the fns are supported by acl2 primitives not in *axe-evaluator-functions*
;ffffixme what about embedded dags?!
;todo: exclude the evaluator functions themselves?
(defund get-non-built-in-supporting-fns-list (fn-names done-list wrld)
  (declare (xargs :guard (and (symbol-listp fn-names)
                              (symbol-listp done-list)
                              (plist-worldp wrld)
                              (function-symbolsp fn-names wrld))))
  (get-all-supporting-fns-aux 1000000000
                              fn-names
                              done-list
                              t                           ;throw-errorp
                              nil ;empty-acc
                              wrld))

(defthmd symbol-listp-of-get-non-built-in-supporting-fns-list
  (implies (symbol-listp fn-names)
           (symbol-listp (get-non-built-in-supporting-fns-list fn-names done-list wrld)))
  :hints (("Goal" :in-theory (enable get-non-built-in-supporting-fns-list))))

;; (defun get-non-built-in-supporting-fns-list-tolerant (fn-names wrld)
;;   (declare (xargs :stobjs state :verify-guards nil))
;;   (get-all-supporting-fns-aux fn-names
;;                               (append *acl2-primitives* *axe-evaluator-functions*) ;stops when it hits one of these..
;;                               nil ;throw-errorp
;;                               nil
;;                               wrld))
