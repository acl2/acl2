; Indicating the final value(s) of interest when lifting
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

;; See also nice-output-indicators.lisp

(include-book "kestrel/jvm/types" :dir :system)
(include-book "kestrel/jvm/heap0" :dir :system)
(include-book "kestrel/jvm/arrays0" :dir :system)
(include-book "kestrel/jvm/class-tables" :dir :system)
(local (include-book "tools/flag" :dir :system))

;; TODO: Move to jvm dir.
;; Recognizes an alist from class-names to class-infos.
;; TODO: Rename class-alistp, and move to JVM package
(defund class-table-alistp (class-table-alist)
  (declare (xargs :guard t))
  (if (atom class-table-alist)
      (null class-table-alist)
    (let* ((entry (first class-table-alist)))
      (and (consp entry)
           (let* ((class-name (car entry))
                  (class-info (cdr entry)))
             (and (jvm::class-namep class-name)
                  (jvm::class-infop class-info class-name)
                  (class-table-alistp (rest class-table-alist))))))))

(defthmd alistp-when-class-table-alistp
  (implies (class-table-alistp class-table-alist)
           (alistp class-table-alist))
  :hints (("Goal" :in-theory (enable class-table-alistp))))

(defthm class-table-alistp-forward-to-alistp
  (implies (class-table-alistp class-table-alist)
           (alistp class-table-alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable class-table-alistp))))

(defthmd lookup-equal-when-class-table-alistp-iff
  (implies (class-table-alistp alist)
           (iff (lookup-equal key alist)
                (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable class-table-alistp))))

(defthm class-infop0-of-lookup-equal-when-class-table-alistp
  (implies (class-table-alistp class-table-alist)
           (iff (jvm::class-infop0 (lookup-equal class-name class-table-alist))
                (lookup-equal class-name class-table-alist)))
  :hints (("Goal" :in-theory (enable lookup-equal class-table-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks that PAIR, a class-name + field-id pair is valid wrt the class-table-alist.
(defund field-pair-okayp (pair class-table-alist)
  (declare (xargs :guard (and (jvm::class-name-field-id-pairp pair)
                              (class-table-alistp class-table-alist))
                  :guard-hints (("Goal" :in-theory (enable alistp-when-class-table-alistp)))
                  ))
  (or (equal pair (array-contents-pair))
      (let* ((class-name (car pair))
             (field-id (cdr pair))
             (class-info (lookup-equal class-name class-table-alist)))
        (if (not class-info)
            ;; Could make this just a warning:
            (er hard? 'field-pair-okayp "Missing class-info for ~x0" class-name)
          (let* ((class-fields (jvm::class-decl-non-static-fields class-info))
                 (class-field-ids (strip-cars class-fields)))
            (member-equal field-id class-field-ids))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This indicates what output to extract from the state when lifting.
;; :return-value means the value on top of the stack.
;; (:array-local <local-num>) means the final contents of the array that was initially referenced by local <local-num>.
;TODO: allow any chain of :field and :array-contents and bv-array-read bottoming out in :return-value or (:param n)...
;TODO: Allow static fields?
;TODO: Should bottom out in a scalar or array, not an object...
(mutual-recursion
 ;; todo: rename to output-indicatorp?
 (defund simple-output-indicatorp (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)
                   :ruler-extenders :all ;TODO: Why was this needed?
                   ))
   (or (eq :all x) ;; return the whole final JVM state
       (eq :return-value x)
       (eq :return-value-long x) ;todo: drop?  tool knows the type of the RV?
       (eq :array-return-value x) ;todo: drop?  tool knows the type of the RV?
;      (eq :return-value-byte x) ;trim down to 1 byte (TODO: Should be able to tell this from the return type!) ;TODO: Think through if this is negative
       (and (true-listp x)
            (eql 1 (len (fargs x)))
            (eq :array-local (ffn-symb x)) ;(:array-local <local-num>) ;;TODO: rename to array-param
            (natp (farg1 x)))
       ;; TODO: improve all this to allow chains of field and contents calls
       (and (true-listp x) ; (:field <class-name-field-id-pair> <indicator-for-object>)
            (eql 2 (len (fargs x)))
            (eq :field (ffn-symb x))
            (jvm::class-name-field-id-pairp (farg1 x))
            (simple-output-indicatorp (farg2 x)))
       (and (true-listp x) ; (:param-field <pair> <local-num>)
            (eql 2 (len (fargs x)))
            (eq :param-field (ffn-symb x))
            (jvm::class-name-field-id-pairp (farg1 x))
            (natp (farg2 x)))
       (and (true-listp x) ; (:tuple <indicator1> ... <indicatorn>)
            (<= 1 (len (fargs x))) ;disallow the empty tuple
            (eq :tuple (ffn-symb x))
            (simple-output-indicatorp-lst (fargs x)))))
 (defund simple-output-indicatorp-lst (x)
   (declare (xargs :measure (acl2-count x)))
   (if (atom x)
       (null x)
     (and (simple-output-indicatorp (first x))
          (simple-output-indicatorp-lst (rest x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 ;; TODO: The lambdas here may be not be necessary, since we always create a DAG to contain the result of this.
 ;; TODO: Reorder args?
 (defund wrap-term-with-output-extractor (output-indicator ; :rv is handled in a wrapper
                                          initial-locals-term
                                          state-term
                                          class-table-alist)
   (declare (xargs :guard (and (simple-output-indicatorp output-indicator)
                               (class-table-alistp class-table-alist))
                   :guard-hints (("Goal" :in-theory (enable simple-output-indicatorp
                                                            simple-output-indicatorp-lst)))))
   (if (eq :all output-indicator)
       state-term
     (if (eq :return-value output-indicator)
         `(jvm::top-operand (jvm::stack (jvm::thread-top-frame (th) ,state-term)))
       (if (eq :return-value-long output-indicator)
           ;; Recall that a long takes 2 stack slots and is stored entirely in the lower slot
           `(jvm::top-long (jvm::stack (jvm::thread-top-frame (th) ,state-term)))
         (if (eq :array-return-value output-indicator) ;TODO: add support for this wherever output-indicators are used
             `((lambda (XXX) ; since XXX appears twice
                 (get-field (jvm::top-operand (jvm::stack (jvm::thread-top-frame (th) xxx)))
                            ',(array-contents-pair)
                            (jvm::heap xxx)))
               ,state-term)
           (if (eq (car output-indicator) :array-local) ;;this means "get the final value of the array that was initially pointed to by array local N.  TODO: This could be an abbreviation for a :field of a :local...
               (let ((local-num (cadr output-indicator)))
                 `(get-field (jvm::nth-local ',local-num ,initial-locals-term) ;;note: these are the locals in the original state
                             ',(array-contents-pair)
                             (jvm::heap ,state-term)))
             (if (eq (car output-indicator) :field)
                 (b* ((pair (farg1 output-indicator))
                      ((when (not (field-pair-okayp pair class-table-alist)))
                       (er hard? 'wrap-term-with-output-extractor "Bad field: ~x0." pair))
                      (obj-indicator (farg2 output-indicator))
                      (obj (wrap-term-with-output-extractor obj-indicator ;return-type
                                                            initial-locals-term state-term class-table-alist)))
                   `(get-field ,obj ',pair (jvm::heap ,state-term)))
               (if (eq (car output-indicator) :param-field) ;todo, redo so that :param is an output-indicator but can't appear naked.  also contents..
                   (let ((pair (farg1 output-indicator))
                         (local-num (farg2 output-indicator)))
                     (if (not (field-pair-okayp pair class-table-alist))
                         (er hard? 'wrap-term-with-output-extractor "Bad field: ~x0." pair)
                       `(get-field (jvm::nth-local ',local-num ,initial-locals-term) ;;NOTE: The local is in the initial state (s0), not the final state!
                                   ',pair
                                   (jvm::heap ,state-term))))
                 (if (eq (car output-indicator) :tuple)
                     ;; TODO: Introduce a lambda?
                     (wrap-term-with-output-extractors (fargs output-indicator) ;return-type
                                                       initial-locals-term state-term class-table-alist)
                   (er hard 'wrap-term-with-output-extractor "Unsupported case: ~x0" output-indicator))))))))))

 (defund wrap-term-with-output-extractors (output-indicators initial-locals-term state-term class-table-alist)
   (declare (xargs :guard (and (simple-output-indicatorp-lst output-indicators)
                               (class-table-alistp class-table-alist))))
   (if (endp output-indicators)
       *nil*
     ;; not a lambda (hope that is okay):
     `(cons ,(wrap-term-with-output-extractor (first output-indicators) ;return-type
                                              initial-locals-term state-term class-table-alist)
            ,(wrap-term-with-output-extractors (rest output-indicators) ;return-type
                                               initial-locals-term state-term class-table-alist)))))

(local (make-flag wrap-term-with-output-extractor))

(defthm-flag-wrap-term-with-output-extractor
  (defthm pseudo-termp-of-wrap-term-with-output-extractor
    (implies (and (simple-output-indicatorp output-indicator)
                  (class-table-alistp class-table-alist)
                  (pseudo-termp initial-locals-term)
                  (pseudo-termp state-term))
             (pseudo-termp (wrap-term-with-output-extractor output-indicator initial-locals-term state-term class-table-alist)))
    :flag wrap-term-with-output-extractor)
  (defthm pseudo-termp-of-wrap-term-with-output-extractors
    (implies (and (simple-output-indicatorp-lst output-indicators)
                  (class-table-alistp class-table-alist)
                  (pseudo-termp initial-locals-term)
                  (pseudo-termp state-term))
             (pseudo-termp (wrap-term-with-output-extractors output-indicators initial-locals-term state-term class-table-alist)))
    :flag wrap-term-with-output-extractors)
  :hints (("Goal" :in-theory (enable wrap-term-with-output-extractor
                                     wrap-term-with-output-extractors
                                     simple-output-indicatorp
                                     simple-output-indicatorp-lst
                                     len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: rename to maybe-output-indicatorp?
(defun output-indicatorp (x)
  (declare (xargs :guard t))
  (or (eq :rv x)
      (simple-output-indicatorp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For use when the output-indicator is :rv; do something sensible using the
;; return-type, if we can.  Returns an simple-output-indicatorp, or nil to
;; indicate failure.
(defund output-indicator-for-return-type (return-type)
  (declare (xargs :guard (or (eq :void return-type)
                             (jvm::typep return-type))))
  (if (eq :void return-type)
      ;; If it is void, throw an error for now (TODO: maybe take the last param that can return a value?  what if it's a field?)
      (er hard? 'output-indicator-for-return-type "No output-indicator given and method is void.")
    ;; If it's not void, we'll use the return type as the output:
    (if (member-eq return-type jvm::*primitive-types*)
        (if (member-eq return-type jvm::*two-slot-types*)
            :return-value-long
          :return-value)
      ;;not a primitive type.  for now, the only reference we handle is a 1-D array
      ;; TODO: Add support for 2-D arrays.
      ;; for any other kind of object, it's not clear what field to return (we probably don't want just the address)
      (if (jvm::is-one-dim-array-typep return-type)
          :array-return-value
        (er hard? 'output-indicator-for-return-type "Can't figure out which output to return: method returns a reference that is not a 1-D array.")))))

(defthm simple-output-indicatorp-of-output-indicator-for-return-type
  (implies (output-indicator-for-return-type return-type)
           (simple-output-indicatorp (output-indicator-for-return-type return-type)))
  :hints (("Goal" :in-theory (enable output-indicator-for-return-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handles an output-indicator that is :rv  May throw an error (and logically return nil).
(defund desugar-output-indicator (output-indicator return-type)
  (declare (xargs :guard (and (output-indicatorp output-indicator)
                              (or (eq :void return-type)
                                  (jvm::typep return-type)))))
  (if (eq :rv output-indicator)
      (output-indicator-for-return-type return-type)
    output-indicator))

(defthm simple-output-indicatorp-of-desugar-output-indicator
  (implies (and (desugar-output-indicator output-indicator return-type) ; no error
                (output-indicatorp output-indicator)
                (or (eq :void return-type)
                    (jvm::typep return-type)))
           (simple-output-indicatorp (desugar-output-indicator output-indicator return-type)))
  :hints (("Goal" :in-theory (enable desugar-output-indicator))))

;; Returns a term to wrap around a dag to extract the output.  In the result,
;; the special symbol 'replace-me should be replaced with the DAG.
(defund output-extraction-term (output-indicator
                                initial-locals-term
                                return-type ; used when output-indicator is :rv
                                class-table-alist)
  (declare (xargs :guard (and (output-indicatorp output-indicator)
                              (pseudo-termp initial-locals-term)
                              (or (eq :void return-type)
                                  (jvm::typep return-type))
                              (class-table-alistp class-table-alist))
                  :guard-hints (("Goal" :in-theory (enable output-indicator-for-return-type))))) ; todo
  (let ((simple-output-indicator (desugar-output-indicator output-indicator return-type)))
    (if (not simple-output-indicator)
        (er hard? 'output-extraction-term "Failed to resove output indicator.")
      (wrap-term-with-output-extractor simple-output-indicator initial-locals-term 'replace-me class-table-alist))))
