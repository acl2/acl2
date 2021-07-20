; More utilities supporting the lifter(s)
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

;; This book will contain lifter utilities that are only used by the compositional lifters.

(include-book "lifter-utilities")

(defconst *invoke-opcodes*
  '(:invokevirtual
    :invokestatic
    :invokespecial
    :invokeinterface))

;; todo: consider memberp here (and then replace member-equal-of-nil above).
(defun make-step-opener-for-non-already-lifted-methods (all-lifted-methods)
  (declare (xargs :guard (all-method-designator-stringp all-lifted-methods)))
  ;; we'll avoid exporting this since many versions of this will be generated
  `(defthmd step-opener-for-non-already-lifted-methods
     (implies (and (member-equal (jvm::op-code (jvm::current-inst th s)) *invoke-opcodes*)
                   (not (member-equal (string-append (farg1 (jvm::current-inst th s)) ;the class name
                                                     (string-append "."
                                                                    (string-append (farg2 (jvm::current-inst th s)) ;the method name
                                                                                   (farg3 (jvm::current-inst th s))))) ;the method descriptor
                                      ',all-lifted-methods)))
              (equal (jvm::step th s)
                     (let ((inst (jvm::current-inst th s)))
                       (jvm::do-inst (jvm::op-code inst)
                                     inst th s))))
     :hints (("Goal" :in-theory (enable jvm::step)))))

;; Rules for handling subroutine calls when doing compositional lifting
;;todo: use these in unroll-java-code2
(defun compositional-lifter-rules ()
  '(step-opener-for-non-already-lifted-methods ;note that this one is defined on the fly
    member-equal-of-nil
    jvm::step-always-open ; jvm::step is replaced by JVM::STEP-ALWAYS-OPEN when we decide to open it
    step-opener-for-non-invokes ;open step, but only for non-invoke instructions
    natp-of-call-stack-size))

;; We open STEP for everything except invoke instructions, which are handled
;; specially depending on whether the method being invoked has already been
;; lifted.
;; todo: just go to step-always-open?
(defthm step-opener-for-non-invokes
  (implies (not (member-equal (jvm::op-code (jvm::current-inst th s)) *invoke-opcodes*))
           (equal (jvm::step th s)
                  (let ((inst (jvm::current-inst th s)))
                    (jvm::do-inst (jvm::op-code inst)
                                  inst th s))))
  :hints (("Goal" :in-theory (enable jvm::step))))


;; Desugar things like (param "foo") to an appropriate term about the stack items of STATE-VAR.
(mutual-recursion
 (defun desugar-params-in-assumption-term-to-stack-items (term ;state-var
                                                          param-name-to-slot-alist param-slot-to-stack-item-alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-alistp param-name-to-slot-alist)
                               (alistp param-slot-to-stack-item-alist))))
   (if (atom term)
       term
     (if (quotep term)
         term
       (let ((new-args (desugar-params-in-assumption-terms-to-stack-items (fargs term) ;state-var
                                                                          param-name-to-slot-alist param-slot-to-stack-item-alist))
             (fn (ffn-symb term)))
         (if (consp fn)
             ;;lambda:
             (let ((formals (farg1 (ffn-symb term)))
                   (body (farg2 (ffn-symb term))))
               `((lambda ,formals ,(desugar-params-in-assumption-term-to-stack-items body ;state-var
                                                                                     param-name-to-slot-alist param-slot-to-stack-item-alist)) ,@new-args))
           (if (eq 'param fn)
               (if (and (eql 1 (len (fargs term)))
                        (myquotep (farg1 term))
                        (stringp (unquote (farg1 term)))
                        (standard-char-listp (coerce (unquote (farg1 term)) 'list)) ;gross: justifies calling string-upcase
                        )
                   ;; Special treatment for a call of PARAM:
                   (b* ((string (unquote (first new-args)))
                        (param-name (pack$ (string-upcase string)))
                        (match (assoc-equal param-name param-name-to-slot-alist))
                        ((when (not match))
                         (er hard? 'desugar-params-in-assumption-term-to-stack-items "No match in local variable table for ~x0.~%" string))
                        (slot (cdr match))
                        (match (assoc-equal slot param-slot-to-stack-item-alist))
                        ((when (not match))
                         (er hard? 'desugar-params-in-assumption-term-to-stack-items "No match in param-slot-to-stack-item-alist for ~x0.~%" slot))
                        (stack-item (cdr match)))
                     stack-item)
                 (er hard? 'desugar-params-in-assumption-term-to-stack-items "Ill-formed call of param: ~x0." term))
             ;; (if (eq 'field fn)
             ;;     ;; If it's a call of FIELD, we put in the heap assumption and make
             ;;     ;; it into a call of GET-FIELD. TODO: Consider adding support
             ;;     ;; for just a field name, instead of a pair, when that is
             ;;     ;; unambiguous (but how will we know the class?)?
             ;;     `(get-field ,(nth 0 new-args) ,(nth 1 new-args) (jvm::heap ,))
             ;;   (if (eq 'static-field fn)
             ;;       ;; If it's a call of STATIC-FIELD, we put in the
             ;;       ;; static-field-map assumption and make it into a call of
             ;;       ;; JVM::GET-STATIC-FIELD.
             ;;       `(jvm::get-static-field ,(nth 0 new-args) ,(nth 1 new-args) (jvm::static-field-map ,))
             ;;     ;; normal case:
             (cons fn new-args)))))))
 (defun desugar-params-in-assumption-terms-to-stack-items (terms ;state-var
                                                           param-name-to-slot-alist param-slot-to-stack-item-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp param-name-to-slot-alist)
                               (alistp param-slot-to-stack-item-alist))))
   (if (endp terms)
       nil
     (cons (desugar-params-in-assumption-term-to-stack-items (first terms) ;state-var
                                                             param-name-to-slot-alist param-slot-to-stack-item-alist)
           (desugar-params-in-assumption-terms-to-stack-items (rest terms) ;state-var
                                                              param-name-to-slot-alist param-slot-to-stack-item-alist)))))

;these are little alists
(defun get-all-lifted-methods-from-table (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((table-alist (table-alist 'compositional-lifter-table wrld)))
    (if (not (symbol-alistp table-alist)) ;for guards
        (er hard? 'get-all-lifted-methods-from-table "Ill-formed compositional lifter table")
      (let ((all-lifted-methods (lookup-eq :all-lifted-methods table-alist)))
        (if (not (all-alistp all-lifted-methods))
            (er hard? 'get-all-lifted-methods-from-table "Ill-formed items in compositional lifter table")
          all-lifted-methods)))))

(defthm all-alistp-of-get-all-lifted-methods-from-table
  (all-alistp (get-all-lifted-methods-from-table wrld)))
