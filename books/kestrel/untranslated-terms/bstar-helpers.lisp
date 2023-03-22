; Helper functions for manipulating calls of b*
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests of b* in /data/ewsmithb/acl2/books/kestrel/tests/bstar-tests.lisp.

(include-book "kestrel/utilities/forms" :dir :system) ; for farg1, etc.
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(local (in-theory (disable mv-nth)))

;; Recognizes a "supported" b* binding, of the form (<binder> ...<expressions>...)
;; where the number of allowed expressions depends on the binder.  Tools should
;; know how to properly handle the supprted bindings.
;; NOTE: Keep this in sync with the functions below
(defund supported-b*-bindingp (binding)
  (declare (xargs :guard t))
  (and (true-listp binding)
       (consp binding)
       (let ((binder (first binding))
             (expressions (rest binding)))
         (if (atom binder)
             ;; A few binders are atoms:
             (or (eq binder '-)        ; (- <term>*), with any number of terms
                 (eq binder '&)        ; (& <term>*), with any number of terms
                 (and (symbolp binder) ; todo: check for legal variable name?
                      (= 1 (len expressions))))
           ;; Most binders are conses:
           (and (true-listp binder)
                (case (car binder)
                  ;; ((when/if/unless <term>) <term>+):
                  ((when if unless) (and (= 1 (len (fargs binder))) ; todo: check these restrictions
                                         (<= 1 (len expressions))))
                  ;; ((mv <var> ... <var>) <term>):
                  ;; TODO: Consider supporting patterns, not just vars, supplied to MV.
                  (mv (and (symbol-listp (fargs binder))
                           (<= 2 (len (fargs binder))) ; must be at least 2 vars
                           (= 1 (len expressions)) ; must be exactly 1 expression
                           ))
                  ;; ((list <var>*) <term>):
                  ;; TODO: Consider supporting patterns, not just vars, supplied to LIST.
                  (list (and (symbol-listp (fargs binder))
                             (= 1 (len expressions)) ; must be exactly 1 expression
                             ))
                  ;; ((er <var>) <term>) or ((er <var> :iferr <term>) <term>):
                  ;; TODO: Are patterns supported?
                  (er (let ((binder-args (fargs binder)))
                        (and (or (and (= 1 (len binder-args))
                                      (symbolp (first binder-args)))
                                 (and (= 3 (len binder-args))
                                      (symbolp (first binder-args))
                                      (eq :iferr (second binder-args))))
                             (= 1 (len expressions)) ; must be exactly 1 expression
                             )))
                  ;; todo: add more kinds of supported binder
                  (otherwise nil)))))))

;; Recognizes a list of supported b* bindings
(defund supported-b*-bindingsp (bindings)
  (declare (xargs :guard t))
  (if (atom bindings)
      (null bindings)
    (and (supported-b*-bindingp (first bindings))
         (supported-b*-bindingsp (rest bindings)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extracts all the terms in the b* binding, in order.  One can process the
;; terms and then call recreate-b*-binding to build a new binding.
(defund extract-terms-from-b*-binding (binding)
  (declare (xargs :guard (supported-b*-bindingp binding)
                  :guard-hints (("Goal" :in-theory (enable supported-b*-bindingp)))))
  (let ((binder (first binding))
        (expressions (rest binding)))
    (if (symbolp binder)
        (if (or (eq binder '-)
                (eq binder '&))
            ;; (- <term>*) or (& <term>*):
            expressions
          ;; (<var> <term>):
          expressions ; must only be one
          )
      (case (car binder)
        ;; ((when/if/unless <term>) <term>+):
        ((when if unless) (cons (farg1 binder) expressions))
        ;; ((mv <var> ... <var>) <term>)
        (mv expressions ; must only be one
            )
        ;; ((list <var>*) <term>):
        (list expressions ; must only be one
              )
        ;; ((er <var>) <term>) or ((er <var> :iferr <term>) <term>):
        (er (if (= 1 (len (fargs binder)))
                expressions ; must only be one
              ;; special case for :iferr:
              (cons (third (fargs binder)) expressions)))
        ;; Should never happen:
        (t (er hard 'extract-terms-from-b*-binding "Unsupported b* binder: ~x0." binding))))))

(defthm true-listp-of-extract-terms-from-b*-binding
  (implies (supported-b*-bindingp binding)
           (true-listp (extract-terms-from-b*-binding binding)))
  :hints (("Goal" :in-theory (enable supported-b*-bindingp extract-terms-from-b*-binding))))

(defthm <=-of-acl2-count-of-extract-terms-from-b*-binding-linear
  (<= (acl2-count (extract-terms-from-b*-binding binding))
      (acl2-count binding))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable extract-terms-from-b*-binding))))

;; Extracts all the terms in the b* bindings, in order.
(defund extract-terms-from-b*-bindings (bindings)
  (declare (xargs :guard (supported-b*-bindingsp bindings)
                  :guard-hints (("Goal" :in-theory (enable supported-b*-bindingsp)))))
  (if (endp bindings)
      nil
    (append (extract-terms-from-b*-binding (first bindings))
            (extract-terms-from-b*-bindings (rest bindings)))))

(defthm <=-of-acl2-count-of-extract-terms-from-b*-bindings-linear
  (<= (acl2-count (extract-terms-from-b*-bindings bindings))
      (acl2-count bindings))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable extract-terms-from-b*-bindings))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recreates the BINDING by replacing the terms it contains with the NEW-TERMS,
;; in order.  Returns (mv new-binding rest-new-terms).
(defund recreate-b*-binding (binding new-terms)
  (declare (xargs :guard (and (supported-b*-bindingp binding)
                              (true-listp new-terms))
                  :guard-hints (("Goal" :in-theory (enable supported-b*-bindingp)))))
  (let* ((binder (first binding))
         (expressions (rest binding)))
    (if (symbolp binder)
        (if (or (eq binder '-)
                (eq binder '&))
            ;; (- <term>*) or (& <term>*):
            (let ((num-exprs (len expressions)))
              (mv `(,binder ,@(take num-exprs new-terms))
                  (nthcdr num-exprs new-terms)))
          ;; (<var> <term>):
          (mv `(,binder ,(first new-terms))
              (rest new-terms)))
      (case (car binder)
        ((when if unless)
         ;; ((when/if/unless <term>) <term>+):
         (let ((num-exprs (len expressions)))
           (mv `((,(car binder) ,(first new-terms)) ,@(take num-exprs (rest new-terms)))
               (nthcdr (+ 1 num-exprs) new-terms))))
        ;; ((mv <var> ... <var>) <term>):
        (mv (mv `((mv ,@(fargs binder)) ,(first new-terms))
                (rest new-terms)))
        ;; ((list <var>*) <term>):
        (list (mv `((list ,@(fargs binder)) ,(first new-terms))
                  (rest new-terms)))
        ;; ((er <var>) <term>) or ((er <var> :iferr <term>) <term>):
        (er (if (= 1 (len (fargs binder)))
                ;; consumes 1 term:
                (mv `((er ,@(fargs binder)) ,(first new-terms))
                    (rest new-terms))
              ;; consumes 2 terms:
              (mv `((er ,(first (fargs binder)) :iferr ,(first new-terms)) ,(first (rest new-terms)))
                  (rest (rest new-terms)))))
        ;; Should never happen:
        (otherwise (progn$ (er hard 'recreate-b*-binding "Unsupported b* binder: ~x0." binding)
                           (mv nil nil)))))))

(local
 (defthm true-listp-of-mv-nth-1-of-recreate-b*-binding
   (implies (true-listp new-terms)
            (true-listp (mv-nth 1 (recreate-b*-binding binding new-terms))))
   :hints (("Goal" :in-theory (enable recreate-b*-binding)))))

;; Recreates the BINDINGS by replacing the terms they contain with the
;; NEW-TERMS, in order.
(defund recreate-b*-bindings (bindings new-terms)
  (declare (xargs :guard (and (supported-b*-bindingsp bindings)
                              (true-listp new-terms))
                  :guard-hints (("Goal" :in-theory (enable supported-b*-bindingsp)))))
  (if (endp bindings)
      (if (not (endp new-terms))
          (er hard? 'recreate-b*-bindings "Extra new terms: ~x0." new-terms)
        nil)
    (mv-let (new-binding new-terms)
      (recreate-b*-binding (first bindings) new-terms)
      (let ((new-bindings (recreate-b*-bindings (rest bindings) new-terms)))
        (cons new-binding new-bindings)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm supported-b*-bindingp-of-mv-nth-0-of-recreate-b*-binding
  (implies (supported-b*-bindingp binding)
           (supported-b*-bindingp (mv-nth 0 (recreate-b*-binding binding new-terms))))
  :hints (("Goal" :in-theory (enable supported-b*-bindingp
                                     recreate-b*-binding))))

(defthm supported-b*-bindingsp-of-recreate-b*-bindings
  (implies (supported-b*-bindingsp bindings)
           (supported-b*-bindingsp (recreate-b*-bindings bindings new-terms)))
  :hints (("Goal" :in-theory (enable supported-b*-bindingsp
                                     recreate-b*-bindings))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: there must be enough terms:
;; (defthm subsetp-equal-of-extract-terms-from-b*-binding-of-mv-nth-0-of-recreate-b*-binding
;;   (implies (supported-b*-bindingp binding)
;;            (subsetp-equal (extract-terms-from-b*-binding (mv-nth 0 (recreate-b*-binding binding new-terms)))
;;                           new-terms))
;;   :hints (("Goal" :in-theory (enable supported-b*-bindingp
;;                                      extract-terms-from-b*-binding
;;                                      recreate-b*-binding))))
