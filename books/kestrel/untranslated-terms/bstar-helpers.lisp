; Helper functions for manipulating untranslated terms
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

;; Recognize a supported b* binding, of the form (<binder> ...<expressions>...)
;; where the number of allowed expressions depends on the binder.
(defun supported-b*-bindingp (binding)
  (declare (xargs :guard t))
  (and (true-listp binding)
       (consp binding)
       (let ((binder (first binding))
             (expressions (rest binding)))
         (if (atom binder)
             ;; A few binders are atoms:
             (or (eq binder '-) ; (- <term> ... <term>) for any number of terms
                 ;; todo: uncomment once supported everywhere:
                 ;; (eq binder '&) ; (& <term> ... <term>) for any number of terms
                 (and (symbolp binder) ; (<var> <term>)
                      (= 1 (len expressions))))
           ;; Most binders are conses:
           (case (car binder)
             ;; todo must be at least 1 expression:
             ((when if unless) (= 1 (len (fargs binder)))) ; ((when <term>) <term> ... <term>)
             (mv (and (symbol-listp (fargs binder)) ; ((mv <var> ... <var>) <term>)
                      (= 1 (len expressions))))
             ;; todo: add more kinds of supported binder
             (otherwise nil))))))

;; Recognize a list of supported b* bindings
(defun supported-b*-bindingsp (bindings)
  (declare (xargs :guard t))
  (if (atom bindings)
      (null bindings)
    (and (supported-b*-bindingp (first bindings))
         (supported-b*-bindingsp (rest bindings)))))

;; Extracts all the terms in the b* binding, in order
(defund extract-terms-from-b*-binding (binding)
  (declare (xargs :guard (supported-b*-bindingp binding)))
  (let ((binder (first binding)))
    (if (symbolp binder)
        (if (eq binder '-) ; (- <term> ... <term>) for any number of terms
            (fargs binding)
          ;; it's a variable:
          (list (farg1 binding)))
      (case (car binder)
        ((when if unless) (cons (farg1 binder) (fargs binding)))
        (mv (list (farg1 binding)))
        ;; Should never happen:
        (t (er hard 'extract-terms-from-b*-binding "Unsupported b* binder: ~x0." binding))))))

(defthm true-listp-of-extract-terms-from-b*-binding
  (implies (supported-b*-bindingp binding)
           (true-listp (extract-terms-from-b*-binding binding)))
  :hints (("Goal" :in-theory (enable extract-terms-from-b*-binding))))

;; Extracts all the terms in the b* bindings, in order
(defun extract-terms-from-b*-bindings (bindings)
  (declare (xargs :guard (supported-b*-bindingsp bindings)))
  (if (endp bindings)
      nil
    (append (extract-terms-from-b*-binding (first bindings))
            (extract-terms-from-b*-bindings (rest bindings)))))

;; Returns (mv new-binding rest-new-terms).
(defun recreate-b*-binding (binding new-terms)
  (declare (xargs :guard (and (supported-b*-bindingp binding)
                              (true-listp new-terms))))
  (let* ((binder (first binding)))
    (if (symbolp binder)
        (if (eq binder '-) ; (- <term> ... <term>) for any number of terms
            (let ((num-terms (len (fargs binding))))
              (mv `(,binder ,@(take num-terms new-terms))
                  (nthcdr num-terms new-terms)))
          ;; it's a variable:
          (mv `(,binder ,(first new-terms)) ; (<var> <term)
              (rest new-terms)))
      (case (car binder)
        ((when if unless) ; ((when <term>) <term> ... <term>)
         (let ((num-args (len (fargs binding))))
           (mv `((,(car binder) ,(first new-terms)) ,@(take num-args (rest new-terms)))
               (nthcdr (+ 1 num-args) new-terms))))
        (mv ; ((mv <var> ... <var>) <term>)
         (mv `((mv ,@(fargs binder)) ,(first new-terms))
             (rest new-terms)))
        ;; Should never happen:
        (otherwise (progn$ (er hard 'recreate-b*-binding "Unsupported b* binder: ~x0." binding)
                           (mv nil nil)))))))

(defun recreate-b*-bindings (bindings new-terms)
  (declare (xargs :guard (and (supported-b*-bindingsp bindings)
                              (true-listp new-terms))))
  (if (endp bindings)
      nil
    (mv-let (new-first new-terms)
      (recreate-b*-binding (first bindings) new-terms)
      (let ((new-rest (recreate-b*-bindings (rest bindings) new-terms)))
        (cons new-first new-rest)))))
