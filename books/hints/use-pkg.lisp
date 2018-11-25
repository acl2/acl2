; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; We implement a custom keyword hint that extends the following property of
; :use hints, quoting :DOC lemma-instance, but in a very limited way as
; described below.

;   Otherwise,
;   if one or more variables vi do not occur in F, but for each such vi
;   exactly one variable v with the same [symbol-name] as vi occurs in
;   F and no other vj with the same symbol-name as v is bound in the
;   substitution, then the pair (vi ti) is replaced by the pair (v ti)
;   in the substitution.

; The limitation here is that we only support the forms

;   :use-pkg ((:instance lemma-name-1 (v1 t1) ...)
;             (:instance lemma-name-2 (v1 t1) ...)
;             ..)

; and the following expected abbrevations, as for :use hints.

;   :use-pkg lemma-name
; and
;   :use-pkg (lemma-name)
; abbreviate
;   :use-pkg ((:instance lemma-name))

;   :use-pkg (:instance lemma-name-1 (v1 t1) ...)
; abbreviates
;   :use-pkg ((:instance lemma-name-1 (v1 t1) ...))

; For example, we do NOT yet support the following.

;   :use-pkg ((:instance (:functional-instance ...) ...))

(in-package "ACL2")

(defun illegal-use-pkg (val msg)
  (declare (xargs :guard t))
  (er hard? :use-pkg
      "Illegal :use-pkg hint, ~x0~@0"
      val
      (if msg
          (msg "~|~@0" msg)
        "")))

(defun fix-single-use-hint-for-pkg (val hint)

; Return a legal :use hint corresponding to the lmi, val, except without the
; leading :instance.

  (declare (xargs :guard t))
  (cond ((symbolp val)
         (list val))
        ((and (consp val)
              (eq (car val) :instance))
         (cdr val))
        (t (illegal-use-pkg hint
                            (msg "Specifically, the following member of the ~
                                  specified list of instances is illegal:~|~x0"
                                 val)))))

(defun assoc-eq-modulo-package (sym alist)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-alistp alist))))
  (cond ((endp alist) nil)
        ((equal (symbol-name sym)
                (symbol-name (caar alist)))
         (car alist))
        (t (assoc-eq-modulo-package sym (cdr alist)))))

(defun fix-use-pkg-hint-doublets-1 (vars lst pkg)
  (declare (xargs :guard (and (symbol-listp vars)
                              (symbol-doublet-listp lst)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (cond ((endp vars)
         nil)
        ((assoc-eq-modulo-package (car vars) lst)
         (fix-use-pkg-hint-doublets-1 (cdr vars) lst pkg))
        (t
         (cons (list (car vars)
                     (intern$ (symbol-name (car vars)) pkg))
               (fix-use-pkg-hint-doublets-1
                (cdr vars) lst pkg)))))

(defun fix-use-pkg-hint-doublets (lst vars pkg)
  (declare (xargs :guard (and (symbol-doublet-listp lst)
                              (symbol-listp vars)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (let ((new-lst (fix-use-pkg-hint-doublets-1 vars lst pkg)))
    (append new-lst lst)))

(defun meta-extract-formula-world (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (or (getpropc name 'theorem nil wrld)
      (mv-let (flg prop)
        (constraint-info name wrld)
        (cond ((unknown-constraints-p prop)
               *t*)
              (flg (ec-call (conjoin prop)))
              (t prop)))))

; We can prove that all-vars returns a symbol-listp (e.g., see
; symbol-listp-all-vars1 in system/verified-termination-and-guards.lisp).  But
; that's not enough for us, because the term from meta-extract-formula isn't
; known to be a pseudo-termp.  So we make life easy as follows.

(defun gentle-all-vars (term)
  (declare (xargs :guard t))
  (let ((vars (ec-call (all-vars term))))
    (cond ((symbol-listp vars) ; always true
           vars)
          (t (er hard? 'gentle-all-vars
                 "Can't happen!  Input: ~x0"
                 term)))))

(defun fix-use-hint-for-pkg-1 (val pkg wrld hint)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (let ((val (fix-single-use-hint-for-pkg val hint)))
    (cond ((not (true-listp val))
           (illegal-use-pkg hint
                            (msg "It seems that a non-true-list has been ~
                                  generated for some instance.")))
          ((not (symbolp (car val)))
           (illegal-use-pkg hint
                            (msg "Only symbols are allowed for designating ~
                                  formulas to use, but ~x0 is not a symbol."
                                 val)))
          ((not (symbol-doublet-listp (cdr val)))
           (illegal-use-pkg hint
                            (msg "Specifically, the following hint is a ~
                                  symbol that is not followed by a list of ~
                                  pairs (symbol term): ~x0"
                                 val)))
          (t
           (let ((term (meta-extract-formula-world (car val) wrld)))
             (cond ((null term)
                    (illegal-use-pkg hint
                                     (msg "Specifically, the symbol ~x0 does ~
                                           not designate a formula."
                                          (car val))))
                   (t (list* :instance
                             (car val)
                             (fix-use-pkg-hint-doublets
                              (cdr val)
                              (gentle-all-vars term)
                              pkg)))))))))

(defun fix-use-hint-for-pkg-lst (lst pkg wrld hint)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (cond ((atom lst)
         (cond ((null lst)
                nil)
               (t (illegal-use-pkg hint
                                   "The hint is a list that is not ~
                                    nil-terminated."))))
        (t (cons (fix-use-hint-for-pkg-1 (car lst) pkg wrld hint)
                 (fix-use-hint-for-pkg-lst (car lst) pkg wrld hint)))))

(defun fix-use-hint-for-pkg (val state)
  (declare (xargs :stobjs state))
  (let ((pkg (current-package state))
        (wrld (w state)))
    (cond ((not (and (stringp pkg)
                     (not (equal pkg "")))) ; both always true
           (illegal-use-pkg val
                            "The current package is not a non-empty ~
                             string,which has seemed impossible."))
          ((symbolp val)
           (list (fix-use-hint-for-pkg-1 val pkg wrld val)))
          ((and (consp val)
                (symbolp (car val)))
           (list (fix-use-hint-for-pkg-1 val pkg wrld val)))
          (t (fix-use-hint-for-pkg-lst val pkg wrld val)))))

(add-custom-keyword-hint :use-pkg
                         (value
                          (splice-keyword-alist
                           :use-pkg
                           (list :use
                                 (fix-use-hint-for-pkg val state))
                           keyword-alist)))
