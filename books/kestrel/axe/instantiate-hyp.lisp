; A tool for instantiating a hyp of a rule
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Utilities for instantiating hypotheses of rules.  This book depends on
;; evaluator.lisp, but see also instantiate-hyp-basic.lisp.

(include-book "evaluator")
(include-book "axe-trees")
(local (include-book "kestrel/lists-light/len" :dir :system))

;;;
;;; instantiate-hyp
;;;

;move
;FORM is a tree (from the hyp of a rule) with quoteps and vars at the leaves
;ALIST binds vars to quoteps and/or nodenums
;this one does *not* wrap remaining free vars in :free
;returns (mv form free-vars-flg) where FORM has been instantiated with ALIST and FREE-VARS-FLG indicates whether any variables remain in FORM (actually, free-vars-flg is an accumulator?)
(mutual-recursion
  (defund instantiate-hyp (form alist free-vars-flg interpreted-function-alist)
    (declare (xargs :verify-guards nil ;done below
                    :guard (and (pseudo-termp form)
                                (symbol-alistp alist)
                                (all-dargp (strip-cdrs alist))
                                (interpreted-function-alistp interpreted-function-alist))))
    (if (variablep form)
        (let ((match (assoc-eq form alist)))
          (if match
              (mv (cdr match) free-vars-flg) ;the var has a binding in the alist and so is not free
            (mv form t)                      ;the var is free
            ))
      (let ((fn (ffn-symb form)))
        (if (eq 'quote fn)
            (mv form free-vars-flg)
          ;;a function call (used to handle IFs specially but that didn't seem worth it):
          (mv-let (ground-termp args free-vars-flg)
                  (instantiate-hyp-lst (fargs form) alist free-vars-flg interpreted-function-alist)
                  (if (and ground-termp
                           (or (member-eq fn *axe-evaluator-functions*) ;switched Wed Jan 13 07:55:10 2010
                               (assoc-eq fn interpreted-function-alist) ;ffffffixme
                               )
                           ;; (not (eq 'repeat fn)) ;Wed Feb 16 22:22:27 2011
                           )
                      (mv (enquote (apply-axe-evaluator-to-quoted-args fn args interpreted-function-alist 0))
                          free-vars-flg)
                    ;;                              (let ((possible-val (eval-fn-if-possible fn (unquote-list args))))
                    ;;                                (if possible-val ;possible-val is quoted (or is nil if we can't eval the fn)
                    ;;                                    (mv possible-val free-vars-flg) ;should be nil
                    ;;                                  (mv (cons fn args) free-vars-flg)))
                    (mv (cons fn args) free-vars-flg)))))))

  ;;returns (mv ground-termp args free-vars-flg)
  (defund instantiate-hyp-lst (l alist free-vars-flg interpreted-function-alist)
    (declare (xargs :guard (and (symbol-alistp alist)
                                (all-dargp (strip-cdrs alist))
                                (pseudo-term-listp l)
                                (interpreted-function-alistp interpreted-function-alist))))
    (if (endp l)
        (mv t nil free-vars-flg)
      (mv-let (new-first free-vars-flg)
              (instantiate-hyp (first l) alist free-vars-flg interpreted-function-alist)
              (mv-let (rest-ground-termp new-rest free-vars-flg)
                      (instantiate-hyp-lst (rest l) alist free-vars-flg interpreted-function-alist)
                      (mv (and rest-ground-termp (quotep new-first))
                          (cons new-first new-rest)
                          free-vars-flg))))))

(make-flag instantiate-hyp)

(defthm-flag-instantiate-hyp
  (defthm true-listp-of-mv-nth-1-of-instantiate-hyp-lst
    (true-listp (mv-nth 1 (instantiate-hyp-lst l alist free-vars-flg interpreted-function-alist)))
    :flag instantiate-hyp-lst)
  :skip-others t
  :hints (("Goal" :in-theory (enable instantiate-hyp instantiate-hyp-lst))))

(defthm-flag-instantiate-hyp
  (defthm len-of-mv-nth-1-of-instantiate-hyp-lst
    (equal (len (mv-nth 1 (instantiate-hyp-lst l alist free-vars-flg interpreted-function-alist)))
           (len l))
    :flag instantiate-hyp-lst)
  :skip-others t
  :hints (("Goal" :in-theory (enable instantiate-hyp instantiate-hyp-lst))))

(defthm-flag-instantiate-hyp
  (defthm axe-treep-of-mv-nth-0-of-instantiate-hyp2
    (implies (and (pseudo-termp form)
                  (all-dargp (strip-cdrs alist)))
             (axe-treep (mv-nth 0 (instantiate-hyp form alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp)
  (defthm all-axe-treep-of-mv-nth-1-of-instantiate-hyp2
    (implies (and (pseudo-term-listp l)
                  (all-dargp (strip-cdrs alist)))
             (all-axe-treep (mv-nth 1 (instantiate-hyp-lst l alist free-vars-flg
                                                                   interpreted-function-alist))))
    :flag instantiate-hyp-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp instantiate-hyp-lst))))

(defthm-flag-instantiate-hyp
  (defthm all-myquotep-of-mv-nth-1-of-instantiate-hyp-lst
    (implies (and (mv-nth 0 (instantiate-hyp-lst l alist free-vars-flg interpreted-function-alist))
                  (pseudo-term-listp l)
                  (all-dargp (strip-cdrs alist)))
             (all-myquotep (mv-nth 1 (instantiate-hyp-lst l alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp-lst)
  :skip-others t
  :hints (("Goal" :in-theory (e/d (instantiate-hyp instantiate-hyp-lst) (myquotep)))))

(verify-guards instantiate-hyp :otf-flg t :hints (("Goal" :in-theory (enable pseudo-termp))))
