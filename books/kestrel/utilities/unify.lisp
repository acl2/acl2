; Onw-way unification of terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; One-way unification

(include-book "terms")
(include-book "acons-fast")

;move
(defthm pseudo-termp-of-car-when-pseudo-term-listp-cheap
  (implies (pseudo-term-listp terms)
           (pseudo-termp (car terms)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;TODO: Rename to something like one-way-unify or match.
;Lambdas should not occur.
(mutual-recursion
 ;;returns (mv success-flg alist)
 (defun unify-term-aux (term pattern alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-termp pattern)
                               (symbol-term-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (variablep pattern)
       (let ((match (assoc-eq pattern alist)))
         (if match
             (if (equal term (cdr match))
                 (mv t alist)
               (mv nil nil))
           (mv t (acons-fast pattern term alist))))
     (let ((pat-fn (ffn-symb pattern))) ;todo: use fquotep
       (if (eq 'quote pat-fn)
           (if (equal term pattern)
               (mv t alist)
             (mv nil nil))
         ;;regular function call:
         (if (and (atom pat-fn) ;;TODO: Handle lambdas?
                  (call-of pat-fn term))
             (unify-term-list-aux (fargs term) (fargs pattern) alist)
           (mv nil nil))))))

 ;;returns (mv success-flg alist)
 ;; TODO: Would be better to cdr down the patterns so that we can specialize
 ;; this when the pattern is known.
 (defun unify-term-list-aux (terms patterns alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-term-listp patterns)
                               (symbol-term-alistp alist))))
   (if (endp terms)
       (mv t alist)
     (mv-let (flg alist)
             (unify-term-aux (first terms) (first patterns) alist)
             (if (not flg)
                 (mv nil nil)
               (unify-term-list-aux (rest terms) (rest patterns) alist))))))

(make-flag unify-term-aux)

;needed for the verify-guards below
(defthm-flag-unify-term-aux
  (defthm symbol-term-alistp-of-mv-nth-1-of-unify-term-aux
    (implies (and (pseudo-termp term)
                  (pseudo-termp pattern)
                  (symbol-term-alistp alist))
             (symbol-term-alistp (mv-nth 1 (unify-term-aux term pattern alist))))
    :flag unify-term-aux)
  (defthm symbol-term-alistp-of-mv-nth-1-of-unify-term-list-aux
    (implies (and (pseudo-term-listp terms)
                  (pseudo-term-listp patterns)
                  (symbol-term-alistp alist))
             (symbol-term-alistp (mv-nth 1 (unify-term-list-aux terms patterns alist))))
    :flag unify-term-list-aux)
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(verify-guards unify-term-list-aux)

(defthm-flag-unify-term-aux
  (defthm alistp-of-mv-nth-1-of-unify-term-aux
    (implies (alistp alist)
             (alistp (mv-nth 1 (unify-term-aux term pattern alist))))
    :flag unify-term-aux)
  (defthm alistp-of-mv-nth-1-of-unify-term-list-aux
    (implies (alistp alist)
             (alistp (mv-nth 1 (unify-term-list-aux terms patterns alist))))
    :flag unify-term-list-aux)
  :hints (("Goal" :in-theory (enable alistp))))

(defthm-flag-unify-term-aux
  (defthm symbol-alistp-of-mv-nth-1-of-unify-term-aux
    (implies (and (symbol-alistp alist)
                  (pseudo-termp pattern))
             (symbol-alistp (mv-nth 1 (unify-term-aux term pattern alist))))
    :flag unify-term-aux)
  (defthm symbol-alistp-of-mv-nth-1-of-unify-term-list-aux
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp patterns))
             (symbol-alistp (mv-nth 1 (unify-term-list-aux terms patterns alist))))
    :flag unify-term-list-aux)
  :hints (("Goal" :in-theory (enable symbol-alistp))))

;returns (mv success-flg alist)
(defund unify-term (term pattern)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp pattern))))
  (unify-term-aux term pattern nil))

(defthm alistp-of-mv-nth-1-of-unify-term
  (alistp (mv-nth 1 (unify-term term pattern)))
  :hints (("Goal" :in-theory (enable acl2::unify-term))))

(defthm symbol-alistp-of-mv-nth-1-of-unify-term
  (implies (pseudo-termp pattern)
           (symbol-alistp (mv-nth 1 (unify-term term pattern))))
  :hints (("Goal" :in-theory (enable acl2::unify-term))))

(defthm symbol-term-alistp-of-mv-nth-1-of-unify-term
  (implies (and (pseudo-termp term)
                (pseudo-termp pattern))
           (symbol-term-alistp (mv-nth 1 (unify-term term pattern))))
  :hints (("Goal" :in-theory (enable acl2::unify-term))))
