#|

 Copied from misc/records because if I want to get my hands on some
 of the local defthms and if I include it and then try proving some
 of the local defthms, the proofs fail. I didn't feel like figuring
 out what was going on, but I should keep this synchronized with the
 original book.

 Another idea is to create a new version of records that requires
 fields to be symbols and which is going to support efficient
 execution and simple reasoning.

|#


; Rob Sumners 


#||
Note: The license below is based on the template at:
http://opensource.org/licenses/BSD-3-Clause

Copyright (C) 2013, Regents of the University of Texas
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

o Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

o Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

o Neither the name of the University of Texas, Austin nor the names of
  its contributors may be used to endorse or promote products derived
  from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

||#

(in-package "ACL2")
(include-book "misc/total-order" :dir :system)

;; See the original book for documentation.

;; BEGIN records definitions.

(defun rcdp1 (x)

; Tail-recursive version of rcdp for alistp argument.

  (declare (xargs :guard (alistp x)))
  (or (endp x)
      (and (cdar x)
	   (or (null (cdr x))
               (and (<< (caar x) (caadr x))
                    (rcdp1 (cdr x)))))))

(defun rcdp (x)
  (declare (xargs :guard t))
  (mbe :logic (or (null x)
                  (and (consp x)
                       (consp (car x))
                       (rcdp (cdr x))
                       (cdar x)
                       (or (null (cdr x))
                           (<< (caar x) (caadr x)))))

; Faster version that is tail recursive.  See also
; books/defexec/other-apps/records/records.lisp for related approaches to fast
; executability for records.

       :exec (and (alistp x)
                  (rcdp1 x))))

(defun ifrp (x) ;; ill-formed rcdp
  (declare (xargs :guard t))
  (or (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (null (caar x))
           (ifrp (cdar x)))))

(defun acl2->rcd (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ifrp x) (list (cons nil x)) x))

(defun rcd->acl2 (x)  ;; inverse of acl2->rcd.
  (declare (xargs :guard (rcdp x)))
  (if (ifrp x) (cdar x) x))

(defun g-aux (a x) ;; record g(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp x)))
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (g-aux a (cdr x)))))

(defun g (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (g-aux a (acl2->rcd x)))

(defun mget (a x)
  (declare (xargs :guard t))
  (g a x))

(defun s-aux (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp r)))
  (cond ((or (endp r)
             (<< a (caar r)))
         (if v (cons (cons a v) r) r))
        ((equal a (caar r))
         (if v (cons (cons a v) (cdr r)) (cdr r)))
        (t
         (cons (car r) (s-aux a v (cdr r))))))

;; we need the following theorems in order to get the guard for s to verify.

(defthm s-aux-is-bounded
  (implies (and (rcdp r)
                (s-aux a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (s-aux a v r)))))

(defthm s-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (s-aux a v r))))

(defun s (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (rcd->acl2 (s-aux a v (acl2->rcd x))))

(defun mset (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (s a v x))


;;;; basic property of records ;;;;

(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite))

;;;; initial properties of s-aux and g-aux ;;;;

(defthm g-aux-same-s-aux
  (implies (rcdp r)
           (equal (g-aux a (s-aux a v r))
                  v)))

(defthm g-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (g-aux a (s-aux b v r))
                  (g-aux a r))))

(defthm s-aux-same-g-aux
  (implies (rcdp r)
           (equal (s-aux a (g-aux a r) r)
                  r)))

(defthm s-aux-same-s-aux
  (implies (rcdp r)
           (equal (s-aux a y (s-aux a x r))
                  (s-aux a y r))))

(defthm s-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

(defthm s-aux-non-nil-cannot-be-nil
  (implies (and v (rcdp r))
           (s-aux a v r)))

(defthm g-aux-is-nil-for-<<
  (implies (and (rcdp r)
                (<< a (caar r)))
           (equal (g-aux a r) nil)))


;;;; properties of acl2->rcd and rcd->acl2 ;;;;

(defthm acl2->rcd-rcd->acl2-of-rcdp
  (implies (rcdp x)
           (equal (acl2->rcd (rcd->acl2 x))
                  x)))

(defthm acl2->rcd-returns-rcdp
  (rcdp (acl2->rcd x)))

(defthm acl2->rcd-preserves-equality
  (iff (equal (acl2->rcd x) (acl2->rcd y))
       (equal x y)))

(defthm rcd->acl2-acl2->rcd-inverse
  (equal (rcd->acl2 (acl2->rcd x)) x))

(defthm rcd->acl2-of-record-non-nil
  (implies (and r (rcdp r))
           (rcd->acl2 r)))

(in-theory (disable acl2->rcd rcd->acl2))


;;;; final (exported) properties of record g(et) and s(et) ;;;;

;; NOTE that these theorems basically follow from the "equivalent" properties
;; for s-aux and g-aux with rcdp hypothesis, and the lemmas about the acl2->rcd
;; and its inverse rcd->acl2. If the user wanted to add to the following set of
;; exported theorems, they should add the corresponding lemma about s-aux and
;; g-aux using rcdp hypothesis and then add the theorem here about the generic
;; s(et) and g(et) they wish to export from the book.

(defthm g-same-s
  (equal (g a (s a v r))
         v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

;;;; NOTE: The following can be used instead of the above rules to force ACL2
;;;; to do a case-split. We disable this rule by default since it can lead to
;;;; an expensive case explosion, but in many cases, this rule may be more
;;;; effective than two rules above and should be enabled.

(defthm g-of-s-redux
  (equal (g a (s b v r))
         (if (equal a b) v (g a r))))

(in-theory (disable g-of-s-redux))

(defthm s-same-g
  (equal (s a (g a r) r)
         r))

(defthm s-same-s
  (equal (s a y (s a x r))
         (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

;; the following theorems are less relevant but have been useful in dealing
;; with a default record of NIL.

(defthm g-of-nil-is-nil
  (not (g a nil)))

(defthm s-non-nil-cannot-be-nil
  (implies v (s a v r))
  :hints (("Goal"
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (s-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-g-non-nil
  (implies (g a r) r)
  :rule-classes :forward-chaining)

;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered.

(in-theory (disable s g))
(in-theory (disable s-aux g-aux rcdp1 rcdp ifrp))

;; Contributed by Sandip Ray (who isn't sure that he is the one who originally
;; wrote this), but renamed here to record-update to avoid name conflicts.

(defun ss-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (ss-macro (cddr upds)
              (list 's (car upds) (cadr upds) result))))

(defmacro ss (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (ss-macro updates old))

