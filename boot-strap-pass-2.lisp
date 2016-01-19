; ACL2 Version 7.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2016, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; This file, boot-strap-pass-2, is compiled and loaded; but it is only
; processed during the second pass of the boot-strap process, not the first.

; We introduce proper defattach events, i.e., without :skip-checks t.  Here are
; some guiding principles for making system functions available for attachment
; by users.

; - The initial attachment is named by adding the suffix -builtin.  For
;   example, worse-than is a constrained function initially attached to
;   worse-than-builtin.

; - Use the weakest logical specs we can (even if T), without getting
;   distracted by names.  For example, we do not specify a relationship between
;   worse-than-or-equal and worse-than.

; - Only make functions attachable if they are used in our sources somewhere
;   outside their definitions.  So for example, we do not introduce
;   worse-than-list as a constrained function, since its only use is in the
;   mutual-recursion event that defines worse-than.

; We conclude by defining some theories, at the end so that they pick up the
; rest of this file.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Miscellaneous verify-termination and guard verification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cons-term and symbol-class -- at one point during development, used in
; fncall-term, but anyhow, generally useful to have in logic mode

(verify-termination-boot-strap quote-listp) ; and guards
(verify-termination-boot-strap cons-term1) ; and guards
(verify-termination-boot-strap cons-term) ; and guards
(verify-termination-boot-strap symbol-class) ; and guards

; observation1-cw

(verify-termination-boot-strap observation1-cw)
(verify-guards observation1-cw)

; packn1 and packn

(verify-termination-boot-strap packn1) ; and guards

(encapsulate ()

(local
 (defthm character-listp-explode-nonnegative-integer
   (implies (character-listp z)
            (character-listp (explode-nonnegative-integer x y z)))
   :rule-classes ((:forward-chaining :trigger-terms
                                     ((explode-nonnegative-integer x y z))))))

(local
 (defthm character-listp-explode-atom
   (character-listp (explode-atom x y))
   :rule-classes ((:forward-chaining :trigger-terms
                                     ((explode-atom x y))))))

(verify-termination-boot-strap packn) ; and guards
(verify-termination-boot-strap packn-pos) ; and guards
)

(verify-termination-boot-strap read-file-into-string1) ; and guards

(encapsulate
 ()

; At one the following local lemma seemed to be helpful, but it is not
; currently necessary.  If we simplify read-file-into-string2, for example by
; removing ec-call, then perhaps we will need this lemma once again.

;(local
; (defthm stringp-read-file-into-string1
;   (implies (car (read-file-into-string1 channel state ans bound))
;            (stringp (car (read-file-into-string1 channel state ans
;                                                  bound))))))

 (verify-termination-boot-strap read-file-into-string2) ; and guards
 )

(verify-termination-boot-strap read-file-into-string) ; and guards

; miscellaneous

(verify-termination-boot-strap guard-or-termination-theorem-msg) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachment: too-many-ifs-post-rewrite and too-many-ifs-pre-rewrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+acl2-loop-only
; The above readtime conditional avoids a CLISP warning, and lets the defproxy
; for print-clause-id-okp provide the raw Lisp definition.
(encapsulate
 ((too-many-ifs-post-rewrite (args val) t
                             :guard (and (pseudo-term-listp args)
                                         (pseudo-termp val))))
 (local (defun too-many-ifs-post-rewrite (args val)
          (list args val))))

; The following events are derived from the original version of community book
; books/system/too-many-ifs.lisp.  But here we provide a proof that does not
; depend on books.  Our approach was to take the proof in the above book,
; eliminate the unnecessary use of an arithmetic book, expand away all uses of
; macros and make-events, avoid use of (theory 'minimal-theory) since that
; theory didn't yet exist (where these events were originally placed), and
; apply some additional hand-editing in order (for example) to remove hints
; depending on the tools/flag community book.  We have left original events
; from the book as comments.

(encapsulate
 ()

 (logic)

;;; (include-book "tools/flag" :dir :system)

; In the original book, but not needed for its certification:
; (include-book "arithmetic/top-with-meta" :dir :system)

; Comments like the following show events from the original book.

;;; (make-flag pseudo-termp-flg
;;;            pseudo-termp
;;;            :flag-var flg
;;;            :flag-mapping ((pseudo-termp . term)
;;;                           (pseudo-term-listp . list))
;;;            :defthm-macro-name defthm-pseudo-termp
;;;            :local t)

 (local
  (defun-nx pseudo-termp-flg (flg x lst)
    (declare (xargs :verify-guards nil
                    :normalize nil
                    :measure (case flg (term (acl2-count x))
                               (otherwise (acl2-count lst)))))
    (case flg
      (term (if (consp x)
                (cond ((equal (car x) 'quote)
                       (and (consp (cdr x))
                            (equal (cddr x) nil)))
                      ((true-listp x)
                       (and (pseudo-termp-flg 'list nil (cdr x))
                            (cond ((symbolp (car x)) t)
                                  ((true-listp (car x))
                                   (and (equal (length (car x)) 3)
                                        (equal (caar x) 'lambda)
                                        (symbol-listp (cadar x))
                                        (pseudo-termp-flg 'term (caddar x) nil)
                                        (equal (length (cadar x))
                                               (length (cdr x)))))
                                  (t nil))))
                      (t nil))
              (symbolp x)))
      (otherwise (if (consp lst)
                     (and (pseudo-termp-flg 'term (car lst) nil)
                          (pseudo-termp-flg 'list nil (cdr lst)))
                   (equal lst nil))))))
 (local
  (defthm pseudo-termp-flg-equivalences
    (equal (pseudo-termp-flg flg x lst)
           (case flg (term (pseudo-termp x))
             (otherwise (pseudo-term-listp lst))))
    :hints
    (("goal" :induct (pseudo-termp-flg flg x lst)))))
 (local (in-theory (disable (:definition pseudo-termp-flg))))

; Added here (not present or needed in the certified book):
 (verify-termination-boot-strap max) ; and guards

 (verify-termination-boot-strap var-counts1)

;;; (make-flag var-counts1-flg
;;;            var-counts1
;;;            :flag-var flg
;;;            :flag-mapping ((var-counts1 . term)
;;;                           (var-counts1-lst . list))
;;;            :defthm-macro-name defthm-var-counts1
;;;            :local t)

 (local
  (defun-nx var-counts1-flg (flg rhs arg lst acc)
    (declare (xargs :verify-guards nil
                    :normalize nil
                    :measure (case flg (term (acl2-count rhs))
                               (otherwise (acl2-count lst)))
                    :hints nil
                    :well-founded-relation o<
                    :mode :logic)
             (ignorable rhs arg lst acc))
    (case flg
      (term (cond ((equal arg rhs) (+ 1 acc))
                  ((consp rhs)
                   (cond ((equal 'quote (car rhs)) acc)
                         ((equal (car rhs) 'if)
                          (max (var-counts1-flg 'term
                                                (caddr rhs)
                                                arg nil acc)
                               (var-counts1-flg 'term
                                                (cadddr rhs)
                                                arg nil acc)))
                         (t (var-counts1-flg 'list
                                             nil arg (cdr rhs)
                                             acc))))
                  (t acc)))
      (otherwise (if (consp lst)
                     (var-counts1-flg 'list
                                      nil arg (cdr lst)
                                      (var-counts1-flg 'term
                                                       (car lst)
                                                       arg nil acc))
                   acc)))))
 (local
  (defthm
    var-counts1-flg-equivalences
    (equal (var-counts1-flg flg rhs arg lst acc)
           (case flg (term (var-counts1 arg rhs acc))
             (otherwise (var-counts1-lst arg lst acc))))))
 (local (in-theory (disable (:definition var-counts1-flg))))

;;; (defthm-var-counts1 natp-var-counts1
;;;   (term
;;;    (implies (natp acc)
;;;             (natp (var-counts1 arg rhs acc)))
;;;    :rule-classes :type-prescription)
;;;   (list
;;;    (implies (natp acc)
;;;             (natp (var-counts1-lst arg lst acc)))
;;;    :rule-classes :type-prescription)
;;;   :hints (("Goal" :induct (var-counts1-flg flg rhs arg lst acc))))

 (local
  (defthm natp-var-counts1
    (case flg
      (term (implies (natp acc)
                     (natp (var-counts1 arg rhs acc))))
      (otherwise (implies (natp acc)
                          (natp (var-counts1-lst arg lst acc)))))
    :hints (("Goal" :induct (var-counts1-flg flg rhs arg lst acc)))
    :rule-classes nil))
 (local
  (defthm natp-var-counts1-term
    (implies (natp acc)
             (natp (var-counts1 arg rhs acc)))
    :hints (("Goal" ; :in-theory (theory 'minimal-theory)
             :use ((:instance natp-var-counts1 (flg 'term)))))
    :rule-classes :type-prescription))
 (local
  (defthm natp-var-counts1-list
    (implies (natp acc)
             (natp (var-counts1-lst arg lst acc)))
    :hints (("Goal" ; :in-theory (theory 'minimal-theory)
             :use ((:instance natp-var-counts1 (flg 'list)))))
    :rule-classes :type-prescription))

 (verify-guards var-counts1)

 (verify-termination-boot-strap var-counts) ; and guards

;;; Since the comment about var-counts says that var-counts returns a list of
;;; nats as long as lhs-args, I prove those facts, speculatively.

; Except, we reason instead about integer-listp.  See the comment just above
; the commented-out definition of nat-listp in the source code (file
; rewrite.lisp).
; (verify-termination nat-listp)

 (local
  (defthm integer-listp-var-counts
    (integer-listp (var-counts lhs-args rhs))))

 (local
  (defthm len-var-counts
    (equal (len (var-counts lhs-args rhs))
           (len lhs-args))))

 (verify-termination-boot-strap count-ifs) ; and guards

; Added here (not present or needed in the certified book):
 (verify-termination-boot-strap ifix) ; and guards

; Added here (not present or needed in the certified book):
 (verify-termination-boot-strap abs) ; and guards

; Added here (not present or needed in the certified book):
 (verify-termination-boot-strap expt) ; and guards

; Added here (not present or needed in the certified book):
 (local (defthm natp-expt
          (implies (and (integerp base)
                        (integerp n)
                        (<= 0 n))
                   (integerp (expt base n)))
          :rule-classes :type-prescription))

; Added here (not present or needed in the certified book):
 (verify-termination-boot-strap signed-byte-p) ; and guards

 (verify-termination-boot-strap too-many-ifs0) ; and guards

 (verify-termination-boot-strap too-many-ifs-pre-rewrite-builtin) ; and guards

 (verify-termination-boot-strap occur-cnt-bounded)

;;; (make-flag occur-cnt-bounded-flg
;;;            occur-cnt-bounded
;;;            :flag-var flg
;;;            :flag-mapping ((occur-cnt-bounded . term)
;;;                           (occur-cnt-bounded-lst . list))
;;;            :defthm-macro-name defthm-occur-cnt-bounded
;;;            :local t)

 (local
  (defun-nx occur-cnt-bounded-flg (flg term2 term1 lst a m bound-m)
    (declare (xargs :verify-guards nil
                    :normalize nil
                    :measure (case flg (term (acl2-count term2))
                               (otherwise (acl2-count lst))))
             (ignorable term2 term1 lst a m bound-m))
    (case flg
      (term (cond ((equal term1 term2)
                   (if (< bound-m a) -1 (+ a m)))
                  ((consp term2)
                   (if (equal 'quote (car term2))
                       a
                     (occur-cnt-bounded-flg 'list
                                            nil term1 (cdr term2)
                                            a m bound-m)))
                  (t a)))
      (otherwise (if (consp lst)
                     (let ((new (occur-cnt-bounded-flg 'term
                                                       (car lst)
                                                       term1 nil a m bound-m)))
                       (if (equal new -1)
                           -1
                         (occur-cnt-bounded-flg 'list
                                                nil term1 (cdr lst)
                                                new m bound-m)))
                   a)))))
 (local
  (defthm occur-cnt-bounded-flg-equivalences
    (equal (occur-cnt-bounded-flg flg term2 term1 lst a m bound-m)
           (case flg
             (term (occur-cnt-bounded term1 term2 a m bound-m))
             (otherwise (occur-cnt-bounded-lst term1 lst a m bound-m))))))
 (local (in-theory (disable (:definition occur-cnt-bounded-flg))))

;;; (defthm-occur-cnt-bounded integerp-occur-cnt-bounded
;;;   (term
;;;    (implies (and (integerp a)
;;;                  (integerp m))
;;;             (integerp (occur-cnt-bounded term1 term2 a m bound-m)))
;;;    :rule-classes :type-prescription)
;;;   (list
;;;    (implies (and (integerp a)
;;;                  (integerp m))
;;;             (integerp (occur-cnt-bounded-lst term1 lst a m bound-m)))
;;;    :rule-classes :type-prescription)
;;;   :hints (("Goal" :induct (occur-cnt-bounded-flg flg term2 term1 lst a m
;;;                                                  bound-m))))

 (local
  (defthm integerp-occur-cnt-bounded
    (case flg
      (term (implies (and (integerp a) (integerp m))
                     (integerp (occur-cnt-bounded term1 term2 a m bound-m))))
      (otherwise
       (implies (and (integerp a) (integerp m))
                (integerp (occur-cnt-bounded-lst term1 lst a m bound-m)))))
    :rule-classes nil
    :hints
    (("Goal" :induct (occur-cnt-bounded-flg flg term2 term1 lst a m bound-m)))))
 (local
  (defthm integerp-occur-cnt-bounded-term
    (implies (and (integerp a) (integerp m))
             (integerp (occur-cnt-bounded term1 term2 a m bound-m)))
    :rule-classes :type-prescription
    :hints (("goal" ; :in-theory (theory 'minimal-theory)
             :use ((:instance integerp-occur-cnt-bounded
                              (flg 'term)))))))
 (local
  (defthm integerp-occur-cnt-bounded-list
    (implies (and (integerp a) (integerp m))
             (integerp (occur-cnt-bounded-lst term1 lst a m bound-m)))
    :rule-classes :type-prescription
    :hints (("goal" ; :in-theory (theory 'minimal-theory)
             :use ((:instance integerp-occur-cnt-bounded
                              (flg 'list)))))))

;;; (defthm-occur-cnt-bounded signed-byte-p-30-occur-cnt-bounded-flg
;;;   (term
;;;    (implies (and (force (signed-byte-p 30 a))
;;;                  (signed-byte-p 30 m)
;;;                  (signed-byte-p 30 (+ bound-m m))
;;;                  (force (<= 0 a))
;;;                  (<= 0 m)
;;;                  (<= 0 bound-m)
;;;                  (<= a (+ bound-m m)))
;;;             (and (<= -1 (occur-cnt-bounded term1 term2 a m bound-m))
;;;                  (<= (occur-cnt-bounded term1 term2 a m bound-m) (+ bound-m m))))
;;;    :rule-classes :linear)
;;;   (list
;;;    (implies (and (force (signed-byte-p 30 a))
;;;                  (signed-byte-p 30 m)
;;;                  (signed-byte-p 30 (+ bound-m m))
;;;                  (force (<= 0 a))
;;;                  (<= 0 m)
;;;                  (<= 0 bound-m)
;;;                  (<= a (+ bound-m m)))
;;;             (and (<= -1 (occur-cnt-bounded-lst term1 lst a m bound-m))
;;;                  (<= (occur-cnt-bounded-lst term1 lst a m bound-m) (+ bound-m m))))
;;;    :rule-classes :linear)
;;;   :hints (("Goal" :induct (occur-cnt-bounded-flg flg term2 term1 lst a m
;;;                                                  bound-m))))

 (local
  (defthm signed-byte-p-30-occur-cnt-bounded-flg
    (case flg
      (term (implies (and (force (signed-byte-p 30 a))
                          (signed-byte-p 30 m)
                          (signed-byte-p 30 (+ bound-m m))
                          (force (<= 0 a))
                          (<= 0 m)
                          (<= 0 bound-m)
                          (<= a (+ bound-m m)))
                     (and (<= -1
                              (occur-cnt-bounded term1 term2 a m bound-m))
                          (<= (occur-cnt-bounded term1 term2 a m bound-m)
                              (+ bound-m m)))))
      (otherwise
       (implies (and (force (signed-byte-p 30 a))
                     (signed-byte-p 30 m)
                     (signed-byte-p 30 (+ bound-m m))
                     (force (<= 0 a))
                     (<= 0 m)
                     (<= 0 bound-m)
                     (<= a (+ bound-m m)))
                (and (<= -1
                         (occur-cnt-bounded-lst term1 lst a m bound-m))
                     (<= (occur-cnt-bounded-lst term1 lst a m bound-m)
                         (+ bound-m m))))))
    :rule-classes nil
    :hints
    (("Goal" :induct (occur-cnt-bounded-flg flg term2 term1 lst a m bound-m)))))
 (local
  (defthm signed-byte-p-30-occur-cnt-bounded-flg-term
    (implies (and (force (signed-byte-p 30 a))
                  (signed-byte-p 30 m)
                  (signed-byte-p 30 (+ bound-m m))
                  (force (<= 0 a))
                  (<= 0 m)
                  (<= 0 bound-m)
                  (<= a (+ bound-m m)))
             (and (<= -1
                      (occur-cnt-bounded term1 term2 a m bound-m))
                  (<= (occur-cnt-bounded term1 term2 a m bound-m)
                      (+ bound-m m))))
    :rule-classes :linear
    :hints (("Goal" ; :in-theory (theory 'minimal-theory)
             :use ((:instance signed-byte-p-30-occur-cnt-bounded-flg
                              (flg 'term)))))))
 (local
  (defthm signed-byte-p-30-occur-cnt-bounded-flg-list
    (implies (and (force (signed-byte-p 30 a))
                  (signed-byte-p 30 m)
                  (signed-byte-p 30 (+ bound-m m))
                  (force (<= 0 a))
                  (<= 0 m)
                  (<= 0 bound-m)
                  (<= a (+ bound-m m)))
             (and (<= -1
                      (occur-cnt-bounded-lst term1 lst a m bound-m))
                  (<= (occur-cnt-bounded-lst term1 lst a m bound-m)
                      (+ bound-m m))))
    :rule-classes :linear
    :hints (("Goal" ; :in-theory (theory 'minimal-theory)
             :use ((:instance signed-byte-p-30-occur-cnt-bounded-flg
                              (flg 'list)))))))

 (verify-guards occur-cnt-bounded)

 (verify-termination-boot-strap too-many-ifs1) ; and guards

 (verify-termination-boot-strap too-many-ifs-post-rewrite-builtin) ; and guards

 )

(defattach too-many-ifs-post-rewrite too-many-ifs-post-rewrite-builtin)

; Complete too-many-ifs-pre-rewrite.

#+acl2-loop-only
; The above readtime conditional avoids a CLISP warning, and lets the defproxy
; for print-clause-id-okp provide the raw Lisp definition.
(encapsulate
  ((too-many-ifs-pre-rewrite (args counts) t
                             :guard
                             (and (pseudo-term-listp args)
                                  (integer-listp counts)
                                  (equal (len args) (len counts)))))
  (local (defun too-many-ifs-pre-rewrite (args counts)
           (list args counts))))

(defattach (too-many-ifs-pre-rewrite too-many-ifs-pre-rewrite-builtin))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachment: ancestors-check, worse-than, worse-than-or-equal
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination-boot-strap pseudo-variantp)

(verify-termination-boot-strap member-char-stringp)

(verify-termination-boot-strap terminal-substringp1)

(verify-termination-boot-strap terminal-substringp)

(verify-termination-boot-strap evg-occur)

(verify-termination-boot-strap min-fixnum)

(verify-termination-boot-strap fn-count-evg-rec ; but not guards
                               (declare (xargs :verify-guards nil)))

(defthm fn-count-evg-rec-type-prescription
  (implies (natp acc)
           (natp (fn-count-evg-rec evg acc calls)))
  :rule-classes :type-prescription)

(defthm fn-count-evg-rec-bound
  (< (fn-count-evg-rec evg acc calls)
     536870912) ; (expt 2 29)
  :rule-classes :linear)

(verify-guards fn-count-evg-rec)

(verify-termination-boot-strap occur)

(verify-termination-boot-strap worse-than-builtin-clocked) ; and mut-rec nest

(verify-termination-boot-strap worse-than-builtin)

(verify-termination-boot-strap worse-than-or-equal-builtin)

(verify-termination-boot-strap ancestor-listp)

(verify-termination-boot-strap earlier-ancestor-biggerp)

(verify-termination-boot-strap fn-count-1) ; but not guards

(defthm fn-count-1-type
  (implies (and (integerp fn-count-acc)
                (integerp p-fn-count-acc))
           (and (integerp (car (fn-count-1 flag term
                                           fn-count-acc p-fn-count-acc)))
                (integerp (mv-nth 0 (fn-count-1 flag term
                                                fn-count-acc
                                                p-fn-count-acc)))
                (integerp (mv-nth 1 (fn-count-1 flag term
                                                fn-count-acc
                                                p-fn-count-acc)))
                (integerp (nth 0 (fn-count-1 flag term
                                             fn-count-acc
                                             p-fn-count-acc)))
                (integerp (nth 1 (fn-count-1 flag term
                                             fn-count-acc
                                             p-fn-count-acc)))))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((fn-count-1 flag term fn-count-acc p-fn-count-acc)))))

(verify-guards fn-count-1)

(verify-termination-boot-strap var-fn-count-1) ; but not guards

(defthm symbol-listp-cdr-assoc-equal
  (implies (symbol-list-listp x)
           (symbol-listp (cdr (assoc-equal key x)))))

; We state the following three rules in all forms that we think might be useful
; to those who want to reason about var-fn-count-1, for example if they are
; developing attachments to ancestors-check.

(defthm integerp-nth-0-var-fn-count-1
  (implies (integerp var-count-acc)
           (integerp (nth 0 (var-fn-count-1
                             flg x
                             var-count-acc fn-count-acc p-fn-count-acc
                             invisible-fns invisible-fns-table))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((var-fn-count-1 flg x var-count-acc fn-count-acc
                     p-fn-count-acc invisible-fns
                     invisible-fns-table))
    :corollary
    (implies (integerp var-count-acc)
             (and (integerp (nth 0 (var-fn-count-1
                                    flg x
                                    var-count-acc fn-count-acc p-fn-count-acc
                                    invisible-fns invisible-fns-table)))
                  (integerp (mv-nth 0 (var-fn-count-1
                                       flg x
                                       var-count-acc fn-count-acc p-fn-count-acc
                                       invisible-fns invisible-fns-table)))
                  (integerp (car (var-fn-count-1
                                  flg x
                                  var-count-acc fn-count-acc p-fn-count-acc
                                  invisible-fns invisible-fns-table))))))))

(defthm integerp-nth-1-var-fn-count-1
  (implies (integerp fn-count-acc)
           (integerp (nth 1 (var-fn-count-1
                             flg x
                             var-count-acc fn-count-acc p-fn-count-acc
                             invisible-fns invisible-fns-table))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((var-fn-count-1 flg x var-count-acc fn-count-acc
                     p-fn-count-acc invisible-fns
                     invisible-fns-table))
    :corollary
    (implies (integerp fn-count-acc)
             (and (integerp (nth 1 (var-fn-count-1
                                       flg x
                                       var-count-acc fn-count-acc p-fn-count-acc
                                       invisible-fns invisible-fns-table)))
                  (integerp (mv-nth 1 (var-fn-count-1
                                       flg x
                                       var-count-acc fn-count-acc p-fn-count-acc
                                       invisible-fns invisible-fns-table))))))))

(defthm integerp-nth-2-var-fn-count-1
  (implies (integerp p-fn-count-acc)
           (integerp (nth 2 (var-fn-count-1
                             flg x
                             var-count-acc fn-count-acc p-fn-count-acc
                             invisible-fns invisible-fns-table))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((var-fn-count-1 flg x var-count-acc fn-count-acc
                     p-fn-count-acc invisible-fns
                     invisible-fns-table))
    :corollary
    (implies (integerp p-fn-count-acc)
             (and (integerp (nth 2 (var-fn-count-1
                                    flg x
                                    var-count-acc fn-count-acc p-fn-count-acc
                                    invisible-fns invisible-fns-table)))
                  (integerp (mv-nth 2 (var-fn-count-1
                                       flg x
                                       var-count-acc fn-count-acc p-fn-count-acc
                                       invisible-fns invisible-fns-table))))))))

(verify-guards var-fn-count-1)

(verify-termination-boot-strap equal-mod-commuting) ; and guards

(verify-termination-boot-strap ancestors-check1)

(verify-termination-boot-strap ancestors-check-builtin)

(defun member-equal-mod-commuting (x lst wrld)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp lst)
                              (plist-worldp wrld))))
  (cond ((endp lst) nil)
        ((equal-mod-commuting x (car lst) wrld) lst)
        (t (member-equal-mod-commuting x (cdr lst) wrld))))

; In the following, terms (nth 0 ...) and (nth 1 ...) in the hints were
; originally (car ...) and (mv-nth 1 ...), respectively, but those didn't
; work.  It would be good at some point to explore why not, given that the
; original versions worked outside the build.

(defun strip-ancestor-literals (ancestors)
  (declare (xargs :guard (ancestor-listp ancestors)))
  (cond ((endp ancestors) nil)
        (t (cons (access ancestor (car ancestors) :lit)
                 (strip-ancestor-literals (cdr ancestors))))))

(encapsulate
 ()

 (local
  (defthm ancestors-check1-property
    (mv-let (on-ancestors assumed-true)
            (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt ancestors
                              tokens)
            (implies (and on-ancestors
                          assumed-true)
                     (member-equal-mod-commuting
                      lit
                      (strip-ancestor-literals ancestors)
                      nil)))
    :rule-classes nil))

 (defthmd ancestors-check-builtin-property
   (mv-let (on-ancestors assumed-true)
           (ancestors-check-builtin lit ancestors tokens)
           (implies (and on-ancestors
                         assumed-true)
                    (member-equal-mod-commuting
                     lit
                     (strip-ancestor-literals ancestors)
                     nil)))
   :hints (("Goal"
            :use
            ((:instance
              ancestors-check1-property
              (lit-atm lit)
              (var-cnt 0)
              (fn-cnt 0)
              (p-fn-cnt 0))
             (:instance
              ancestors-check1-property
              (lit-atm lit)
              (var-cnt (nth 0 (var-fn-count-1 nil lit 0 0 0 nil nil)))
              (fn-cnt (nth 1 (var-fn-count-1 nil lit 0 0 0 nil nil)))
              (p-fn-cnt (nth 2 (var-fn-count-1 nil lit 0 0 0 nil nil))))
             (:instance
              ancestors-check1-property
              (lit-atm (cadr lit))
              (var-cnt (nth 0 (var-fn-count-1 nil (cadr lit) 0 0 0 nil nil)))
              (fn-cnt (nth 1 (var-fn-count-1 nil (cadr lit) 0 0 0 nil nil)))
              (p-fn-cnt (nth 2
                             (var-fn-count-1 nil (cadr lit) 0 0 0
                                             nil nil)))))))))

#+acl2-loop-only
; The above readtime conditional avoids a CLISP warning, and lets the defproxy
; for print-clause-id-okp provide the raw Lisp definition.
(encapsulate
 ((ancestors-check (lit ancestors tokens) (mv t t)
                   :guard (and (pseudo-termp lit)
                               (ancestor-listp ancestors)
                               (true-listp tokens))))

 (local (defun ancestors-check (lit ancestors tokens)
          (ancestors-check-builtin lit ancestors tokens)))

 (defthmd ancestors-check-constraint
   (implies (and (pseudo-termp lit)
                 (ancestor-listp ancestors)
                 (true-listp tokens))
            (mv-let (on-ancestors assumed-true)
                    (ancestors-check lit ancestors tokens)
                    (implies (and on-ancestors
                                  assumed-true)
                             (member-equal-mod-commuting
                              lit
                              (strip-ancestor-literals ancestors)
                              nil))))
   :hints (("Goal" :use ancestors-check-builtin-property))))

(defattach (ancestors-check ancestors-check-builtin)
  :hints (("Goal" :by ancestors-check-builtin-property)))

(defattach worse-than worse-than-builtin)

(defattach worse-than-or-equal worse-than-or-equal-builtin)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachment: acl2x-expansion-alist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination-boot-strap hons-copy-with-state) ; and guards

(verify-termination-boot-strap identity-with-state) ; and guards

(defattach (acl2x-expansion-alist
; User-modifiable; see comment in the defstub introducing
; acl2x-expansion-alist.
            identity-with-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachments: rw-cache utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination-boot-strap rw-cache-debug-builtin) ; and guards

(defattach rw-cache-debug rw-cache-debug-builtin)

(verify-termination-boot-strap rw-cache-debug-action-builtin) ; and guards

(defattach rw-cache-debug-action rw-cache-debug-action-builtin)

(verify-termination-boot-strap rw-cacheable-failure-reason-builtin) ; and guards

(defattach rw-cacheable-failure-reason rw-cacheable-failure-reason-builtin)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachments: print-clause-id-okp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination-boot-strap all-digits-p) ; and guards

(verify-termination-boot-strap ; and guards
 (d-pos-listp
  (declare
   (xargs
    :guard-hints
    (("Goal"
      :use ((:instance coerce-inverse-2
                       (x (symbol-name (car lst))))
            (:instance character-listp-coerce
                       (str (symbol-name (car lst)))))
      :expand ((len (coerce (symbol-name (car lst)) 'list)))
      :in-theory (disable coerce-inverse-2
                          character-listp-coerce)))))))

(verify-termination-boot-strap pos-listp)
(verify-guards pos-listp)

(defthm d-pos-listp-forward-to-true-listp
  (implies (d-pos-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(verify-termination-boot-strap clause-id-p) ; and guards

#+acl2-loop-only
; The above readtime conditional avoids a CLISP warning, and lets the defproxy
; for print-clause-id-okp provide the raw Lisp definition.
(encapsulate
 (((print-clause-id-okp *) => * :formals (cl-id) :guard (clause-id-p cl-id)))
 (local (defun print-clause-id-okp (x)
          x)))

(verify-termination-boot-strap print-clause-id-okp-builtin) ; and guards

(defattach print-clause-id-okp print-clause-id-okp-builtin)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachments: oncep-tp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We could avoid the forms below by replacing the earlier forms
;   (defproxy oncep-tp (* *) => *)
;   (defun oncep-tp-builtin ...) ; :guard t
;   (defattach (oncep-tp oncep-tp-builtin) :skip-checks t)
; in place, by changing defproxy to defstub and removing :skip-checks t.
; However, the guard on once-tp would then be left with a guard of t, which
; might be stronger than we'd like.

#+acl2-loop-only
; The above readtime conditional avoids a CLISP warning, and lets the defproxy
; for print-clause-id-okp provide the raw Lisp definition.
(encapsulate
 (((oncep-tp * *) => *
   :formals (rune wrld)
   :guard (and (plist-worldp wrld)

; Although (runep rune wrld) is appropriate here, we don't want to fight the
; battle yet of putting runep into :logic mode.  So we just lay down the
; syntactic part of its code, which should suffice for user-defined attachments
; to oncep-tp.

               (and (consp rune)
                    (consp (cdr rune))
                    (symbolp (cadr rune))))))
 (logic)
 (local (defun oncep-tp (rune wrld)
          (oncep-tp-builtin rune wrld))))

(defattach oncep-tp oncep-tp-builtin)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; verify-termination and guard verification:
; string-for-tilde-@-clause-id-phrase and some subsidiary functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; David Rager proved termination and guards for
; string-for-tilde-@-clause-id-phrase, with a proof that included community
; books unicode/explode-atom and unicode/explode-nonnegative-integer.  Here, we
; rework that proof a bit to avoid those dependencies.  Note that this proof
; depends on d-pos-listp, whose termination and guard verification are
; performed above.

; We proved true-listp-explode-nonnegative-integer here, but then found it was
; already proved locally in axioms.lisp.  So we made that defthm non-local (and
; strengthened it to its current form).

(verify-termination-boot-strap chars-for-tilde-@-clause-id-phrase/periods)

(verify-termination-boot-strap chars-for-tilde-@-clause-id-phrase/primes)

(defthm pos-listp-forward-to-integer-listp
  (implies (pos-listp x)
           (integer-listp x))
  :rule-classes :forward-chaining)

(verify-termination-boot-strap chars-for-tilde-@-clause-id-phrase)

(defthm true-listp-chars-for-tilde-@-clause-id-phrase/periods
  (true-listp (chars-for-tilde-@-clause-id-phrase/periods lst))
  :rule-classes :type-prescription)

(defthm true-listp-explode-atom
  (true-listp (explode-atom n print-base))
  :rule-classes :type-prescription)

(encapsulate
 ()

; The following local events create perfectly good rewrite rules, but we avoid
; the possibility of namespace clashes for existing books by making them local
; as we add them after Version_4.3.

 (local
  (defthm character-listp-explode-nonnegative-integer
    (implies
     (character-listp ans)
     (character-listp (explode-nonnegative-integer n print-base ans)))))

 (local
  (defthm character-listp-explode-atom
    (character-listp (explode-atom n print-base))
    :hints ; need to disable this local lemma from axioms.lisp
    (("Goal" :in-theory (disable character-listp-cdr)))))

 (local
  (defthm character-listp-chars-for-tilde-@-clause-id-phrase/periods
    (character-listp (chars-for-tilde-@-clause-id-phrase/periods lst))))

 (verify-termination-boot-strap string-for-tilde-@-clause-id-phrase))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; verify-termination and guard verification:
; strict-merge-symbol-<, strict-merge-sort-symbol-<, strict-symbol-<-sortedp,
; and sort-symbol-listp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination-boot-strap strict-merge-symbol-<
                               (declare (xargs :measure
                                               (+ (len l1) (len l2)))))

(encapsulate
 ()

 (local
  (defthm len-strict-merge-symbol-<
    (<= (len (strict-merge-symbol-< l1 l2 acc))
        (+ (len l1) (len l2) (len acc)))
    :rule-classes :linear))

 (local
  (defthm len-evens
    (equal (len l)
           (+ (len (evens l))
              (len (odds l))))
    :rule-classes :linear))

 (local
  (defthm symbol-listp-evens
    (implies (symbol-listp x)
             (symbol-listp (evens x)))
    :hints (("Goal" :induct (evens x)))))

 (local
  (defthm symbol-listp-odds
    (implies (symbol-listp x)
             (symbol-listp (odds x)))))

 (local
  (defthm symbol-listp-strict-merge-symbol-<
    (implies (and (symbol-listp l1)
                  (symbol-listp l2)
                  (symbol-listp acc))
             (symbol-listp (strict-merge-symbol-< l1 l2 acc)))))

 (verify-termination-boot-strap strict-merge-sort-symbol-<
                                (declare (xargs :measure (len l)
                                                :verify-guards nil)))

 (defthm symbol-listp-strict-merge-sort-symbol-<
; This lemma is non-local because it is needed for "make proofs", for
; guard-verification for new-verify-guards-fns1.
   (implies (symbol-listp x)
            (symbol-listp (strict-merge-sort-symbol-< x))))

 (verify-guards strict-merge-sort-symbol-<)

 (verify-termination-boot-strap strict-symbol-<-sortedp) ; and guards

 (verify-termination-boot-strap sort-symbol-listp) ; and guards

 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Theories
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory definition-minimal-theory
  (definition-runes
    *definition-minimal-theory*
    nil
    world))

(deftheory executable-counterpart-minimal-theory
  (definition-runes
    *built-in-executable-counterparts*
    t
    world))

(deftheory minimal-theory

; Warning: The resulting value must be a runic-theoryp.  See
; theory-fn-callp.

; Keep this definition in sync with translate-in-theory-hint.

  (union-theories (theory 'definition-minimal-theory)
                  (union-theories

; Without the :executable-counterpart of force, the use of (theory
; 'minimal-theory) will produce the warning "Forcing has transitioned
; from enabled to disabled", at least if forcing is enabled (as is the
; default).

                   '((:executable-counterpart force))
                   (theory 'executable-counterpart-minimal-theory))))

; See the Essay on the Status of the Tau System During and After Bootstrapping
; in axioms.lisp where we discuss choices (1.a), (1.b), (2.a) and (2.b)
; related to the status of the tau system.  Here is where we implement
; (2.a).

(in-theory (if (cadr *tau-status-boot-strap-settings*)          ; (2.a)
               (enable (:executable-counterpart tau-system))
               (disable (:executable-counterpart tau-system))))

(deftheory ground-zero

; WARNING: Keep this near the end of *acl2-pass-2-files* in order for
; the ground-zero theory to be as expected.

  (current-theory :here))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; meta-extract support
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination-boot-strap formals) ; and guards
(verify-termination-boot-strap constraint-info) ; and guards

(defund meta-extract-formula (name state)

; This function supports meta-extract-global-fact+.  It needs to be executable
; and in :logic mode (hence, as required by the ACL2 build process,
; guard-verified), since it may be called by meta functions.

; While this function can be viewed as a version of formula, it applies only to
; symbols (not runes), it is in :logic mode, and there are a few other
; differences as well.  The present function requires name to be a symbol and
; only returns a normalp=nil form of body.  (Otherwise, in order to put body in
; :logic mode, body would need to be guard-verified, which would probably take
; considerable effort.)

  (declare (xargs :stobjs state
                  :guard (symbolp name)))
  (let ((wrld (w state)))
    (or (getpropc name 'theorem nil wrld)
        (mv-let (flg prop)
                (constraint-info name wrld)
                (cond ((eq prop *unknown-constraints*)
                       *t*)
                      (flg (ec-call (conjoin prop)))
                      (t prop))))))

(verify-termination-boot-strap type-set-quote)
(verify-guards type-set-quote)

(defun typespec-check (ts x)
  (declare (xargs :guard (integerp ts)))
  (if (bad-atom x)
      (< ts 0) ; bad-atom type intersects every complement type

; We would like to write
;   (ts-subsetp (type-set-quote x) ts)
; here, but for that we need a stronger guard than (integerp ts), and we prefer
; to keep this simple.

    (not (eql 0 (logand (type-set-quote x) ts)))))

(defun meta-extract-rw+-term (term alist equiv rhs state)

; This function supports the function meta-extract-contextual-fact.  Neither of
; these functions is intended to be executed.

; Meta-extract-rw+-term creates (logically) a term claiming that term under
; alist is equiv to rhs, where equiv=nil represents 'equal and equiv=t
; represents 'iff.  If equiv is not t, nil, or an equivalence relation, then
; *t* is returned.

; Note that this function does not support the use of a geneqv for the equiv
; argument.

  (declare (xargs :mode :program ; becomes :logic with system-verify-guards
                  :stobjs state
                  :guard (and (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist))
                              (pseudo-termp term))))
  (non-exec
   (let ((lhs (sublis-var alist term)))
     (case equiv
       ((nil) `(equal ,lhs ,rhs))
       ((t)   `(iff ,lhs ,rhs))
       (otherwise
        (if (symbolp equiv)
            (if (equivalence-relationp equiv (w state))
                `(,equiv ,lhs ,rhs)
; else bad equivalence relation
              *t*)
          *t*))))))

(defun meta-extract-contextual-fact (obj mfc state)

; This function is not intended to be executed.

; This function may be called in the hypothesis of a meta rule, because we know
; it always produces a term that evaluates to non-nil under the mfc where the
; metafunction is called, using the specific alist A for which we're proving
; (evl x a) = (evl (metafn x) a).  The terms it produces reflect the
; correctness of certain prover operations -- currently, accessing type-alist
; and typeset information, rewriting, and linear arithmetic.  See the Essay on
; Correctness of Meta Reasoning.  Note that these operations use the state for
; heuristic purposes, and get their logical information from the world stored
; in mfc (not in state).

; This function avoids forcing and does not return a tag-tree.

  (declare (xargs :mode :program ; becomes :logic with system-verify-guards
                  :stobjs state))
  (non-exec
   (case-match obj
     ((':typeset term . &) ; mfc-ts produces correct results
      `(typespec-check
        ',(mfc-ts term mfc state :forcep nil :ttreep nil)
        ,term))
     ((':rw+ term alist obj equiv . &) ; result is equiv to term/alist.
      (meta-extract-rw+-term term alist equiv
                             (mfc-rw+ term alist obj equiv mfc state
                                      :forcep nil :ttreep nil)
                             state))
     ((':rw term obj equiv . &) ; as for :rw+, with alist of nil
      (meta-extract-rw+-term term nil equiv
                             (mfc-rw term obj equiv mfc state
                                     :forcep nil :ttreep nil)
                             state))
     ((':ap term . &) ; Can linear arithmetic can falsify term?
      (if (mfc-ap term mfc state :forcep nil)
          `(not ,term)
        *t*))
     ((':relieve-hyp hyp alist rune target bkptr . &) ; hyp/alist proved?
      (if (mfc-relieve-hyp hyp alist rune target bkptr mfc state
                           :forcep nil :ttreep nil)
          (sublis-var alist hyp)
        *t*))
     (& *t*))))

(defun rewrite-rule-term (x)

; This function is not intended to be executed.  It turns a rewrite-rule record
; into a term.

  (declare (xargs :guard t))
  (non-exec
   (if (eq (access rewrite-rule x :subclass) 'meta)
       *t*
     `(implies ,(conjoin (access rewrite-rule x :hyps))
               (,(access rewrite-rule x :equiv)
                ,(access rewrite-rule x :lhs)
                ,(access rewrite-rule x :rhs))))))

(defmacro meta-extract-global-fact (obj state)
; See meta-extract-global-fact+.
   `(meta-extract-global-fact+ ,obj ,state ,state))

(defun fncall-term (fn arglist state)
  (declare (xargs :stobjs state
                  :guard (true-listp arglist)))
  (mv-let (erp val)
          (magic-ev-fncall fn arglist state
                           t   ; hard-error-returns-nilp
                           nil ; aok
                           )
          (cond (erp *t*)
                (t (fcons-term* 'equal

; As suggested by Sol Swords, we use fcons-term below in order to avoid having
; to reason about the application of an evaluator to (cons-term fn ...).

                                (fcons-term fn (kwote-lst arglist))
                                (kwote val))))))

(defun logically-equivalent-states (st1 st2)
   (declare (xargs :guard t))
   (non-exec (equal (w st1) (w st2))))

(defun meta-extract-global-fact+ (obj st state)

; This function is not intended to be executed.

; This function may be called in the hypothesis of a meta rule, because we know
; it always produces a term that evaluates to non-nil for any alist.  The terms
; it produces reflect the correctness of certain facts stored in the world.
; See the Essay on Correctness of Meta Reasoning.

  (declare (xargs :mode :program ; becomes :logic with system-verify-guards
                  :stobjs state))
  (non-exec
   (cond
    ((logically-equivalent-states st state)
     (case-match obj
       ((':formula name)
        (meta-extract-formula name st))
       ((':lemma fn n)
        (let* ((lemmas (getpropc fn 'lemmas nil (w st)))
               (rule (nth n lemmas)))

; The use of rewrite-rule-term below relies on the fact that the 'LEMMAS
; property of a symbol in the ACL2 world is a list of rewrite-rule records that
; reflect known facts.

          (if (< (nfix n) (len lemmas))
              (rewrite-rule-term rule)
            *t*))) ; Fn doesn't exist or n is too big.
       ((':fncall fn arglist)
        (non-exec ; avoid guard check
         (fncall-term fn arglist st)))
       (& *t*)))
    (t *t*))))

(add-macro-alias meta-extract-global-fact meta-extract-global-fact+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Support for system-verify-guards
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section supports a mechanism for users to extend the set of
; guard-verified functions.  They do so in community books under books/system/,
; which are checked when building with feature :acl2-devel, for example
; building with `make' with ACL2_DEVEL=d.  But normal builds will not set that
; feature, and will simply trust that functions marked in
; *system-verify-guards-alist* can be guard-verified.

; The following commands will check that things are as they should be, after
; adjusting *system-verify-guards-alist* (see comments there).  Altogether they
; took only about two minutes on a fast machine in May 2015.

;   (time nice make ACL2_DEVEL=d)
;   cd books
;   make clean ACL2=`pwd`/../saved_acl2d
;   time ./build/cert.pl -j 8 --acl2 `pwd`/../saved_acl2d system/top.cert
;   cd ..
;   (time nice make -j 8 devel-check ACL2=`pwd`/saved_acl2d)

; For details, see the comment just above the call of system-verify-guards near
; the end of this section.

; A flaw in our approach is that user-supplied guard verifications may depend
; on package axioms.  Thus, we view such verifications as strong hints, rather
; than as ironclad guarantees that the functions can be guard-verified in
; definitional (or even conservative) extensions of the ground-zero theory.  We
; consider this sufficient, as the event that some package axiom will cause
; such bogus marking as guard-verified seems much less likely than the event
; that our system has other serious bugs!

(verify-termination-boot-strap safe-access-command-tuple-form) ; and guards

(defun pair-fns-with-measured-subsets (fns wrld acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld)
                              (true-listp acc))))
  (cond ((endp fns) (reverse acc))
        (t (pair-fns-with-measured-subsets
            (cdr fns)
            wrld
            (cons (let* ((fn (car fns))
                         (justification (getpropc fn 'justification nil wrld))
                         (ms (and (consp justification) ; for guard
                                  (consp (cdr justification)) ; for guard
                                  (access justification justification :subset))))
                    (cons fn ms))
                  acc)))))

(defun new-verify-guards-fns1 (wrld installed-wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (plist-worldp installed-wrld)
                              (symbol-listp acc))))
  (cond ((or (endp wrld)
             (and (eq (caar wrld) 'command-landmark)
                  (eq (cadar wrld) 'global-value)
                  (equal (safe-access-command-tuple-form (cddar wrld))
                         '(exit-boot-strap-mode))))
         (pair-fns-with-measured-subsets
          (strict-merge-sort-symbol-< acc)
          installed-wrld
          nil))
        ((and (eq (cadar wrld) 'symbol-class)
              (eq (cddar wrld) :COMMON-LISP-COMPLIANT)
              (getpropc (caar wrld) 'predefined nil installed-wrld))
         (new-verify-guards-fns1 (cdr wrld)
                                 installed-wrld
                                 (cons (caar wrld) acc)))
        (t (new-verify-guards-fns1 (cdr wrld) installed-wrld acc))))

(defun new-verify-guards-fns (state)

; It is important for performance that this function be guard-verified, because
; it is called inside an assert-event form in chk-new-verified-guards, which
; causes evaluation to be in safe-mode and would cause evaluation of
; plist-worldp on behalf of guard-checking for new-verify-guards-fns1.

  (declare (xargs :stobjs state))
  (let ((wrld (w state)))
    (new-verify-guards-fns1 wrld wrld nil)))

(defconst *system-verify-guards-alist*

; Each cdr was produced by evaluating
; (new-verify-guards-fns state)
; after including the book indicated in the car in a build with feature
; :acl2-devel set (see discussion in the comment at the top of this section).
; For example, cdr of the entry for "system/top" is produced by evaluating:
; (include-book "system/top" :dir :system).
; The indicated books need to be certified using an ACL2 executable that was
; built with feature :acl2-devel set, but this takes about 2.5 minutes on a
; fast machine in Feb. 2013, as follows:

; make -j 8 regression ACL2_BOOK_DIRS=system ACL2=<:acl2-devel version>

; Each member of each cdr below is of the form (fn . measured-subset).

; Note that it is not necessary to do a full regression with an :acl2-devel
; executable; only the books in the keys of this alist need to be certified.

  '(("system/top"
     (>=-LEN X)
     (ALIST-TO-DOUBLETS ALIST)
     (ALL->=-LEN LST)
     (ARGLISTP)
     (ARGLISTP1 LST)
     (ARITIES-OKP USER-TABLE)
     (ARITY)
     (COLLECT-BY-POSITION FULL-DOMAIN)
     (CONS-TERM1-MV2)
     (DUMB-NEGATE-LIT)
     (FETCH-DCL-FIELD)
     (FETCH-DCL-FIELDS LST)
     (FETCH-DCL-FIELDS1 LST)
     (FETCH-DCL-FIELDS2 KWD-LIST)
     (FIND-DOT-DOT I FULL-PATHNAME)
     (FIND-FIRST-BAD-ARG ARGS)
     (LAMBDA-KEYWORDP)
     (LEGAL-CONSTANTP1)
     (LEGAL-VARIABLE-OR-CONSTANT-NAMEP)
     (LEGAL-VARIABLEP)
     (MAKE-LAMBDA-APPLICATION)
     (MERGE-SORT-TERM-ORDER L)
     (MERGE-TERM-ORDER L2 L1)
     (META-EXTRACT-CONTEXTUAL-FACT)
     (META-EXTRACT-GLOBAL-FACT+)
     (META-EXTRACT-RW+-TERM)
     (PLAUSIBLE-DCLSP LST)
     (PLAUSIBLE-DCLSP1 LST)
     (PLIST-WORLDP-WITH-FORMALS ALIST)
     (STRIP-CADRS X)
     (STRIP-DCLS LST)
     (STRIP-DCLS1 LST)
     (STRIP-KEYWORD-LIST LST)
     (SUBCOR-VAR FORM)
     (SUBCOR-VAR-LST FORMS)
     (SUBCOR-VAR1 VARS)
     (SUBLIS-VAR)
     (SUBLIS-VAR-LST)
     (SUBLIS-VAR1 FORM)
     (SUBLIS-VAR1-LST L)
     (SUBST-EXPR)
     (SUBST-EXPR-ERROR)
     (SUBST-EXPR1 TERM)
     (SUBST-EXPR1-LST ARGS)
     (SUBST-VAR FORM)
     (SUBST-VAR-LST L)
     (TERM-LIST-LISTP L)
     (TERM-LISTP X)
     (TERM-ORDER)
     (TERM-ORDER1)
     (TERMP X))))

(defconst *len-system-verify-guards-alist*
  (length *system-verify-guards-alist*))

(defmacro chk-new-verified-guards (n)
  (cond
   ((or (not (natp n))
        (> n *len-system-verify-guards-alist*))
    `(er soft 'chk-new-verified-guards
         "The index ~x0 is not a valid index for *system-verify-guards-alist*."
         ',n))
   ((eql n *len-system-verify-guards-alist*)
    '(value-triple :CHK-NEW-VERIFIED-GUARDS-COMPLETE))
   (t
    (let* ((pair (nth n *system-verify-guards-alist*))
           (user-book-name (car pair))
           (fns (cdr pair)))
      `(progn (include-book ,user-book-name
                            :DIR :SYSTEM
                            :UNCERTIFIED-OKP nil
                            :DEFAXIOMS-OKP nil
                            :SKIP-PROOFS-OKP nil
                            :TTAGS nil)
              (assert-event
               (equal ',fns
                      (new-verify-guards-fns state))
               :msg (msg "ERROR: The set of newly guard-verified functions ~
                          from the ACL2 community book ~x0 does not match the ~
                          expected set from the constant ~
                          *system-verify-guards-alist*.~|~%From the ~
                          book:~|~X13~|~%Expected from ~
                          *system-verify-guards-alist*:~|~X23~|"
                         ',user-book-name
                         (new-verify-guards-fns state)
                         ',fns
                         nil))
              (value-triple :CHK-NEW-VERIFIED-GUARDS-SUCCESS))))))

(defun system-verify-guards-fn-1 (fns-alist acc)
  (declare (xargs :guard (symbol-alistp fns-alist)))
  (cond ((endp fns-alist) acc)
        (t (system-verify-guards-fn-1
            (cdr fns-alist)
            (cons `(skip-proofs (verify-termination-boot-strap ; and guards
                                 ,(caar fns-alist)
                                 ,@(let ((ms (cdar fns-alist)))
                                     (and ms
                                          `((declare (xargs :measure
                                                            (:? ,@ms))))))))
                  acc)))))

(defun cons-absolute-event-numbers (fns-alist wrld acc)
  (declare (xargs :guard (and (symbol-alistp fns-alist)
                              (plist-worldp wrld)
                              (alistp acc))))
  (cond ((endp fns-alist) acc)
        (t (cons-absolute-event-numbers
            (cdr fns-alist)
            wrld
            (acons (or (getpropc (caar fns-alist) 'absolute-event-number nil
                                 wrld)
                       (er hard? 'cons-absolute-event-numbers
                           "The 'absolute-event-number property is missing ~
                            for ~x0."
                           (caar fns-alist)))
                   (car fns-alist)
                   acc)))))

(defun sort->-absolute-event-number (fns-alist wrld)
  (declare (xargs :mode :program)) ; because of merge-sort-car->
  (strip-cdrs (merge-sort-car->
               (cons-absolute-event-numbers fns-alist wrld nil))))

(defun system-verify-guards-fn (alist wrld acc)
  (declare (xargs :mode :program)) ; because of sort->-absolute-event-number
  (cond ((endp alist) acc)
        (t (system-verify-guards-fn
            (cdr alist)
            wrld
            (system-verify-guards-fn-1
             (sort->-absolute-event-number (cdar alist) wrld)
             acc)))))

(defmacro system-verify-guards ()
  `(make-event
    (let ((events (system-verify-guards-fn *system-verify-guards-alist*
                                           (w state)
                                           nil)))
      (list* 'encapsulate
             ()
             '(set-verify-guards-eagerness 2)
             events))))

; Normally we go ahead and trust *system-verify-guards-alist*, installing
; guard-verified functions with the following form.  But when feature
; :acl2-devel is set, then we do not do so, as we instead intend to run
; (chk-new-verified-guards i) for each i less than the length of
; *system-verify-guards-alist*, in order to check that the effect of
; system-verify-guards is sound.  This check is performed by using `make' with
; target devel-check, as shown near the top of this section.

#+(and acl2-loop-only ; Note that make-event can't be called here in raw Lisp.
       (not acl2-devel))
(system-verify-guards)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Support for system-events
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro system-event (event &optional (book-name '"system/top"))

; (System-event E) expands to (skip-proofs E) during normal builds.  However,
; for acl2-devel builds (see discussion under the section "Support for
; system-verify-guards" in boot-strap-pass-2.lisp), we merely add the event to
; a table, to be checked by Make target devel-check, which invokes function
; system-verify-skip-proofs for that purpose.

  #+acl2-devel `(table system-event-table ',event ',book-name)

; It is tempting to generate a progn, where the skip-proofs is preceded by:

; (value-triple ,(concatenate 'string "Verified in community book " book-name))

; However, that value-triple event doesn't show up with any of :pe, :pcb, or
; :pcb!, so we won't bother.

  #-acl2-devel (declare (ignore book-name))
  #-acl2-devel `(skip-proofs ,event))

(defun system-events-fn (events book-name)
  (declare (xargs :guard (true-listp events)))
  (cond ((endp events) nil)
        (t (cons `(system-event ,(car events) ,book-name)
                 (system-events-fn (cdr events) book-name)))))

(defmacro system-events (book-name &rest events)
  (declare (xargs :guard (stringp book-name)))
  (cons 'progn (system-events-fn events book-name)))

(defun system-include-book-forms (book-names)
  (declare (xargs :guard (true-listp book-names)))
  (cond ((endp book-names) nil)
        (t (cons `(include-book ,(car book-names) :dir :system)
                 (system-include-book-forms (cdr book-names))))))

(defmacro check-system-events ()

; Executed by "make devel-check".

  `(make-event
    (let ((event-book-alist (table-alist 'system-event-table (w state))))
      (cons 'progn
            (append (system-include-book-forms
                     (remove-duplicates (strip-cdrs event-book-alist)
                                        :test 'equal))
                    '((set-enforce-redundancy t))
                    (strip-cars event-book-alist)
                    '((value-triple :CHECK-SYSTEM-EVENTS-SUCCESS)))))))

(system-events "system/termp"

(defthm legal-variable-or-constant-namep-implies-symbolp
  (implies (not (symbolp x))
           (not (legal-variable-or-constant-namep x))))

(in-theory (disable legal-variable-or-constant-namep))

(defthm termp-implies-pseudo-termp
  (implies (termp x w)
           (pseudo-termp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm term-listp-implies-pseudo-term-listp
  (implies (term-listp x w)
           (pseudo-term-listp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm arities-okp-implies-arity
  (implies (and (arities-okp user-table w)
                (assoc fn user-table))
           (equal (arity fn w) (cdr (assoc fn user-table)))))

(in-theory (disable arity arities-okp))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Memoization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+(and hons acl2-loop-only)
(progn

; We skip raw Lisp functions here; see *thread-unsafe-builtin-memoizations*.

  (memoize 'fchecksum-obj :stats nil :forget t)
  (memoize 'expansion-alist-pkg-names-memoize :stats nil :forget t)

; Comment on memoizing a worse-than function:

; In Version_7.0 and several preceding versions, we memoized a "worse-than"
; function as follows.

; (memoize 'worse-than-builtin-memoized :stats nil)

; We now use a clocked version of worse-than and avoid such memoization.  See
; worse-than-builtin-clocked for comments about potential memoization.
; To restore such memoization, search for every occurrence of
; "Comment on memoizing a worse-than function".

; Below, we discuss some earlier experiments on memoizing worse-than-builtin or
; the like, on two particular community books:

; - books/coi/dtrees/base.lisp does not benefit from memoization of worse-than
;   functions, and can be slowed down by it.

; - books/centaur/esim/stv/stv2c/stv2c.lisp requires memoization of
;   worse-than-builtin (or the like) to avoid stalling out in a proof.

; Below we look at some results for the first of these books, using Version_7.0
; except (where indicated below) a development version that was close to
; Version_7.0.

; Except where indicated otherwise, we memoized worse-than-builtin for
; experiments below as follows.

; (memoize 'worse-than-builtin
;          :stats nil
;          :condition ; Sol Swords suggestion
;          '(and (nvariablep term1)
;                (not (fquotep term1))
;                (nvariablep term2)
;                (not (fquotep term2))))

; Specifically, we ran the following commands in the above book's directory.

;   (ld "cert.acl2")
;   (rebuild "base.lisp" t)
;   (in-package "DTREE")
;   (ubt! 'aux-domain-of-dtreemapfix)
;   (skip-proofs (defthm lemma
;                  (implies (set::in a (aux-domain (dtreemapfix map)))
;                           (set::in a (aux-domain map)))))

; In some cases we also ran the following command or the following two commands
; after the commands above but before evaluating the defthm shown below:

;   (acl2::unmemoize 'acl2::worse-than-builtin)
;   #!acl2(memoize 'worse-than-builtin
;            :stats nil
;            :forget t
;            :condition ; Sol Swords suggestion
;            '(and (nvariablep term1)
;                 (not (fquotep term1))
;                  (nvariablep term2)
;                  (not (fquotep term2))))

; Then we submitted the following event.

;   (defthm lemma2-for-aux-domain-of-dtreemapfix
;     (implies (set::in a (aux-domain map))
;              (set::in a (aux-domain (dtreemapfix map)))))

; Times and memory use (last two reports from top) from some experiments are
; shown below.  The key is that all runs with worse-than unmemoized were
; significantly faster than all runs with worse-than memoized, regardless of
; various attempts to speed up that memoization.

; With GCL, out of the box:
; Time:  122.34 seconds (prove: 122.33, print: 0.01, other: 0.00)
; 11959 kaufmann  20   0 15.3g 2.8g  53m R  100  9.0   2:05.29 gcl-saved_acl2h
; 11959 kaufmann  20   0 15.3g 2.8g  53m S   21  9.0   2:05.92 gcl-saved_acl2h

; With GCL, after the above unmemoize form:
; Time:  78.72 seconds (prove: 78.72, print: 0.00, other: 0.00)
; 11934 kaufmann  20   0 13.2g 854m  53m R  100  2.7   1:18.68 gcl-saved_acl2h
; 11934 kaufmann  20   0 13.2g 854m  53m S   98  2.7   1:21.64 gcl-saved_acl2h

; With GCL, after the above sequence of unmemoize and memoize:
; Time:  94.45 seconds (prove: 94.44, print: 0.01, other: 0.00)
; 11995 kaufmann  20   0 13.8g 727m  53m R  100  2.3   1:35.62 gcl-saved_acl2h
; 11995 kaufmann  20   0 13.8g 727m  53m S   62  2.3   1:37.47 gcl-saved_acl2h

; With CCL, out of the box:
; Time:  131.46 seconds (prove: 131.42, print: 0.04, other: 0.00)
; 12044 kaufmann  20   0  512g 1.8g  17m S  100  5.6   2:10.31 lx86cl64
; 12044 kaufmann  20   0  512g 1.8g  17m S   81  5.6   2:12.73 lx86cl64

; With CCL, after the above unmemoize form:
; Time:  89.83 seconds (prove: 89.82, print: 0.00, other: 0.00)
; 12068 kaufmann  20   0  512g 1.3g  17m S   99  4.2   1:29.91 lx86cl64
; 12068 kaufmann  20   0  512g 1.4g  17m S   40  4.4   1:31.12 lx86cl64

; With CCL, after the above sequence of unmemoize and memoize:
; Time:  147.46 seconds (prove: 147.44, print: 0.02, other: 0.00)
; 12093 kaufmann  20   0  512g 804m  18m S  100  2.5   2:27.86 lx86cl64
; 12093 kaufmann  20   0  512g 1.0g  18m S   30  3.2   2:28.77 lx86cl64

; All of the above were run with EGC off (the default at the time).  Now we
; repeat some of the above tests, but after turning EGC on as follows.

; (acl2::value :q) (ccl::egc t) (acl2::lp)

; With CCL, out of the box:
; Time:  1439.72 seconds (prove: 1439.71, print: 0.01, other: 0.00)
; 12127 kaufmann  20   0  512g 3.0g  35m S  100  9.4  23:58.68 lx86cl64
; 12127 kaufmann  20   0  512g 3.0g  35m S   78  9.4  24:01.03 lx86cl64

; With CCL, after the above unmemoize form:
; Time:  87.27 seconds (prove: 87.26, print: 0.01, other: 0.00)
; 12362 kaufmann  20   0  512g 407m  35m S  100  1.3   1:25.72 lx86cl64
; 12362 kaufmann  20   0  512g 417m  35m S   93  1.3   1:28.51 lx86cl64

; With CCL, after the above sequence of unmemoize and memoize:
; Time:  135.92 seconds (prove: 135.90, print: 0.02, other: 0.00)
; 12384 kaufmann  20   0  512g 705m  36m S    0  2.2   2:17.39 lx86cl64
; 12384 kaufmann  20   0  512g 705m  36m S    0  2.2   2:17.40 lx86cl64

; As just above, but after redefining waterfall1 in raw Lisp so that its
; body is (prog2$ (clear-memoize-table 'worse-than-builtin) <old-body>)
; Time:  134.38 seconds (prove: 134.37, print: 0.02, other: 0.00)
; 12631 kaufmann  20   0  512g 691m  36m S   99  2.1   2:14.64 lx86cl64
; 12631 kaufmann  20   0  512g 698m  36m S   38  2.2   2:15.79 lx86cl64

; All of the above used ACL2 Version_7.0.  The tests below were run with a
; development copy as of 1/21/2015 (a mere 9 days after the release of 7.0).
; We continue to turn EGC on at the start, as above.

; With CCL, after the above sequence of unmemoize and memoize:
; Time:  135.80 seconds (prove: 135.79, print: 0.01, other: 0.00)
; 13018 kaufmann  20   0  512g 664m  36m S   99  2.1   2:15.91 lx86cl64
; 13018 kaufmann  20   0  512g 671m  36m S   42  2.1   2:17.16 lx86cl64

; With CCL executable built without start-sol-gc (now called
; set-gc-strategy-builtin-delay) and with EGC on, after the above sequence of
; unmemoize and memoize:
; Time:  136.47 seconds (prove: 136.45, print: 0.02, other: 0.00)
; 13049 kaufmann  20   0  512g  59m  36m S   99  0.2   2:14.93 lx86cl64
; 13049 kaufmann  20   0  512g  59m  36m S   96  0.2   2:17.81 lx86cl64

; With CCL executable built without start-sol-gc (now called
; set-gc-strategy-builtin-delay) and with EGC on, after the above unmemoize
; form:
; Time:  86.33 seconds (prove: 86.33, print: 0.01, other: 0.00)
; 13178 kaufmann  20   0  512g  58m  35m S  100  0.2   1:27.18 lx86cl64
; 13178 kaufmann  20   0  512g  58m  35m S   17  0.2   1:27.70 lx86cl64

; With CCL executable built without start-sol-gc (now called
; set-gc-strategy-builtin-delay) and with EGC on, out of the box except for
; redefining waterfall1 in raw Lisp so that its body is (prog2$
; (clear-memoize-table 'worse-than-builtin) <old-body>); notice that :forget
; remains nil.
; Time:  182.61 seconds (prove: 182.58, print: 0.02, other: 0.00)
; 13135 kaufmann  20   0  512g 137m  17m S  100  0.4   3:02.78 lx86cl64
; 13135 kaufmann  20   0  512g 137m  17m S   37  0.4   3:03.90 lx86cl64

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; End
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflabel

; WARNING: Put this at the end of the last file in
; *acl2-pass-2-files*.

  end-of-pass-2)
