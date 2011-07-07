; ACL2 Version 4.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

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
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachment: too-many-ifs-post-rewrite and too-many-ifs-pre-rewrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ((too-many-ifs-post-rewrite (args val) t
                             :guard (and (pseudo-term-listp args)
                                         (pseudo-termp val))))
 (local (defun too-many-ifs-post-rewrite (args val)
          (list args val))))

; The following events are derived from the original version of
; books/system/too-many-ifs.lisp.  But here we provide a proof that does not
; depend on books.  Our approach was to take the proof in the above book,
; eliminate the unnecessary use of an arithmetic book, expand away all uses of
; macros and make-events, avoid use of (theory 'minimal-theory) since that
; theory didn't yet exist (where these events were originally placed), and
; apply some additional hand-editing in order (for example) to remove hints
; depending on the tools/flag book.  We have left original events from the book
; as comments.

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

(verify-termination-boot-strap worse-than-builtin) ; and worse-than-or-equal-builtin

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

(encapsulate
 ()

 (local
  (defthm ancestors-check1-property
    (mv-let (on-ancestors assumed-true)
            (ancestors-check1 lit-atm lit fn-cnt p-fn-cnt ancestors tokens)
            (implies (and on-ancestors
                          assumed-true)
                     (member-equal-mod-commuting lit
                                                 (strip-cars ancestors)
                                                 nil)))
    :rule-classes nil))

 (defthmd ancestors-check-builtin-property
   (mv-let (on-ancestors assumed-true)
           (ancestors-check-builtin lit ancestors tokens)
           (implies (and on-ancestors
                         assumed-true)
                    (member-equal-mod-commuting lit
                                                (strip-cars ancestors)
                                                nil)))
   :hints (("Goal"
            :use
            ((:instance ancestors-check1-property
                        (lit-atm lit)
                        (fn-cnt 0)
                        (p-fn-cnt 0))
             (:instance ancestors-check1-property
                        (lit-atm lit)
                        (fn-cnt (nth 0 (fn-count-1 nil lit 0 0)))
                        (p-fn-cnt (nth 1 (fn-count-1 nil lit 0 0))))
             (:instance ancestors-check1-property
                        (lit-atm (cadr lit))
                        (fn-cnt (nth 0 (fn-count-1 nil (cadr lit) 0 0)))
                        (p-fn-cnt (nth 1
                                       (fn-count-1 nil (cadr lit) 0
                                                   0)))))))))

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
                              (strip-cars ancestors)
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

(defattach (acl2x-expansion-alist
; User-modifiable; see comment in the defstub introducing
; acl2x-expansion-alist.
            hons-copy-with-state))

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

(encapsulate
 (((print-clause-id-okp *) => * :formals (cl-id) :guard (clause-id-p cl-id)))
 (local (defun print-clause-id-okp (x)
          x)))

(verify-termination-boot-strap print-clause-id-okp-builtin) ; and guards

(defattach print-clause-id-okp print-clause-id-okp-builtin)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Attachments: oncep-tp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
;;; Attachments: waterfall-parallelism and waterfall-printin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ((waterfall-parallelism () t))
 (local (defun waterfall-parallelism () nil))
 (defthm waterfall-parallelism-constraint
   (member-eq (waterfall-parallelism)
              *waterfall-parallelism-values*)))

(encapsulate
 ((waterfall-printing () t))
 (logic)
 (local (defun waterfall-printing () :full))
 (defthm waterfall-printing-constraint
   (member-eq (waterfall-printing)
              *waterfall-printing-values*)))

(defun make-symbol-constants-fn (prefix lst)
  (declare (xargs :guard (and (symbolp prefix)
                              (symbol-listp lst))))
  (cond ((endp lst) nil)
        (t (cons `(defun ,(symbol-constant-fn prefix (car lst)) ()
                    (declare (xargs :guard t :mode :logic))
                    ,(car lst))
                 (make-symbol-constants-fn prefix (cdr lst))))))

(defmacro make-waterfall-parallelism-constants (prefix)
  (cons 'progn (make-symbol-constants-fn prefix
                                         *waterfall-parallelism-values*)))

(make-waterfall-parallelism-constants waterfall-parallelism)

(defmacro make-waterfall-printing-constants (prefix)
  (cons 'progn (make-symbol-constants-fn prefix
                                         *waterfall-printing-values*)))

(make-waterfall-printing-constants waterfall-printing)

; We execute defattach events without :skip-checks.  But we avoid using
; set-waterfall-parallelism, because that causes an invocation of
; set-waterfall-printing, which is an error when #-acl2-par.
#+acl2-loop-only
(progn
  (defattach (waterfall-parallelism waterfall-parallelism-nil))
  (defattach (waterfall-printing waterfall-printing-full)))

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
                   (theory 'executable-counterpart-minimal-theory)))
  :doc
  ":Doc-Section Theories

  a minimal theory to enable~/~/

  This ~ilc[theory] (~pl[theories]) enables only a few built-in
  functions and executable counterparts.  It can be useful when you
  want to formulate lemmas that rather immediately imply the theorem
  to be proved, by way of a ~c[:use] hint (~pl[hints]), for example as
  follows.
  ~bv[]
  :use (lemma-1 lemma-2 lemma-3)
  :in-theory (union-theories '(f1 f2) (theory 'minimal-theory))
  ~ev[]
  In this example, we expect the current goal to follow from lemmas
  ~c[lemma-1], ~c[lemma-2], and ~c[lemma-3] together with rules ~c[f1]
  and ~c[f2] and some obvious facts about built-in functions (such as
  the ~il[definition] of ~ilc[implies] and the
  ~c[:]~ilc[executable-counterpart] of ~ilc[car]).  The
  ~c[:]~ilc[in-theory] hint above is intended to speed up the proof by
  turning off all inessential rules.~/

  :cited-by theory-functions")

(deftheory ground-zero (current-theory :here)

; WARNING: Keep this near the end of *acl2-pass-2-files* in order for
; the ground-zero theory to be as expected.

  :doc
  ":Doc-Section Theories

  ~il[enable]d rules in the ~il[startup] theory~/

  ACL2 concludes its initialization ~c[(boot-strapping)] procedure by
  defining the theory ~c[ground-zero]; ~pl[theories].  In fact, this
  theory is just the theory defined by ~c[(current-theory :here)] at
  the conclusion of initialization; ~pl[current-theory].~/

  Note that by evaluating the event
  ~bv[]
  (in-theory (current-theory 'ground-zero))
  ~ev[]
  you can restore the current theory to its value at the time you
  started up ACL2.~/

  :cited-by theory-functions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; End
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflabel

; WARNING: Put this at the end of the last file in
; *acl2-pass-2-files*.

  end-of-pass-2)
