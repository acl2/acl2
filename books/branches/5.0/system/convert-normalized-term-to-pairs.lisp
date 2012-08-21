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

; Written by:  J Moore
; email:       moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; April, 2012

(in-package "ACL2")

(tau-status :system nil)

(defun normalizedp (term)

; This notion of normalized just refers to the top-level IF structure.
; Interior IFs are allowed and not inspected.  For example,
; (IF A (FOO (IF (IF B C D) E F)) G) is ``normalized'' in this sense.

  (cond ((variablep term) t)
        ((fquotep term) t)
        ((eq (ffn-symb term) 'IF)
         (and (or (symbolp (fargn term 1))
                  (and (not (fquotep (fargn term 1)))
                       (not (eq (ffn-symb (fargn term 1)) 'IF))))
              (normalizedp (fargn term 2))
              (normalizedp (fargn term 3))))
        (t t)))

(verify-termination conjoin)

; Cntp-M stands for ``meaning'', with prefix ``cntp'' standing for
; convert-normalized-term-to-pairs.

(defun cntp-M-pair (pair)
  (fcons-term* 'IF (conjoin (car pair)) (cdr pair) *t*))

(defun cntp-M (pairs)
  (cond ((endp pairs) *t*)
        (t (fcons-term* 'IF
                        (cntp-M-pair (car pairs))
                        (cntp-M (cdr pairs))
                        *nil*))))

(defevaluator cntp-evl cntp-evl-lst ((IF x y z) (NOT x) (EQUAL x y)))

(local
 (defun rev (x)
   (if (endp x)
       nil
     (append (rev (cdr x)) (list (car x))))))

(local
 (defthm revappend-is-append-rev
   (equal (revappend x y)
          (append (rev x) y))))

(verify-termination dumb-negate-lit)

; The following definition is straight out of tau.lisp and could be replaced
; by (verify-termination convert-normalized-term-to-pairs) except I wanted to
; exhibit the defun here.

(defun convert-normalized-term-to-pairs (rhyps term ans)

; Term is a term in IF-normal form.  We convert it to a list of (hyps . concl)
; pairs such that the conjunction of the (implies (and ,hyps) concl) terms is
; IFF-equivalent to term.

  (cond
   ((variablep term)
    (cons (cons (revappend rhyps nil) term) ans))
   ((fquotep term)
    (if (equal term *nil*)
        (cond ((consp rhyps)
               (cons (cons (revappend (cdr rhyps) nil) (dumb-negate-lit (car rhyps)))
                     ans))
              (t (cons (cons nil *nil*) ans)))
        ans))
   ((eq (ffn-symb term) 'IF)
    (convert-normalized-term-to-pairs
     (cons (fargn term 1) rhyps)
     (fargn term 2)
     (convert-normalized-term-to-pairs
      (cons (dumb-negate-lit (fargn term 1)) rhyps)
      (fargn term 3)
      ans)))
   (t (cons (cons (revappend rhyps nil) term) ans))))

(local
 (defthm cntp-evl-conjoin-rev
   (iff (cntp-evl (conjoin (rev x)) alist)
        (cntp-evl (conjoin x) alist))))

(local
 (defthm cntp-evl-conjoin-append
   (iff (cntp-evl (conjoin (append x y)) alist)
        (and (cntp-evl (conjoin x) alist)
             (cntp-evl (conjoin y) alist)))))

(defthm convert-normalized-term-to-pairs-correct
  (implies (and (pseudo-termp term)
                (normalizedp term)
                (pseudo-term-listp rhyps))
           (iff (cntp-evl (cntp-M (convert-normalized-term-to-pairs
                                   rhyps term ans))
                          alist)
                (and (cntp-evl (fcons-term* 'IF (conjoin rhyps) term *t*)
                               alist)
                     (cntp-evl (cntp-M ans)
                               alist)))))

; The inductive proof breaks down into 6,396 Subgoals and takes about 78
; seconds on a 2011 Macbook Pro.
