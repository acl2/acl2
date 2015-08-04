; Copyright (C) 2013, Regents of the University of Texas
; Written by J Moore, April, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  J Moore
; email:       moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

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


;; [Jared] reordered these lemmas so the rev proof can make use of the append proof.

(local
 (defthm cntp-evl-conjoin-append
   (iff (cntp-evl (conjoin (append x y)) alist)
        (and (cntp-evl (conjoin x) alist)
             (cntp-evl (conjoin y) alist)))))

(local
 (defthm cntp-evl-conjoin-rev
   (iff (cntp-evl (conjoin (rev x)) alist)
        (cntp-evl (conjoin x) alist))))



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
               (cons (cons (revappend (cdr rhyps) nil)
                           (dumb-negate-lit (car rhyps)))
                     ans))
              (t (cons (cons nil *nil*) ans)))
        ans))
   ((eq (ffn-symb term) 'IF)
    (cond
     ((equal (fargn term 3) *nil*)
      (convert-normalized-term-to-pairs
       rhyps (fargn term 2)
       (cons (cons (revappend rhyps nil)
                   (fargn term 1)) ans)))
     ((equal (fargn term 2) *nil*)
      (convert-normalized-term-to-pairs
       rhyps (fargn term 3)
       (cons (cons (revappend rhyps nil)
                   (dumb-negate-lit (fargn term 1))) ans)))
     (t
      (convert-normalized-term-to-pairs
       (cons (fargn term 1) rhyps)
       (fargn term 2)
       (convert-normalized-term-to-pairs
        (cons (dumb-negate-lit (fargn term 1)) rhyps)
        (fargn term 3)
        ans)))))
   (t (cons (cons (revappend rhyps nil) term) ans))))


;; [Jared] dumb speed hacking... mostly just trying to not do so much case splitting

(local (defthm cntp-evl-conjoin-cons
         (iff (cntp-evl (conjoin (cons x y)) alist)
              (and (cntp-evl x alist)
                   (cntp-evl (conjoin y) alist)))))

(local (defthm cntp-evl-of-dumb-negate-lit
         (implies (pseudo-termp x)
                  (iff (cntp-evl (dumb-negate-lit x) alist)
                       (not (cntp-evl x alist))))))

(local (defthm pseudo-termp-of-dumb-negate-lit
         (implies (pseudo-termp x)
                  (pseudo-termp (dumb-negate-lit x)))))

(local (in-theory (disable conjoin
                           true-listp
                           dumb-negate-lit
                           rev
                           default-car
                           default-cdr
                           (:t cntp-m)
                           length
                           len
                           )))

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
                               alist))))
  :hints(("Goal"
          :induct (convert-normalized-term-to-pairs rhyps term ans)
          :expand ((pseudo-termp term)
                   (normalizedp term)))))

; The inductive proof breaks down into about 6,600 Subgoals and takes about 93
; seconds on a 2011 Macbook Pro.

; [Jared] down to just a couple of seconds now...

