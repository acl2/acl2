; RP-REWRITER

; Noe: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019 Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "aux-functions")

(include-book "extract-formula")

(include-book "misc")

(encapsulate
  nil

  (defthm dont-rw-syntaxp-aux-cons
    (equal (dont-rw-syntaxp-aux (cons a b))
           (AND (OR (atom a)
                   ; (strict-quotep a)
                    (DONT-RW-SYNTAXP-AUX a))
                (DONT-RW-SYNTAXP-AUX b))))
  

  (defthm dont-rw-syntaxp-cons
    (equal (dont-rw-syntaxp  (cons a b))
           (or nil;(strict-quotep (cons a b))
               (AND (OR (atom a)
                        ;(strict-quotep a)
                        (DONT-RW-SYNTAXP-AUX a))
                    (DONT-RW-SYNTAXP-AUX b))))
    :hints (("Goal"
             :in-theory (e/d (dont-rw-syntaxp) ())))))


(def-rp-rule make-fast-alist-def
  (equal (make-fast-alist (cons (cons x y) rest))
         (hons-acons x y
                     (make-fast-alist rest))))

(def-rp-rule len-cons
  (equal (len (cons a b))
         (+ 1 (len b))))

(def-rp-rule atom-cons
  (equal (atom (cons a b))
         nil))

(def-rp-rule consp-cons
  (consp (cons a b)))

(def-rp-rule equal-to-t
  (equal (equal a a)
         't))

(def-rp-rule boolean-listp-is-booleanp
  (booleanp (boolean-listp a))
  :hints (("goal"
           :in-theory (enable boolean-listp))))



;; add definitions from minimal theory.
(add-rp-rule car-cons)
(add-rp-rule cdr-cons)
(add-rp-rule return-last)
(add-rp-rule mv-nth)
(add-rp-rule the-check)
(add-rp-rule cons-with-hint)
(add-rp-rule iff)
(add-rp-rule wormhole-eval)
(add-rp-rule mv-list)
(add-rp-rule minusp)
(add-rp-rule plusp)
(add-rp-rule zerop)
(add-rp-rule listp)
(add-rp-rule case-split)
(add-rp-rule force)
(add-rp-rule /=)
(add-rp-rule =)
(add-rp-rule atom)
(add-rp-rule null)
(add-rp-rule endp)
(add-rp-rule eql)
(add-rp-rule not :outside-in t)
(add-rp-rule implies :outside-in t)
(add-rp-rule eq)
(add-rp-rule eql)
(add-rp-rule cons-equal)
(add-rp-rule acons)

(def-rp-rule append-of-nil
  (equal (append nil x)
         x))



#|(def-rp-rule$ t nil
  force-fail
  (implies
   (hard-error
    'force-fail
    "The below term could not be reduced to 't.
If you want to look at the stack, you can try using 
 (rp::update-rp-brr t rp::rp-state) and
 (rp::pp-rw-stack :omit '()
                  :evisc-tuple (evisc-tuple 10 12 nil nil)
                  :frames 50).
Forced term was:~% ~p0 ~% "
    (list (cons #\0 forced-term)))
   (equal (force forced-term) t))
  :hints (("goal" 
           :in-theory '(return-last hard-error hide))))||#

(def-rp-rule$ t nil
  force$-fail
  (implies
   (hard-error
    'force-fail
    "The below term could not be reduced to 't. 
If you want to look at the stack, you can enable and view it with 
 (rp::update-rp-brr t rp::rp-state) and
 (rp::pp-rw-stack :omit '()
                  :evisc-tuple (evisc-tuple 10 12 nil nil)
                  :frames 50). 

This was caused by the rule: ~p0
On the hypothesis: ~p1
Forced term is ~p2 ~% "
    (list (cons #\0 rule)
          (cons #\1 hyp)
          (cons #\2 forced-term)))
   (equal (force$ forced-term rule hyp) t))
  :hints (("goal" 
           :in-theory '(return-last hard-error hide))))


(disable-exc-counterpart force$)

(def-rp-rule force$-of-t
  (equal (force$ t rule-name hyp)
         t))
