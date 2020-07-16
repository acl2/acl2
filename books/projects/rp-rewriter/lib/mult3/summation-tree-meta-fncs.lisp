; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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

(include-book "fnc-defs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(include-book "pp-flatten-meta-fncs")

(include-book "std/util/defines" :dir :system)

(include-book "sum-merge-fncs")

(local
 (in-theory (disable +-IS-SUM)))

#|(define create-list-instance-single (e)
  :returns (res rp-termp :hyp (rp-termp e))
  (cond ((equal e ''0)
         ''nil)
        (t
         `(list ,e))))||#

(skip-proofs
 (define get-c-args ((c))
   :inline t
   :returns (mv (hash-code)
                (s-args rp-termp
                        :hyp (rp-termp c))
                (pp-args rp-termp
                         :hyp (rp-termp c))
                (c-arg-lst rp-term-listp
                           :hyp (rp-termp c))
                (valid symbolp))
   (b* ((c (ex-from-rp-loose c)))
     (case-match c
       #|(('d ('rp ''evenpi ('d-sum s pp c/d)))
       (mv s pp c/d 'd))||#
       (('c ('quote hash-code) s pp ('list . c-lst))
        (mv hash-code s pp c-lst 'c))
       (('c ('quote hash-code) s pp ''nil)
        (mv hash-code s pp nil 'c))
       (& (mv ''0 ''nil ''nil ''nil nil))))))

(progn

  (define sum-char-codes (chars)
    (if (atom chars)
        0
      (+  (if (characterp (car chars))
              (char-code (car chars))
            0)
          (sum-char-codes (cdr chars)))))

  (defwarrant sum-char-codes)

  #|(define pp-instance-hash (e)
    (declare (ignorable e))
    :returns (hash-code integerp)
    :inline t
    (cond ((not e)
           0)
          ((symbolp e)
           (cond ((equal e 'in1)
                  23)
                 ((equal e 'in2)
                  13)
                 ((equal e 'a)
                  15)
                 ((equal e 'b)
                  17)
                 (t
                  (b* ((e (symbol-name e)))
                    (sum-char-codes (explode e))))))
          ((characterp e)
           (char-code e))
          ((integerp e)
           e)
          ((and (quotep e)
                (consp (cdr e)))
           (pp-instance-hash (unquote e)))
          ((atom e)
           (nfix e))
          (t
           (+ (pp-instance-hash (car e))
              (* 4 (pp-instance-hash (cdr e)))))))||#

  ;;(memoize 'pp-instance-hash)

  (define pp-instance-hash (e)
    :returns (hash integerp)
    :inline t
    (case-match e
      (('and-list ('quote hash) &)
       (ifix hash))
      (''1
       1)
      (& 0)))

  
  (defwarrant pp-instance-hash$inline)

  (define pp-lst-hash (pp-lst)
    ;;:inline t
    :returns (hash-code integerp)
    ;;(loop$ for x in pp-lst sum (pp-instance-hash x))
    (if (atom pp-lst)
        0
      (+ (pp-instance-hash (car pp-lst))
         (pp-lst-hash (cdr pp-lst)))))

  (defwarrant pp-lst-hash)

  (define calculate-pp-hash (pp)
    :returns (hash-code integerp)
    :inline t
    (case-match pp
      (('list . pp-lst)
       ;;(let ((len (len pp-lst))) (* len len))
       (pp-lst-hash pp-lst)
       )
      (& 0)))

  (defwarrant calculate-pp-hash$inline)

  (define get-hash-code-of-single-s (s)
    :returns (hash-code integerp)
    :inline t
    (b* ((s (ex-from-rp/--loose s)))
      (case-match s
        (('s ('quote hash-code) & &)
         (ifix hash-code))
        (''0
         0)
        (&
         (progn$ (hard-error
                  'get-hash-code-of-single-s
                  "unrecognized s instance in get-hash-code-of-s:~p0 ~%"
                  (list (cons #\0 s)))
                 0)))))

  (defwarrant get-hash-code-of-single-s$inline)

  (define get-hash-code-of-s-lst (s-lst)
    :returns (hash-code integerp)
    :inline t
    ;;(loop$ for x in s-lst sum (get-hash-code-of-single-s x))
    (if (atom s-lst)
        0
      (+ (get-hash-code-of-single-s (car s-lst))
         (get-hash-code-of-s-lst (cdr s-lst)))))

  (defwarrant get-hash-code-of-s-lst$inline)

  (define get-hash-code-of-s (s)
    :returns (hash-code integerp)
    :inline t
    (case-match s
      (('list . s-lst)
       (get-hash-code-of-s-lst s-lst))
      (& 0)))

  (defwarrant get-hash-code-of-s$inline)

  (define get-hash-code-of-single-c (c)
    :returns (hash-code integerp)
    :inline t
    (b* ((c (ex-from-rp/--loose c)))
      (case-match c
        (('c ('quote hash-code) & & &)
         (ifix hash-code))
        (''0
         0)
        (& (progn$ (hard-error
                    'get-hash-code-of-single-c
                    "unrecognized c instance:~p0 ~%"
                    (list (cons #\0 c)))
                   0)))))

  (defwarrant get-hash-code-of-single-c$inline)

  (define get-hash-code-of-c-lst (c-lst)
    :returns (hash-code integerp)
    :inline t
    ;;(loop$ for x in s-lst sum (get-hash-code-of-single-c x))
    (if (atom c-lst)
        0
      (+ (get-hash-code-of-single-c (car c-lst))
         (get-hash-code-of-c-lst (cdr c-lst)))))

  (define get-hash-code-of-c (c)
    :returns (hash-code integerp)
    :inline t
    (case-match c
      (('list . c-lst)
       (get-hash-code-of-c-lst c-lst))
      (& 0)))

  (define calculate-s-hash (pp c)
    :returns (hash-code integerp)
;:inline t
    (+ (calculate-pp-hash pp)
       (* 2 (get-hash-code-of-c c)))
    #|(* 4 (+ (* 2 (calculate-pp-hash pp))
    (get-hash-code-of-c c)))||#
    )

  (define calculate-c-hash (s pp c)
    :returns (hash-code integerp)
;:inline t
    (+ (get-hash-code-of-s s)
       (calculate-pp-hash pp)
       (* 2 (get-hash-code-of-c c)))
       
    #|(* 4 (+ (* 2 (calculate-pp-hash pp))
            (get-hash-code-of-s s)
    (get-hash-code-of-c c)))||#
    ))

(define is-rp-bitp (term)
  (case-match term
    (('rp ''bitp &)
     t)))

(skip-proofs
 (acl2::defines
  is-c-bitp-traverse-aux
  (define is-c-bitp-traverse-aux (single-c remainder)
    (case-match single-c
      (('c & s pp c)
       (b* ((pp-len (case-match pp (('list . lst) (len lst)) (& 0)))
            (s-len (case-match s (('list . lst) (len lst)) (& 0)))
            #|((when (> s-len 0))
            -1)||#
            (remainder (- remainder (+ pp-len s-len))))
         (if (< remainder 0)
             remainder
           (case-match c
             (('list . lst)
              (is-c-bitp-traverse-aux-lst lst (1+ (* 2 remainder))))
             (& remainder)))))
      (('rp ''bitp &)
       (- remainder 1))
      (& (progn$
          (hard-error 'is-c-bitp-traverse-aux
                      "Unexpected c form ~p0 ~%"
                      (list (cons #\0 single-c)))
          -1))))

  (define is-c-bitp-traverse-aux-lst (lst remainder)
    (if (atom lst)
        remainder
      (is-c-bitp-traverse-aux-lst (cdr lst)
                                  (is-c-bitp-traverse-aux (car lst) remainder))))))

(define is-c-bitp-traverse (single-c)
  (declare (ignorable single-c))
  (and t (>= (is-c-bitp-traverse-aux single-c 3) 0)))

(define create-c-instance (s pp c)
;:inline t
  :returns (c/d-res rp-termp :hyp (and (rp-termp pp)
                                       (rp-termp s)
                                       (rp-termp c)))
  (cond ((or (and (equal c ''nil)
                  (equal s ''nil)
                  (case-match pp (('list ('and-list & &)) t)))
             (and (equal c ''nil)
                  (equal pp ''nil)
                  (case-match s (('list ('s & & &)) t)
                    (('list ('rp ''bitp &)) t)))
             (and (equal s ''nil)
                  (equal pp ''nil)
                  (case-match c
                    (('list single-c)
                     (or (is-rp-bitp single-c)
                         (is-c-bitp-traverse single-c))))))
         ''0)
        ((and (quotep pp)
              (consp (cdr pp))
              (quotep s)
              (consp (cdr s))
              (quotep c)
              (consp (cdr c)))
         `',(c 0 (unquote s) (unquote pp) (unquote c)))
        (t
         (b* ((hash-code (calculate-c-hash s pp c))
              #|(- (if (equal hash-code 2215122)
              (progn$ (cw "found hash-code: ~p0 ~%" hash-code)
              (sleep 10))
              nil))||#)
         ;;;;; hash-code calc..
           `(c ',hash-code ,s ,pp ,c)))))

(local
 (defthm is-rp-of-bitp
   (is-rp `(rp 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(define can-s-be-compressed (pp c)
  :inline t
  (case-match c
    (('list ('c & ''nil c-pp &))
     (equal pp c-pp))))

(define compress-s (pp c)
  (case-match c
    (('list ('c & ''nil c-pp c-c))
     (b* (((unless (equal pp c-pp))
           `(rp 'bitp (s ',(calculate-s-hash pp c) ,pp ,c))))
       (compress-s c-pp c-c)))))
      
               

(define create-s-instance (pp c)
  :inline t
  :returns (res rp-termp
                :hyp (and (rp-termp pp)
                          (rp-termp c)))
  (cond ((and (quotep pp)
              (quotep c)
              (consp (cdr pp))
              (consp (cdr c)))
         `',(s 0 (unquote pp) (unquote c)))
        ((and (equal c ''nil)
              (case-match pp (('list ('and-list & &)) t)))
         (cadr pp))
        ((and (equal pp ''nil)
              (case-match c
                (('list single-c)
                 (or (is-rp-bitp single-c)))))
         (cadr c))
        ((and (equal pp ''nil)
              (case-match c
                (('list single-c)
                 (is-c-bitp-traverse single-c))))
         `(rp 'bitp ,(cadr c)))
        ((can-s-be-compressed pp c)
         (compress-s pp c))
        ((and
          (case-match pp
            (('list & &) t))
          (case-match c
            (('list ('rp ''bitp ('c & & c-pp &)))
             (and (equal c-pp pp)))))
         (cadr c))

        (t
         `(rp 'bitp (s ',(calculate-s-hash pp c) ,pp ,c)))))

#|(define d-to-c ((c/d))
  :returns (c/d-res rp-termp :hyp (rp-termp c/d))
  :inline t
  ;; try converting d to c.
  (case-match c/d
    (('d ('rp ''evenpi ('d-sum s pp1 c/d1)))
     (cond ((and (quotep s) (consp (cdr s))
                 (quotep pp1) (consp (cdr pp1))
                 (quotep c/d1) (consp (cdr c/d1)))
            `',(d (d-sum (unquote s)
                         (unquote pp1)
                         (unquote c/d1))))
           (t
            (case-match s
              (('list ('-- ('s pp2 c/d2)))
               (if (and (rp-equal-cnt pp1 pp2 1)
                        (rp-equal-cnt c/d1 c/d2 0))
                   (create-c-instance ''nil pp1 c/d1)
                 c/d))
              (& c/d)))))
    (('c arg1 arg2 arg3)
     (if (and (quotep arg1)
              (consp (cdr arg1))
              (quotep arg2)
              (consp (cdr arg2))
              (quotep arg3)
              (consp (cdr arg3)))
         `',(c (unquote arg1)
               (unquote arg2)
               (unquote arg3))
       c/d))
    (& c/d)))||#

#|
(define c-cough ((single-c))
;:inline t
  :returns (mv (s-coughed rp-termp :hyp (rp-termp single-c))
               (pp-coughed rp-termp :hyp (rp-termp single-c))
               (c-cleaned rp-termp :hyp (rp-termp single-c)))
  :prepwork ((local
              (in-theory (e/d (is-rp) ()))))
  (b* (((mv & s-arg pp-arg c-arg type)
        (get-c-args single-c)))
    (cond ((equal single-c ''0)
           (mv ''nil ''nil single-c))
          (type
           (b* (((mv s-coughed s)
                 (c-fix-s-args s-arg))
                ((mv pp-coughed pp)
                 (c-fix-pp-args pp-arg (expt 2 30)))
                (c-cleaned
                 ;;(if (eq type 'single-c)
                 (create-c-instance s pp c-arg)
                 ;;  `(d (rp 'evenpi (d-sum ,s ,pp ,c/d-arg)))))
                 ;;(c/d-cleaned (d-to-c c/d-cleaned))
                 ))
             (mv s-coughed pp-coughed c-cleaned)))
          (t
           (progn$ (cw "c-cough is given a bad term ~p0 ~%" single-c)
                   (mv ''nil ''nil single-c))))))||#

;; (c/d-cough '(c (list (s 'nil (list (c 'nil (list a b) 'nil)))
;;                      (s 'nil (list (c 'nil (list a b) 'nil))))
;;                (list a a (-- b) (-- c))
;;                'nil))

(define fast-merge-profile ()
  t)

(define swap-terms (single-c1 single-c2 swap)
  :inline t
  :returns (mv (res1 rp-termp
                     :hyp (and (rp-termp single-c1)
                               (rp-termp single-c2)))
               (res2 rp-termp
                     :hyp (and (rp-termp single-c1)
                               (rp-termp single-c2))))
  (if swap
      (mv single-c2 single-c1)
    (mv single-c1 single-c2)))

(define clean-c-args (s-arg pp-arg (pp-arg-cnt natp) clean-flg)
  ;; similar to what c-cough does.
  :returns (mv (s-coughed rp-termp
                          :hyp (rp-termp s-arg))
               (s-arg-res rp-termp
                          :hyp (rp-termp s-arg))
               (pp-coughed rp-termp
                           :hyp (rp-termp pp-arg))
               (pp-arg-res rp-termp
                           :hyp (rp-termp pp-arg)))
  (b* (((mv s-coughed s-arg)
        (if clean-flg (c-fix-s-args s-arg) (mv ''nil s-arg)))
       ((mv pp-coughed pp-arg)
        (if clean-flg (c-fix-pp-args pp-arg pp-arg-cnt)
          (mv ''nil pp-arg))))
    (mv s-coughed s-arg pp-coughed pp-arg)))

#|(define remove-s-from-for-fast-merge (s-arg2 pp-arg1 c-arg1)
  (declare (ignorable pp-arg1 c-arg1 pp-arg1))
  :guard (and (consp s-arg2)
              (consp (cdr s-arg2)))
  :inline t
  (b* ((s-arg `(list . ,(cddr s-arg2)))
       ;;(s-arg (s-sum-merge s-arg2 `(list (-- (s ,pp-arg1 ,c/d-arg1)))))
       )
    s-arg))||#

;; (define extra-s-can-be-pp (pp c)
;;   :inline t
;;   (or (and (equal c ''nil)
;;            (case-match pp (('list ('binary-and & &)) t)))
;;       (and (case-match c (('list ('rp ''bitp &)) t))
;;            (equal pp ''nil)))
;;   ///
;;   (defthm extra-s-can-be-pp-implies
;;     (implies (extra-s-can-be-pp pp c)
;;              (and (or (and (equal c ''nil)
;;                            (case-match pp (('list ('binary-and & &)) t)))
;;                       (and (case-match c (('list ('rp ''bitp &)) t))
;;                            (equal pp ''nil)))))
;;     :rule-classes :forward-chaining))

;; (mutual-recursion
;;  (defun search-pattern (term)
;;    (declare (xargs :guard t))
;;    (cond ((extra-s-can-be-pp term)
;;           (list term))
;;          ((or (atom term)
;;               (quotep term))
;;           nil)
;;          (t
;;           (search-pattern-lst (cdr term)))))
;;  (defun search-pattern-lst (lst)
;;    (if (atom lst)
;;        nil
;;      (append (search-pattern (car lst))
;;              (search-pattern-lst (cdr lst))))))

;; (make-flag search-pattern :defthm-macro-name defthm-search-pattern)

;; (memoize 'search-pattern)

(local
 (defthm is-rp-of-evenpi
   (IS-RP `(RP 'EVENPI ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm is-rp-of-bitp
   (IS-RP `(RP 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm rp-termp-of-d
   (iff (rp-termp `(d ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of---
   (iff (rp-termp `(-- ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of-list
   (iff (rp-termp `(list . ,x))
        (rp-term-listp x))))

#|(local
 (defthm rp-termp-of-d-sum
   (iff (rp-termp `(d-sum ,x ,y ,z))
        (and (rp-termp x)
             (rp-termp y)
             (rp-termp z)))))||#

#|(local
 (defthm rp-termp-of-of-rp-evenpi
   (iff (rp-termp `(rp 'evenpi ,x))
        (rp-termp x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))||#

#|(define is-a-negated-minterm (term)
  :inline t
  (case-match term
    (('list ('-- ('binary-and & &))) t)))||#

#|(define c/d-merge-slow-aux (pp-arg1 pp-arg2 pp-coughed-from-arg
                                    s-arg1 s-arg2 s-coughed-from-arg
                                    extra-s-arg1
                                    extra-s-arg2
                                    c-arg
                                    clean-flg
                                    c/d1-is-c
                                    c/d2-is-c)
  :inline t
  :prepwork ((local
              (in-theory (disable falist-consistent
                                  (:TYPE-PRESCRIPTION RP-TERMP)
                                  (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                  (:TYPE-PRESCRIPTION IS-RP$INLINE)
                                  (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                                  (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                  (:FORWARD-CHAINING RP-TERMP-IMPLIES)
                                  (:FORWARD-CHAINING
                                   EXTRACT-FROM-SYNP-PSEUDO-TERM-LISTP)
                                  (:REWRITE DEFAULT-CDR)
                                  (:TYPE-PRESCRIPTION O<)
                                  (:REWRITE ACL2::O-P-O-INFP-CAR)
                                  (:REWRITE DEFAULT-CAR)
                                  (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                                  (:TYPE-PRESCRIPTION O-P)
                                  rp-termp
                                  (:REWRITE ACL2::MV-NTH-OF-CONS)))))
  :returns (mv (s-coughed rp-termp
                          :hyp (and (rp-termp pp-arg1)
                                    (rp-termp pp-arg2)
                                    (rp-termp pp-coughed-from-arg)
                                    (rp-termp s-arg1)
                                    (rp-termp s-arg2)
                                    (rp-termp s-coughed-from-arg)
                                    (if c/d1-is-c (rp-termp extra-s-arg1) t)
                                    (if c/d2-is-c (rp-termp extra-s-arg2) t)
                                    (rp-termp c-arg)))
               (pp-coughed rp-termp
                           :hyp (and (rp-termp pp-arg1)
                                     (rp-termp pp-arg2)
                                     (rp-termp pp-coughed-from-arg)
                                     (rp-termp s-arg1)
                                     (rp-termp s-arg2)
                                     (rp-termp s-coughed-from-arg)
                                     (if c/d1-is-c (rp-termp extra-s-arg1) t)
                                     (if c/d2-is-c (rp-termp extra-s-arg2) t)
                                     (rp-termp c-arg)))
               (c/d-merged rp-termp
                           :hyp (and (rp-termp pp-arg1)
                                     (rp-termp pp-arg2)
                                     (rp-termp pp-coughed-from-arg)
                                     (rp-termp s-arg1)
                                     (rp-termp s-arg2)
                                     (rp-termp s-coughed-from-arg)
                                     (if c/d1-is-c (rp-termp extra-s-arg1) t)
                                     (if c/d2-is-c (rp-termp extra-s-arg2) t)
                                     (rp-termp c-arg))))
  (b* (((mv pp-arg pp-arg-cnt1) (pp-sum-merge pp-arg1 pp-arg2))
       ((mv pp-arg pp-arg-cnt2) (pp-sum-merge pp-coughed-from-arg pp-arg))

       (s-arg (s-sum-merge s-arg2 s-coughed-from-arg))
       (s-arg (s-sum-merge s-arg1 s-arg))
       ((mv s-arg pp-arg pp-arg-cnt3)
        (cond (c/d1-is-c
               (if (is-a-negated-minterm extra-s-arg1)
                   (b* (((mv pp-arg pp-arg-cnt3)
                        (pp-sum-merge pp-arg extra-s-arg1)))
                     (mv s-arg pp-arg pp-arg-cnt3))
                 (mv (s-sum-merge extra-s-arg1 s-arg)
                        pp-arg
                        0)))
              (t (mv s-arg pp-arg 0))))
       ((mv s-arg pp-arg pp-arg-cnt4)
        (cond (c/d2-is-c
               (if (is-a-negated-minterm extra-s-arg2)
                   (b* (((mv pp-arg pp-arg-cnt4)
                         (pp-sum-merge pp-arg extra-s-arg2)))
                     (mv s-arg pp-arg pp-arg-cnt4))
                 (mv (s-sum-merge extra-s-arg2 s-arg)
                     pp-arg
                     0)))
              (t (mv s-arg pp-arg 0))))
       (pp-arg-cnt (+ ;;(expt 2 20) ;;test and remove later when sure...
                    pp-arg-cnt1 pp-arg-cnt2 pp-arg-cnt3 pp-arg-cnt4))
       #|(s-arg (cond ((and c/d1-is-c c/d2-is-c)
       (s-sum-merge s-arg (s-sum-merge extra-s-arg1 extra-s-arg2)))
       (c/d1-is-c (s-sum-merge s-arg extra-s-arg1))
       (c/d2-is-c (s-sum-merge s-arg extra-s-arg2))
       (t s-arg)))||#
       ((mv s-coughed s-arg pp-coughed pp-arg)
        (clean-c-args s-arg pp-arg pp-arg-cnt clean-flg))
       (d-res `(d (rp 'evenpi (d-sum ,s-arg ,pp-arg ,c-arg))))
       (c/d-merged (if clean-flg (d-to-c d-res) d-res)))

    (mv s-coughed pp-coughed c/d-merged)))||#

;;;;;;;;;;;;;;;

;;c-merge

(progn
  (define can-c-merge-fast-aux (s-lst pp c)
    ;;:inline t
    (if (atom s-lst)
        nil
      (or (b* ((cur-s (ex-from-rp-loose (car s-lst))))
            (case-match cur-s
              (('s & pp-arg c-arg)
               (progn$
                (and
                 ;;(equal pp-arg pp) (equal c/d-arg c)
                 (rp-equal-cnt c-arg c 0) (rp-equal-cnt pp-arg pp 0) ;; TEST
                 ;; ADDING CALCULATE-PP-HASH COMPARISON HERE.
                 )))))
          (can-c-merge-fast-aux (cdr s-lst) pp c)
          )))

  (define can-c-merge-fast (single-c1 single-c2)
    ;; returns nil, 0 or 1. 0 and 1 mean terms can merge fast, and 1 means flip c/d1
    ;; and c/d2
    (b* (((mv & s-arg1 pp-arg1 c-arg1 type1) (get-c-args single-c1))
         ((mv & s-arg2 pp-arg2 c-arg2 type2) (get-c-args single-c2))
         (c-arg1 (create-list-instance c-arg1))
         (c-arg2 (create-list-instance c-arg2))
         ((when (or (not (equal type1 'c))
                    (not (equal type2 'c))))
          nil)
         (match1 ;; possible match to (sum (f2 x) (f2 (sum (m2 x) y)))
          ;; c/d1 = (c 'nil arg-pp1 arg-c/d1)
          ;; c/d2 = (c (list (s arg-pp1 arg-c/d1) other-s) arg-pp2 arg-c/d2)
          (and (equal s-arg1 ''nil)
               (case-match s-arg2 (('list . &) t))))

         (match2 ;; possible match to (sum (f2 x) (f2 (sum (m2 x) y)))
          ;; c/d1 = (c (list (s arg-pp1 arg-c/d1) other-s) arg-pp2 arg-c/d2)
          ;; c/d2 = (c 'nil arg-pp1 arg-c/d1)
          (and (case-match s-arg1 (('list . &) t))
               (equal s-arg2 ''nil))))
      (cond (match1
             (if (can-c-merge-fast-aux (cdr s-arg2) pp-arg1 c-arg1)
                 0
               nil))
            (match2
             (if (can-c-merge-fast-aux (cdr s-arg1) pp-arg2 c-arg2)
                 1
               nil))
            (t
             nil))))

  (define well-merged-c-lst-p-aux (single-c c-lst)
    (if (atom c-lst)
        t
      (and (not (can-c-merge-fast single-c (car c-lst)))
           (well-merged-c-lst-p-aux single-c (cdr c-lst)))))

  (define well-merged-c-lst-p (c-lst)
    (if (atom c-lst)
        t
      (and (well-merged-c-lst-p-aux (car c-lst) (cdr c-lst))
           (well-merged-c-lst-p (cdr c-lst)))))

  (define well-merged-c-p (c &key (message '""))
    (and nil
         (case-match c
           (('list . c-lst)
            (b* ((res (well-merged-c-lst-p c-lst)))
              (if res
                  res
                (hard-error 'well-merged-c-p
                            "The given c is not merged well.~%~p0~%~p1~%"
                            (list (cons #\0 message)
                                  (cons #\1 c))))))
           (& t))))

  (acl2::defines
   all-well-merged-c-p
   (define all-well-merged-c-p (term)
     :measure (cons-count term)
     :prepwork ((local
                 (in-theory (enable measure-lemmas))))
     (b* ((term (ex-from-rp-loose term)))
       (case-match term
         (('c & s & c)
          (and (well-merged-c-p c)
               (all-well-merged-c-p c)
               (all-well-merged-c-p s)))
         (('s & & c)
          (and (well-merged-c-p c)
               (all-well-merged-c-p c)))
         (('list . lst)
          (all-well-merged-c-lst-p lst))
         (& t))))

   (define all-well-merged-c-lst-p (lst)
     (if (atom lst)
         t
       (and (all-well-merged-c-p (car lst))
            (all-well-merged-c-lst-p (cdr lst)))))))

;; TEST:try passign hash of c (and make the calculation  same as s)
(define single-c-try-merge-params (s-lst c-hash-code pp-arg c-arg)
  ;; returns (mv updated-s-lst success)

  (if (atom s-lst)
      (mv s-lst nil)
    (b* ((cur-s (ex-from-rp-loose (car s-lst))))
      (case-match cur-s
        (('s ('quote s-hash-code) cur-pp-arg cur-c-arg)
         (if (and (equal c-hash-code s-hash-code)
                  (equal c-arg cur-c-arg) (equal pp-arg cur-pp-arg)
                  ;;(rp-equal-cnt c-arg cur-c-arg  0)
                  ;;(rp-equal-cnt pp-arg cur-pp-arg 0)
                  )
             (mv (cdr s-lst) t)

           (b* (((mv rest-s-lst success)
                 (single-c-try-merge-params (cdr s-lst) c-hash-code pp-arg c-arg)))
             (if success
                 (mv (cons (car s-lst) rest-s-lst) t)
               (mv s-lst nil)))))
        (&
         (progn$
          (hard-error 'single-c-try-merge-params
                      "Bad form for current s-lst:~p0~%"
                      (list (cons #\0 s-lst)))
          (mv s-lst nil)))))))



(skip-proofs
 (acl2::defines
  c-sum-merge

  (define single-c-try-merge  (single-c1 single-c2)
    ;; returns (mv coughed-s coughed-pp-lst merged-single-c merge-success)
    ;; if merge-success is t
    ;; otherwise (mv nil nil 0 merge-success)
    (b* (((mv & s-arg1 & & type1) (get-c-args single-c1))
         ((mv & s-arg2 & & type2) (get-c-args single-c2))
         ((when (or (not type1) (not type2)))
          (progn$ (hard-error
                   'single-c-try-merge
                   "Unexpected single-c instances.~%single-c1:~p0~%single-c2:~p1~%"
                   (list (cons #\0 single-c1)
                         (cons #\1 single-c1)))
                  (mv ''nil nil ''0 nil)))

         ;; check if there is any chance of merger
         (case1
          ;;single-c1 = (c & ''nil pp-arg1 c-arg1)
          ;;single-c2 = (c & (list . s-lst) pp-arg2 c-arg2)
          (and (equal s-arg1 ''nil)
               (case-match s-arg2 (('list . &) t))))
         (case2
          ;;single-c2 = (c & (list . s-lst) pp-arg2 c-arg2)
          ;;single-c1 = (c & ''nil pp-arg1 c-arg1)
          (and (equal s-arg2 ''nil)
               (case-match s-arg1 (('list . &) t))))

         ((unless (or case1 case2))
          (mv ''nil nil ''0 nil))

         ;;when case2 applies, swap the single-cs to avoid repeating code.
         ((mv single-c1 single-c2)
          (swap-terms single-c1 single-c2 case2))
         ((mv c1-hash-code &      pp-arg1 c-arg1-lst &) (get-c-args single-c1))
         ((mv &            s-arg2 pp-arg2 c-arg2-lst &) (get-c-args single-c2))

         ;; search for a merge potential by going through s-lst of the single-c2
         ;; when a match is found, that s will be removed from the list.
         ((mv updated-s-lst success)
          (single-c-try-merge-params (cdr s-arg2)
                                     c1-hash-code
                                     pp-arg1
                                     (create-list-instance c-arg1-lst)))
         ;; no match? move on..
         ((unless success)
          (mv ''nil nil ''0 nil))
         ;; if it reached here, then it  means it can merge. Eviscerate single-c1
         ;; and merge its arguments:
         ;; first merge c-arguments. It might cough out s and pp lists..
         ((mv arg-coughed-s arg-coughed-pp-lst-lst arg-merged-c-lst)
          (c-sum-merge c-arg1-lst c-arg2-lst ))
         ;;(- (well-merged-c-p arg-merged-c :message (list 'pos1 c-arg1 c-arg2)))
         ;; merge all the pp lists. the  existing ones from initial single-cs and
         ;; the one that was coughed out.
;((mv merged-pp &) (pp-sum-merge pp-arg1 pp-arg2))
;((mv merged-pp &) (pp-sum-merge arg-coughed-pp-lst-lst merged-pp))

         (pp-lst-lst (cons-pp-to-pp-lst-lst pp-arg2 arg-coughed-pp-lst-lst))
         (pp-lst-lst (cons-pp-to-pp-lst-lst pp-arg1 pp-lst-lst))
         ((mv pp-lst coughed-pp-lst)
          (pp-lst-sum-merge pp-lst-lst :for-c t))
         (new-pp-arg (pp-lst-to-pp pp-lst))

         ;; also merge the updated s-lst of single-c2 and coughed s-lst.
         (merged-s (s-sum-merge arg-coughed-s
                                (create-list-instance updated-s-lst)))
         ;; before creating the c instance, try coughing out with the new s and
         ;; pp arguments.
         ((mv coughed-s new-s-arg)
          (c-fix-s-args merged-s))
         (arg-merged-c (create-list-instance arg-merged-c-lst))
         #|((mv coughed-pp new-pp-arg)
         (c-fix-pp-args merged-pp (expt 2 30)))||#)
      (mv coughed-s coughed-pp-lst
          (create-c-instance new-s-arg
                             new-pp-arg
                             arg-merged-c)
          t)))

  (define c-sum-merge-lst-aux (single-c1 c2-lst)
    ;;:returns (mv coughed-s coughed-pp-lst merged-single-c rest-c2-lst merge-success)

    ;; try and merge single-c1 with something in c2-lst
    ;; after the merge, coughed-s and coughed-pp-lst might have results from the
    ;; new c.
    ;; the result "merged-single-c" may be mergable with something in rest-c2-lst

    (if (atom c2-lst)
        (mv ''nil nil ''0 nil nil)
      (b* (((mv coughed-s coughed-pp-lst merged-single-c merge-success)
            (single-c-try-merge single-c1 (car c2-lst)))
           ((when merge-success)
            (mv coughed-s coughed-pp-lst merged-single-c (cdr c2-lst) merge-success))
           
           ((mv coughed-s coughed-pp-lst merged-single-c rest-c2-lst merge-success)
            (c-sum-merge-lst-aux single-c1 (cdr c2-lst)))

           ;;(- (well-merged-c-p merged-c :message "pos. a"))
           )
        (if merge-success
            (mv coughed-s coughed-pp-lst merged-single-c (cons (car c2-lst) rest-c2-lst)
                merge-success)
          (mv ''nil ''nil ''0 c2-lst nil)))))

  (define c-sum-merge-lst (single-c1 c2-lst )
    
    :measure (acl2-count c2-lst)
    ;;:returns (mv coughed-s2 coughed-pp-lst-lst new-c2-lst)

    ;; Same as c-sum-merge-lst-aux but merged-single-c is not mergable with anything
    ;; in rest-c2-lst because it was tried to be merged as long as it goes.

    (b* (((mv coughed-s coughed-pp-lst merged-single-c rest-c2-lst merge-success)
          (c-sum-merge-lst-aux single-c1 c2-lst)))
      (if merge-success
          (b* (((mv coughed-s2 coughed-pp-lst-lst new-c2-lst)
                (c-sum-merge-lst merged-single-c rest-c2-lst))
               (coughed-s (s-sum-merge coughed-s coughed-s2))
               (coughed-pp-lst-lst (if coughed-pp-lst (pp-cons coughed-pp-lst
                                                               coughed-pp-lst-lst)
                                     coughed-pp-lst-lst))
               ;;((mv coughed-pp &) (pp-sum-merge coughed-pp coughed-pp2))
               )
            (mv coughed-s coughed-pp-lst-lst new-c2-lst))
        (mv ''nil nil (s-sum-merge-aux (list single-c1) c2-lst)))))

  (define c-sum-merge-lst-lst (c1-lst c2-lst)
    ;;:returns (mv coughed-s coughed-pp-lst-lst merged-c-lst rest-c1-lst rest-c2-lst)
    (if (atom c1-lst)
        (mv ''nil nil nil  c2-lst)
      (b* (((mv coughed-s coughed-pp-lst-lst c2-lst)
            (c-sum-merge-lst (car c1-lst) c2-lst))

           ;;(- (well-merged-c-p merged-c :message "pos. b"))

           ((mv coughed-s2 coughed-pp-lst-lst2 merged-c-lst  c2-lst)
            (c-sum-merge-lst-lst (cdr c1-lst) c2-lst))

           ;;(- (well-merged-c-p (create-list-instance merged-c-lst) :message "pos. c"))

           (coughed-s-merged (s-sum-merge coughed-s coughed-s2))
           (coughed-pp-lst-lst (append-pp-lst-lsts coughed-pp-lst-lst
                                                   coughed-pp-lst-lst2))
;((mv coughed-pp-merged &) (pp-sum-merge coughed-pp coughed-pp2))
           )
        (mv coughed-s-merged
            coughed-pp-lst-lst
            merged-c-lst
            c2-lst))))

  (define c-sum-merge (c1-lst c2-lst)
    :returns (mv (coughed-s rp-termp
                            :hyp (and (rp-term-listp c1-lst)
                                      (rp-term-listp c2-lst)))
                 (coughed-pp-lst-lst rp-term-list-listp
                                     :hyp (and (rp-term-listp c1-lst)
                                               (rp-term-listp c2-lst)))
                 (merged-c-lst rp-term-listp
                               :hyp (and (rp-term-listp c1-lst)
                                         (rp-term-listp c2-lst))))
    :measure (+ (cons-count c1-lst)
                1
                (cons-count c2-lst))
    (b* ((first-id (case-match c1-lst
                     (('list ('c ('quote hash) . &) . &) hash)
                     (& 0)))
         (second-id (case-match c2-lst
                      (('list ('c ('quote hash) . &) . &) hash)
                      (& 0)))
         (len1 (len c1-lst))
         (len2 (len c2-lst))
         ((mv c1-lst c2-lst) (swap-terms c1-lst c2-lst
                                         (if (= len1 len2)
                                             (> (nfix first-id)
                                                (nfix second-id))
                                           (> len1 len2)))))
      (c-sum-merge-aux c1-lst c2-lst)))

  (define c-sum-merge-aux (c1-lst c2-lst)
    ;; returns (mv coughed-s coughed-pp-lst-lst res-c)

    :returns (mv (coughed-s rp-termp
                            :hyp (and (rp-termp c1-lst)
                                      (rp-termp c2-lst)))
                 (coughed-pp-lst-lst rp-term-list-listp
                                     :hyp (and (rp-termp c1-lst)
                                               (rp-termp c2-lst)))
                 (c/d-merged rp-termp
                             :hyp (and (rp-termp c1-lst)
                                       (rp-termp c2-lst))))
    :measure (+ (cons-count c1-lst)
                1
                (cons-count c2-lst))
    (cond ((equal c1-lst nil)
           (mv ''nil nil c2-lst))
          ((equal c2-lst nil)
           (mv ''nil nil c1-lst))
          (t (b* (((mv coughed-s1 coughed-pp-lst-lst1 merged-c-lst  c2-lst)
                   (c-sum-merge-lst-lst c1-lst c2-lst))

                  ;;(- (well-merged-c-p (create-list-instance merged-c-lst) :message "pos. d"))

                  
                  ((unless merged-c-lst)
                   (mv coughed-s1 coughed-pp-lst-lst1 c2-lst))
                  ((mv coughed-s2 coughed-pp2-lst-lst c2-lst)
                   (c-sum-merge merged-c-lst c2-lst))
                  ;;(- (well-merged-c-p arg-merged-c :message "pos. 2"))
                  (coughed-s (s-sum-merge coughed-s1 coughed-s2))
                  ;;((mv coughed-pp &) (pp-sum-merge coughed-pp1 coughed-pp2))

                  (coughed-pp-lst-lst (append-pp-lst-lsts coughed-pp2-lst-lst coughed-pp-lst-lst1))

                  ;;(coughed-pp-lst-lst (cons-pp-to-pp-lst-lst  coughed-pp2-lst-lst))

                  )
               (mv coughed-s coughed-pp-lst-lst c2-lst)))))))

#|(memoize 'c-sum-merge-lst-lst
         :recursive nil)||#

(memoize 'c-sum-merge-aux
         :memo-table-init-size 100000
         ;;:recursive nil
         :condition '(and (not (equal c1-lst nil)) (not (equal c2-lst nil)))
         :aokp t)
#|(memoize 'c-sum-merge-lst
         :memo-table-init-size 100000
         :recursive nil
         :aokp t)||#

;; :i-am-here

#|(C-SUM-MERGE
        '(LIST (C '455715
                 'NIL
                 (LIST (AND-LIST (LIST (BIT-OF (RP 'INTEGERP IN1) '57)
                                       (BIT-OF (RP 'INTEGERP IN1) '58)
                                       (BIT-OF (RP 'INTEGERP IN1) '59)))
                       (AND-LIST (LIST (BIT-OF (RP 'INTEGERP IN1) '57)
                                       (BIT-OF (RP 'INTEGERP IN1) '58)
                                       (BIT-OF (RP 'INTEGERP IN2) '13)))
                       (AND-LIST (LIST (BIT-OF (RP 'INTEGERP IN1) '57)
                                       (BIT-OF (RP 'INTEGERP IN1) '59)
                                       (BIT-OF (RP 'INTEGERP IN2) '13))))
                 'NIL))
        '(LIST (C '450549
                 'NIL
                 (LIST (AND-LIST (LIST (BIT-OF (RP 'INTEGERP IN1) '51)
                                       (BIT-OF (RP 'INTEGERP IN1) '52)
                                       (BIT-OF (RP 'INTEGERP IN1) '53)))
                       (AND-LIST (LIST (BIT-OF (RP 'INTEGERP IN1) '51)
                                       (BIT-OF (RP 'INTEGERP IN1) '52)
                                       (BIT-OF (RP 'INTEGERP IN2) '19))))
                 'NIL)))||#

;; (c-sum-merge '(list (c '0
;;                        'nil
;;                        (list a b x)
;;                        (list
;;                         (c '0 'nil (list x b c) 'nil))))
;;              '(list (c '0
;;                        (list (s '0
;;                                 (list a b x)
;;                                 (list (c '0 'nil (list x b c) 'nil))))
;;                        (list d e)
;;                        (list (c '0 (list (s '0 (list n m) 'nil)
;;                                          (s '0 (list x b c) 'nil))
;;                                 (list y x) 'nil)))))

;; (i-am-here)

;; (define c/d-merge-fast-aux (pp-arg1 pp-arg2 pp-coughed-from-arg
;;                                     s-arg2 s-coughed-from-arg
;;                                     c-arg
;;                                     clean-flg)
;;   :inline t
;;   :guard (and (consp s-arg2)
;;               (consp (cdr s-arg2)))
;;   (b* (((mv pp-arg pp-arg-cnt1) (pp-sum-merge pp-arg1 pp-arg2))
;;        ((mv pp-arg pp-arg-cnt2) (pp-sum-merge pp-coughed-from-arg pp-arg))
;;        (pp-arg-cnt (+ ;;(expt 2 20) ;;test and remove later when sure...
;;                     pp-arg-cnt1 pp-arg-cnt2))
;;        (s-arg `(list . ,(cddr s-arg2)))
;;        (s-arg (s-sum-merge s-arg s-coughed-from-arg))
;;        ((mv s-coughed s-arg pp-coughed pp-arg)
;;         (clean-c-args s-arg pp-arg pp-arg-cnt clean-flg))
;;        (c-merged
;;         (create-c-instance s-arg pp-arg c-arg)))
;;     (mv s-coughed pp-coughed c-merged)))



(skip-proofs
 (define s-of-s-fix-lst (s-lst c-lst)
   :returns (mv (pp-res-lst-lst rp-term-list-listp
                                :hyp (and (rp-term-listp s-lst)
                                          ;;(rp-termp pp)
                                          (rp-term-listp c-lst)))
                (c-res rp-termp
                       :hyp (and (rp-term-listp s-lst)
                                 ;;(rp-termp pp)
                                 (rp-term-listp c-lst))))
   (if (atom s-lst)
       (mv nil c-lst)
     (b* (((mv pp-lst-lst c-lst) (s-of-s-fix-lst (cdr s-lst) c-lst))
          (cur-s (ex-from-rp/-- (car s-lst))))
       (case-match cur-s
         (('s & cur-pp cur-c)
          (b* (((unless (and (valid-list-termp cur-pp)
                             (valid-list-termp cur-c)))
                ;; below pp-lst-lst should be wrapped by a function!!!!!!
                (mv `(cons ,cur-s ,pp-lst-lst) c-lst))
               
               (cur-c-lst (extract-from-list cur-c))
               ((mv coughed-s coughed-pp-lst-lst c-lst)
                (c-sum-merge cur-c-lst c-lst))
               (pp-lst-lst (append-pp-lst-lsts coughed-pp-lst-lst pp-lst-lst))
               (pp-lst-lst (cons-pp-to-pp-lst-lst cur-pp pp-lst-lst)))
            (case-match coughed-s
              (('list . s-lst)
               (b* (((mv rest-pp-lst-lst c-lst)
                     (s-of-s-fix-lst s-lst c-lst)))
                 (mv (append-pp-lst-lsts rest-pp-lst-lst pp-lst-lst)
                     c-lst)))
              (''nil
               (mv pp-lst-lst c-lst))
              (& (progn$ (cw "Unexpected s format ~p0 ~%" coughed-s)
                         (hard-error 's-of-s-fix-aux "" nil)
                         (mv `(binary-append ,pp-lst-lst ,coughed-s) c))))))
         (''nil
          (mv pp-lst-lst c-lst))
         (&
          (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
                  (hard-error 's-of-s-fix-aux "" nil)
                  (mv `(cons ,cur-s ,pp-lst-lst) c-lst))))))))

(define s-of-s-fix (s pp c-lst &key clean-pp)
  ;; pp is not clean
  ;; returns a new pair of pp and c-lst
  ;; :returns (mv pp c-lst)
  :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                          (rp-termp pp)
                                          (rp-term-listp c-lst)))
               (c-res rp-termp :hyp (and (rp-termp s)
                                         (rp-termp pp)
                                         (rp-term-listp c-lst))))
  (case-match s
    (('list . s-lst)
     (b* (((mv pp-lst-lst c-lst)
           (s-of-s-fix-lst s-lst c-lst))
          (pp-lst-lst (cons-pp-to-pp-lst-lst pp pp-lst-lst))
          ((mv pp-lst &) (pp-lst-sum-merge pp-lst-lst :for-s t))
          (pp (pp-lst-to-pp pp-lst)))
       (mv pp c-lst)))
    (''nil
     (if clean-pp
         (mv (s-fix-args pp) c-lst)
       (mv pp c-lst)))
    (& (progn$ (cw "Unexpected s format ~p0 ~%" s)
               (hard-error 's-of-s-fix "" nil)
               (mv `(binary-append ,pp ,s) c-lst)))))

;; (s-of-s-fix '(list (s '0  (list (binary-and a1 a1) (binary-and a2 a2))
;;                        (list (c '0
;;                                 'nil
;;                                 (list a b x)
;;                                 (list
;;                                  (c '0 'nil (list x b c) 'nil)))))
;;                     (s '0 (list (binary-and a1 a1) (binary-and a3 a3))
;;                        (list (c '0
;;                                  (list (s '0
;;                                           (list a b x)
;;                                           (list (c '0 'nil (list x b c) 'nil))))
;;                                  (list d e)
;;                                  (list (c '0 (list (s '0 (list n m) 'nil)
;;                                                    (s '0 (list x b c) 'nil))
;;                                           (list y x) 'nil))))))
;;             '(list (binary-and a2 a2) (binary-and a3 a3))
;;             ''nil)

#|(acl2::defines
 c-merge
 :flag-defthm-macro defthm-c-merge
 :flag-local nil
 :prepwork ((local
             (defthm lemma1
               (implies (and (rp-termp x)
                             (rp-termp y)
                             (rp-termp z))
                        (rp-termp
                         (list 'd
                               (list 'rp ''evenpi
                                     (list 'd-sum x y z)))))
               :hints (("goal"
                        :in-theory (e/d (is-rp rp-termp) ())))))

            (local
             (defthm lemma2
               (implies (and (rp-termp x)
                             (rp-termp y))
                        (and (rp-termp
                              (list 'binary-sum x y))
                             (rp-termp (list 'binary-append x y))
                             (rp-termp (list 'cons x y))
                             (rp-termp
                              (list 'list
                                    (list '--
                                          (list 's x y))))))
               :hints (("goal"
                        :in-theory (e/d (is-rp rp-termp) ())))))

            (local
             (defthm lemma3
               (implies (and (rp-term-listp x))
                        (and
                         (rp-termp (cons 'list x))
                         (rp-termp (cons 'c x))
                         (rp-termp (cons 's x))))
               :hints (("goal"
                        :in-theory (e/d (is-rp rp-termp) ())))))

            (local
             (defthm lemma4
               (rp-termp
                (list 'list
                      (list 'quote x)))
               :hints (("goal"
                        :in-theory (e/d (rp-termp is-rp) ())))))

            (local
             (defthm lemma5
               (implies (and (consp lst)
                             (rp-term-listp lst))
                        (rp-term-listp (cdr lst)))
               :hints (("Goal"
                        :expand (rp-term-listp lst)
                        :in-theory (e/d () ())))))

            (local
             (defthm lemma6
               (implies (and (rp-termp term)
                             (consp term)
                             (equal (car term) 'list))
                        (rp-term-listp (cdr term)))))

            (local
             (defthm lemma7
               (implies
                (can-c-merge-fast single-c1 single-c2)
                (and (consp
                      (mv-nth
                       0
                       (get-c-args
                        (mv-nth 1
                                (swap-single-cs single-c1 single-c2
                                           (equal (can-c-merge-fast single-c1 single-c2)
                                                  1))))))
                     (consp
                      (cdr (mv-nth
                            0
                            (get-c-args
                             (mv-nth 1
                                     (swap-single-cs single-c1 single-c2
                                                (equal (can-c-merge-fast single-c1 single-c2)
                                                       1)))))))
                     (equal (car (mv-nth
                                  0
                                  (get-c-args
                                   (mv-nth 1
                                           (swap-single-cs single-c1 single-c2
                                                      (equal (can-c-merge-fast single-c1 single-c2)
                                                             1))))))
                            'list)))
               :hints (("goal"
                        :in-theory (e/d (can-c-merge-fast
                                         can-c-merge-fast-aux
                                         get-c-args
                                         swap-single-cs) ())))))

            (local
             (defthm natp-lemma1
               (implies (and (natp x)
                             (natp y))
                        (natp (+ x y)))))

            (local
             (defthm natp-lemma2
               (implies (natp x)
                        (acl2-numberp x))))

            (local
             (in-theory (e/d (;;remove-s-from-for-fast-merge
                              c/d-merge-fast-aux)
                             (falist-consistent
                              rp-termp
                              natp)))))

 (define s-of-s-fix-aux ((s-lst)
                         (pp)
                         (c)
                         (limit natp))
   :measure (nfix limit)
   :returns (mv (pp-res rp-termp
                        :hyp (and (rp-term-listp s-lst)
                                  (rp-termp pp)
                                  (rp-termp c)))
                (c/d-res rp-termp "A dirty c/d"
                         :hyp (and (rp-term-listp s-lst)
                                   (rp-termp pp)
                                   (rp-termp c))))
   ;; iterate on s,
   ;; extract its insides and merge them with pp and c/d
   (cond
    ((zp limit)
     (progn$ (cw "Limit exhausted! ~%")
             (hard-error 's-of-s-fix-aux "" nil)
             (mv `(binary-append (list . ,s-lst) ,pp)
                 c)))

    ((atom s-lst)
     (mv pp c))
    (t
     (b* (((mv pp c) (s-of-s-fix-aux (cdr s-lst) pp c (1- limit)))
          (cur-s (ex-from-rp/-- (car s-lst))))
       (case-match cur-s
         (('s pp-cur c/d-cur)
          (b* (((mv s-coughed pp-coughed c)
                (c-merge c c/d-cur nil (1- limit)))
               ((mv pp &) (pp-sum-merge pp pp-cur))
               ((mv pp &) (pp-sum-merge pp pp-coughed)))
            (case-match s-coughed
              (('list . s-lst)
               (s-of-s-fix-aux s-lst pp c (1- limit)))
              (''nil
               (mv pp c))
              (& (progn$ (cw "Unexpected s format ~p0 ~%" s-coughed)
                         (hard-error 's-of-s-fix-aux "" nil)
                         (mv `(binary-append ,pp ,s-coughed) c))))))
         (''nil
          (mv pp c))
         (&
          (progn$ (cw "Unexpected s term ~p0 ~%" cur-s)
                  (hard-error 's-of-s-fix-aux "" nil)
                  (mv `(cons ,cur-s ,pp) c))))))))

 (define s-of-s-fix ((s)
                     (pp)
                     (c)
                     (limit natp))
   ;; pp is expected to be dirty wrt s
   ;; c/d is expected to be clean.
   ;; remove nested s instances for (s (+ s pp c/d))
   :returns (mv (pp-res rp-termp :hyp (and (rp-termp s)
                                           (rp-termp pp)
                                           (rp-termp c)))
                (c/d-res rp-termp :hyp (and (rp-termp s)
                                            (rp-termp pp)
                                            (rp-termp c))))
   :measure (nfix limit)
   (cond
    ((zp limit)
     (progn$ (cw "Limit exhausted! ~%")
             (hard-error 's-of-s-fix "" nil)
             (mv `(binary-append ,pp ,s) c)))
    (t
     (case-match s
       (('list . s-lst)
        (b* (((mv pp c)
              (s-of-s-fix-aux s-lst pp c (1- limit)))
             ((mv s-coughed pp-coughed c) (c-cough c))
             ((mv pp &) (pp-sum-merge pp pp-coughed))
             (pp (s-fix-args pp)))
          (if (equal s-coughed ''nil)
              (mv pp c)
            (s-of-s-fix s-coughed pp c (1- limit)))))
       (''nil
        (mv (s-fix-args pp) c))
       (& (progn$ (cw "Unexpected s format ~p0 ~%" s)
                  (hard-error 's-of-s-fix "" nil)
                  (mv `(binary-append ,pp ,s) c)))))))

 (define get-extra-s-arg ((s-arg)
                          (pp-arg)
                          (c-arg)
                          (limit natp))
;:inline t
   :measure (nfix limit)
   :returns (extra-s-arg rp-termp
                         :hyp (and (rp-termp s-arg)
                                   (rp-termp pp-arg)
                                   (rp-termp c-arg)))
   (cond
    ((zp limit)
     (progn$ (cw "Limit exhausted! ~%")
             (hard-error 'get-extra-s-arg "" nil)
             `(list (-- (s (binary-append ,s-arg ,pp-arg) ,c-arg)))))
    (t (b* (((mv s-pp s-c/d)
             (s-of-s-fix s-arg pp-arg c-arg (1- limit)))
            (res
             (cond ((and (quotep s-pp)
                         (quotep s-c/d)
                         (consp (cdr s-pp))
                         (consp (cdr s-c/d)))
                    (b* ((res (-- (s (unquote s-pp)
                                     (unquote s-c/d)))))
;(if (equal res 0)
; ''nil
                      `(list ',res)
;)
                      ))
                   ((extra-s-can-be-pp s-pp s-c/d)
                    `(list (-- ,(cadr s-pp))))
                   (t
                    `(list (-- (s ,s-pp ,s-c/d)))))))
         res))))

 (define c-merge ((single-c1)
                    (single-c2)
                    (clean-flg booleanp)
                    (limit natp))
   ;; merges two c/d terms (c/d1 and c/d2)
   ;; returns coughed-s, coughed-pp and merged c/d
   :measure (nfix limit)
   :returns (mv (s-coughed rp-termp
                           :hyp (and (rp-termp single-c1)
                                     (rp-termp single-c2)))
                (pp-coughed rp-termp
                            :hyp (and (rp-termp single-c1)
                                      (rp-termp single-c2)))
                (c/d-merged rp-termp
                            :hyp (and (rp-termp single-c1)
                                      (rp-termp single-c2))))

   (b* (((when (zp limit))
         (progn$ (cw "Limit reached!~&")
                 (hard-error 'c-merge "" nil)
                 (mv ''nil ''nil `(binary-sum ,single-c1 ,single-c2))))
        (single-c1 (ex-from-rp single-c1))
        (single-c2 (ex-from-rp single-c2))
        ((when (equal single-c1 ''0))
         (mv ''nil ''nil single-c2))
        ((when (equal single-c2 ''0))
         (mv ''nil ''nil single-c1))
        ;; check if can be merged without converting to d.
        (c-merge-fast (can-c-merge-fast single-c1 single-c2))
        ((mv single-c1 single-c2) ;; maybe swap them
         (swap-single-cs single-c1 single-c2 (equal c-merge-fast 1)))

        ((mv s-arg1 pp-arg1 c-arg1 type1) (get-c-args single-c1))
        ((mv s-arg2 pp-arg2 c-arg2 type2) (get-c-args single-c2))
        ((when (or (not type1)
                   (not type2)))
         (progn$ (cw "c/d-merge error. Terms are not instances of c or d. ~%")
                 (cw "Term1 = ~p0 ~%" single-c1)
                 (cw "Term2 = ~p0 ~%" single-c2)
                 (hard-error 'c-merge "" nil)
                 (mv ''nil ''nil `(binary-sum ,single-c1 ,single-c2))))

        ((mv s-coughed-from-arg pp-coughed-from-arg c-arg)
         (c-merge c-arg1 c-arg2 t (1- limit)))

        )
     (cond
      (c-merge-fast
       (c/d-merge-fast-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                           s-arg2 s-coughed-from-arg
                           c-arg
                           clean-flg))
      (t
       (b* ((c/d1-is-c (eq type1 'c))
            (c/d2-is-c (eq type2 'c))
            (extra-s-arg1 (and c/d1-is-c
                               (get-extra-s-arg s-arg1 pp-arg1
                                                c-arg1 (1- limit))))
            (extra-s-arg2 (and c/d2-is-c
                               (get-extra-s-arg s-arg2 pp-arg2
                                                c-arg2 (1- limit)))))
         (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                             s-arg1 s-arg2 s-coughed-from-arg
                             extra-s-arg1
                             extra-s-arg2
                             c-arg
                             clean-flg
                             c/d1-is-c
                             c/d2-is-c)))))))||#

;; (define c/d-merge-aux (c/d1-is-c
;;                        c/d2-is-c
;;                        extra-s-arg1
;;                        extra-s-arg2

(define quote-all (lst)
  :returns (res rp-term-listp)
  (if (atom lst)
      nil
    (cons (list 'quote (car lst))
          (quote-all (cdr lst)))))

(local
 (in-theory (disable
             pp-term-p)))

(define good-4vec-term-p (term)
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig term)
       (term (ex-from-rp term)))
    (case-match term
      (('sv::4vec-bitand x y)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)))
      (('sv::4vec-bitxor x y)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)))
      (('sv::4vec-bitor x y)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)))
      (('sv::4vec-? x y z)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)
            (good-4vec-term-p z)))
      (('sv::4vec-?* x y z)
       (and (good-4vec-term-p x)
            (good-4vec-term-p y)
            (good-4vec-term-p z)))
      (('svl::4vec-bitnot$ ''1 x)
       (and (good-4vec-term-p x)
            ))
      (('svl::bits num start size)
       (and (equal size ''1)
            (case-match num
              (('rp ''integerp x)
               (atom (ex-from-rp x))))
            (case-match start
              (('quote x)
               (natp x)))))
      (('sv::4vec-fix$inline x)
       (and (good-4vec-term-p x)))
      (('sv::3vec-fix x)
       (and (good-4vec-term-p x)))
      (& (pp-term-p orig)))))

(define 4vec->pp-term ((term good-4vec-term-p))
  :returns (pp-term)
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :guard-hints (("Goal"
                 :in-theory (e/d (good-4vec-term-p) ())))
  (b* ((orig term)
       (term (ex-from-rp term)))
    (case-match term
      (('sv::4vec-bitand x y)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y)))
         `(binary-and ,n1 ,n2)))
      (('sv::4vec-bitxor x y)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y)))
         `(binary-xor ,n1 ,n2)))
      (('sv::4vec-bitor x y)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y)))
         `(binary-or ,n1 ,n2)))
      (('sv::4vec-? x y z)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y))
            (n3 (4vec->pp-term z)))
         `(binary-? ,n1 ,n2 ,n3)))
      (('sv::4vec-?* x y z)
       (b* ((n1 (4vec->pp-term x))
            (n2 (4vec->pp-term y))
            (n3 (4vec->pp-term z)))
         `(binary-? ,n1 ,n2 ,n3)))
      (('svl::4vec-bitnot$ ''1 x)
       `(binary-not ,(4vec->pp-term x)))
      (('svl::bits num start &)
       `(bit-of ,num ,start))
      (('sv::4vec-fix$inline x)
       (4vec->pp-term x))
      (('sv::3vec-fix x)
       (4vec->pp-term x))
      (& orig)))
  ///

  (acl2::defret
   rp-termp-of--<fn>
   (rp-termp pp-term)
   :hyp (rp-termp term)

   :hints (("Goal"
            :induct (4vec->pp-term term)
            :do-not-induct t
            :expand ((:free (rest) (RP-TERMP (cons 'BIT-OF rest)))
                     (:free (rest) (RP-TERMP (cons 'quote rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-not rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-and rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-or rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-? rest)))
                     (:free (rest) (RP-TERMP (cons 'binary-xor rest))))
            :in-theory (e/d () (rp-termp
                                falist-consistent
                                pp-term-p)))))

  #|(local
  (defthm lemma1
  (IMPLIES (AND (PP-HAS-BITP-RP TERM))
  (equal (PP-TERM-P TERM)
  (B* ((ORIG TERM) (TERM (EX-FROM-RP TERM)))
  (CASE-MATCH TERM
  (('BINARY-AND X Y)
  (AND (PP-TERM-P X) (PP-TERM-P Y)))
  (('BINARY-OR X Y)
  (AND (PP-TERM-P X) (PP-TERM-P Y)))
  (('BINARY-XOR X Y)
  (AND (PP-TERM-P X) (PP-TERM-P Y)))
  (('BINARY-? X Y Z)
  (AND (PP-TERM-P X)
  (PP-TERM-P Y)
  (PP-TERM-P Z)))
  (('BINARY-NOT X) (AND (PP-TERM-P X)))
  (('BIT-OF & &) T)
  (''1 T)
  (& (PP-HAS-BITP-RP ORIG))))))
  :hints (("goal"
  :do-not-induct t
  :expand (pp-term-p term)
  :in-theory (e/d () (pp-has-bitp-rp))))))||#

  (acl2::defret
   pp-term-p-of--<fn>
   :hyp (good-4vec-term-p term)
   (pp-term-p pp-term)
   :hints (("Goal"
            :induct (4vec->pp-term term)
            :do-not-induct t
            :expand ((:free (x y) (pp-term-p (cons x y)))
                     (:free (x y) (is-rp (cons x y))))
            :in-theory (e/d (good-4vec-term-p) (rp-termp pp-term-p))))))

(define extract-new-sum-element (term acc)
  :measure (cons-count term)
  :prepwork
  ((local
    (in-theory (enable measure-lemmas))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('c & & & &)
       (cons term-orig acc))
      (('s & & &)
       (cons term-orig acc))
      (('c-res & & &)
       (cons term-orig acc))
      (('sum-list &)
       (cons term-orig acc))
      (('and-list & &)
       (cons term-orig acc))
      (('binary-sum a b)
       (b* ((acc (extract-new-sum-element a acc))
            (acc (extract-new-sum-element b acc)))
         acc))
      (('quote x)
       (b* ((x (ifix x)))
         (cond ((natp x) (append (repeat x ''1) acc))
               (t (append (repeat (- x) ''-1) acc)))))
      (&
       (cond ((good-4vec-term-p term)
              (cons term-orig acc))
             (t
              (progn$
               (hard-error 'extract-new-sum-element
                           "Unexpexted term: ~p0 ~%"
                           (list (cons #\0 term-orig)))
               (cons term-orig acc))))))))

(define extract-new-sum-consed (term)
  :measure (cons-count term)
  :prepwork
  ((local
    (in-theory (enable measure-lemmas
                       ex-from-rp-loose))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('cons x rest)
       (b* ((acc (extract-new-sum-consed rest)))
         (extract-new-sum-element x acc)))
      (('quote x)
       (if (consp x)
           (b* ((acc (extract-new-sum-consed (list 'quote (cdr x)))))
             (extract-new-sum-element (list 'quote (car x)) acc))
         (extract-new-sum-element term-orig nil)))
      (&
       (extract-new-sum-element term-orig nil)))))

(define new-sum-merge-aux (sum-lst)

  (b* (((when (atom sum-lst))
        (mv ''nil nil nil))
       ((mv s pp-lst-lst c-lst)
        (new-sum-merge-aux (cdr sum-lst)))
       (term-orig (car sum-lst))
       (term (ex-from-rp-loose term-orig)))
    (case-match term
      (('c & & & &)
       (b* (((mv coughed-s coughed-pp-lst-lst c-lst)
             (c-sum-merge-lst term-orig c-lst ))
            (s (s-sum-merge s coughed-s))
            (pp-lst-lst (append-pp-lst-lsts coughed-pp-lst-lst pp-lst-lst)))
         (mv s pp-lst-lst c-lst)))
      (('s & & &)
       (b* ((s (s-sum-merge s (create-list-instance
                               (list term-orig)))))
         (mv s pp-lst-lst c-lst)))
      (('c-res s-arg pp-arg c-arg)
       (b* (((mv coughed-s coughed-pp-lst-lst c-lst)
             (c-sum-merge-lst c-arg c-lst))
            (s (s-sum-merge s s-arg))
            (s (s-sum-merge s coughed-s))
            (pp-lst-lst (cons-pp-to-pp-lst-lst pp-arg pp-lst-lst))
            (pp-lst-lst (append-pp-lst-lsts coughed-pp-lst-lst pp-lst-lst)))
         (mv s pp-lst-lst c-lst)))
      (('sum-list arg-pp)
       (b* ((pp-lst-lst (cons-pp-to-pp-lst-lst arg-pp  pp-lst-lst)))
         (mv s pp-lst-lst c-lst)))
      (('and-list & &)
       (b* ((pp-lst-lst (pp-cons (list term)  pp-lst-lst)))
         (mv s pp-lst-lst c-lst)))
      (('quote &)
       (b* ((pp-lst-lst (pp-cons (list term)  pp-lst-lst)))
         (mv s pp-lst-lst c-lst)))
      (& (cond ((good-4vec-term-p term)
                (b* ((term (4vec->pp-term term-orig))
                     (pp-lst (pp-flatten term nil))
                     (pp-lst-lst (pp-cons pp-lst pp-lst-lst)))
                  (mv s pp-lst-lst c-lst)))
               (t
                (progn$ (hard-error 'new-sum-merge-aux
                                    "Unexpected term ~p0 ~%"
                                    (list (cons #\0 term-orig)))
                        (mv `(cons ,term-orig ,s)
                            pp-lst-lst
                            c-lst))))))))

(define new-sum-merge (term &key cough-pp)
  (b* ((sum-lst (extract-new-sum-consed term))
       ;(sum-lst (hons-copy sum-lst))
       ((mv s pp-lst-lst c-lst)
        (new-sum-merge-aux sum-lst))
       ((mv pp-lst coughed-pp-lst)
        (pp-lst-sum-merge pp-lst-lst :for-s t :for-c cough-pp)))
    (mv s pp-lst coughed-pp-lst c-lst)))

;; (progn
(define well-formed-new-sum (term)
  :returns (res booleanp)
  (case-match term
    (('cons x rest)
     (b* ((x (ex-from-rp-loose x))
          (rest-res (well-formed-new-sum rest)))
       (cond ((good-4vec-term-p x)
              rest-res)
             ((case-match x (('and-list & &) t))
              rest-res)
             ((case-match x (('s & & &) t))
              rest-res)
             ((case-match x (('c & & & &) t))
              rest-res)
             #|((case-match x (('d ('rp ''evenpi ('d-sum & & &))) t))
             rest-res)||#
             ((case-match x (('c-res & & &) t))
              rest-res)
             ((case-match x (('sum-list &) t))
              rest-res)
             ((equal x ''0)
              rest-res)
             (t
              nil))))
    (('quote x)
     (integer-listp x))
    (& nil)))

(defmacro mv-nth-0-of-2 (term)
  `(b* (((mv x &) ,term))
     x))

;;   (define new-sum-merge-aux ((term well-formed-new-sum))
;;     ;; a term to be summed that came from rewrite rules e.g full-adder to s-spec
;;     ;; and c-spec

;;     ;; expected input should be a list of s/c/d/c-res terms
;;     ;; goal is to sum them and return (mv s pp c/d)
;;     :returns (mv s-res pp c-raw)
;;     ;;(s-res rp-termp
;;     ;;        :hyp (rp-termp term))
;;     ;; (pp rp-termp
;;     ;;     :hyp (rp-termp term))
;;     ;; (c/d rp-termp
;;     ;;      :hyp (rp-termp term)))
;;     :prepwork ((local
;;                 (in-theory (e/d (well-formed-new-sum)
;;                                 (rp-termp)))))
;;     (case-match term
;;       (('cons x rest)
;;        (b* (((mv s-rest pp-rest c-rest)
;;              (new-sum-merge-aux rest))
;;             (?limit (expt 2 40))
;;             (x-orig x)
;;             (x (ex-from-rp-loose x)))
;;          (cond ((good-4vec-term-p x) ;; (pp-term-p x)
;;                 (b* ((x (4vec->pp-term x)))
;;                   (mv s-rest
;;                       (mv-nth-0-of-2 (pp-sum-merge (pp-flatten x nil) pp-rest))
;;                       c-rest)))
;;                (t
;;                 (case-match x
;;                   (('s & & &)
;;                    ;;((case-match x (('s & & &) t))
;;                    (mv (s-sum-merge (create-list-instance (list x-orig)) s-rest)
;;                        pp-rest
;;                        c-rest))
;;                   (('c & & & &)
;;                    ;;((case-match x (('c & & & &) t))
;;                    (b* (((mv coughed-s coughed-pp-lst-lst c)
;;                          (c-sum-merge c-rest (create-list-instance (list x-orig))))
;; ;(c-merge c-rest x-orig nil limit)
;; ;(& (well-merged-c-p arg-merged-c :message "pos. 4"))
;;                         ((mv pp-lst &)
;;                          (pp-lst-sum-merge (cons-pp-to-pp-lst-lst pp-rest
;;                                                                   coughed-pp-lst-lst)))
;;                         (pp (create-list-instance pp-lst))
;;                         )
;;                      (mv (s-sum-merge s-rest coughed-s)
;;                          pp ;;(mv-nth-0-of-2 (pp-sum-merge pp-rest coughed-pp))
;;                          c)))
;;                   #|((case-match x (('d ('rp ''evenpi ('d-sum & & &))) t))
;;                   (b* (((mv s pp c) ; ;
;;                   (c-merge c-rest x-orig nil limit))) ; ;
;;                   (mv (s-sum-merge s-rest s) ; ;
;;                   (mv-nth-0-of-2 (pp-sum-merge pp-rest pp)) ; ;
;;                   c)))||#
;;                   (('c-res & & &)
;;                    ;; ((case-match x (('c-res & & &) t))
;;                    (b* (((mv s pp-lst-lst c)
;;                          (c-sum-merge c-rest (create-list-instance (list (cadddr
;;                                                                           x)))))
;; ;(& (well-merged-c-p arg-merged-c :message "pos. 5"))

;;                         (pp-lst-lst (cons-pp-to-pp-lst-lst pp-rest pp-lst-lst))
;;                         (pp-lst-lst (cons-pp-to-pp-lst-lst (caddr x) pp-lst-lst))
;;                         ((mv pp-lst &)
;;                          (pp-lst-sum-merge pp-lst-lst))
;;                         (pp (create-list-instance pp-lst))

;;                         )
;;                      (mv (s-sum-merge
;;                           s-rest
;;                           (s-sum-merge s (cadr x)))
;;                          pp
;;                          #|(mv-nth-0-of-2 (pp-sum-merge
;;                          pp-rest ; ;
;;                          (mv-nth-0-of-2 (pp-sum-merge pp (caddr x)))))||#
;;                          c)))
;;                   (('sum-list ('list . &))
;; ;((case-match x (('sum-list ('list . &)) t))
;;                    (mv s-rest
;;                        (mv-nth-0-of-2 (pp-sum-merge pp-rest (cadr x)))
;;                        c-rest))
;;                   (''0
;;                    ;;((equal x ''0)
;;                    (mv s-rest pp-rest c-rest))
;;                   (&
;;                    (progn$ (cw "not well-formed term for new sums= ~p0 ~%" x)
;;                            (mv ''nil ''nil ''0))))))))
;;       (''nil
;;        (mv ''nil ''nil ''nil))
;;       (('quote x)
;;        (mv ''nil (create-list-instance  (quote-all x)) ''nil))
;;       (& (progn$ (cw "not well-formed term for new sums= ~p0 ~%" term)
;;                  ;; should never happen
;;                  (hard-error 'new-sum-merge-aux "" nil)
;;                  (mv ''nil ''nil ''nil))))
;;     ///
;;     (local
;;      (defthm lemma1
;;        (implies (and (rp-termp x))
;;                 (rp-termp (list 'list x)))
;;        :hints (("Goal"
;;                 :in-theory (e/d (rp-termp
;;                                  is-rp) ())))))

;;     (local
;;      (defthm lemma2
;;        (implies (and (rp-term-listp x))
;;                 (rp-termp (cons 'list x)))
;;        :hints (("Goal"
;;                 :in-theory (e/d (rp-termp
;;                                  is-rp) ())))))

;;     (acl2::defret rp-termp-of--<fn>
;;                   :hyp (rp-termp term)
;;                   (and (rp-termp s-res)
;;                        (rp-termp pp)
;;                        (rp-termp c-raw))
;;                   :hints (("Goal"
;;                            :induct (new-sum-merge-aux term)
;;                            :do-not-induct t
;;                            :in-theory (e/d () (rp-termp
;;                                                (:DEFINITION PP-TERM-P)))))))

;;   (define new-sum-merge ((term well-formed-new-sum))
;;     :returns (mv (s-res rp-termp :hyp (rp-termp term))
;;                  (pp rp-termp :hyp (rp-termp term))
;;                  (c rp-termp :hyp (rp-termp term)))
;;     :inline t
;;     (b* (((mv s pp c)
;;           (new-sum-merge-aux term))
;;          ;;(s (s-fix-args s))
;;          )
;;       (mv s pp c))))

(progn
  (define light-pp-term-p (term)
    :inline t
    (or
     (pp-has-bitp-rp term)
     (b* ((term (ex-from-rp term)))
       (case-match term
         (('binary-not &)
          t)
         (('binary-and & &)
          t)
         (('binary-or & &)
          t)
         (('binary-xor & &)
          t)
         (('binary-? & & &)
          t)
         (('bit-of & &)
          t)))))

  (define light-pp-term-list-p (lst)
    (if (atom lst)
        (equal lst nil)
      (and (light-pp-term-p (car lst))
           (light-pp-term-list-p (cdr lst)))))

  (define quarternaryp-sum-aux ((term well-formed-new-sum))
    :returns (mv (res natp
                      :rule-classes (:rewrite :type-prescription))
                 (valid booleanp))
    :verify-guards nil
    :prepwork ((local
                (in-theory (disable natp)))
               (local
                (defthm lemma1
                  (implies (NAT-LISTP lst)
                           (natp (sum-list lst)))
                  :hints (("Goal"
                           :induct (sum-list lst)
                           :do-not-induct t
                           :in-theory (e/d (sum-list
                                            nat-listp
                                            sum)
                                           (+-is-sum))))
                  :rule-classes (:type-prescription :rewrite))))
    (case-match term
      (('cons x rest)
       (b* (((mv rest-sum valid) (quarternaryp-sum-aux rest))
            ((unless valid)
             (mv 0 nil))
            (x-orig x)
            (x (ex-from-rp-loose x)))
         (cond ((light-pp-term-p x)
                (mv (1+ rest-sum) t))
               ((case-match x (('s & & &) t))
                (mv (1+ rest-sum) t))
               ((case-match x-orig (('rp ''bitp ('c & & & &)) t))
                (mv (1+ rest-sum) t))
               ((case-match x-orig (('and-list & &) t))
                (mv (1+ rest-sum) t))
               ((case-match x-orig (('rp ''bitp ('c-res & & &)) t))
                (mv (1+ rest-sum) t))
               ((equal x ''0)
                (mv rest-sum t))
               ((equal x ''1)
                (mv (1+ rest-sum) t))
               #|((case-match x (('quote &) t))
               (cond ((natp (cadr x)) ;
               (mv (+ (cadr x) rest-sum) t)) ;
               (t ;
               (mv 0 nil))))||#
               ((case-match x (('sum-list ''nil) t))
                (mv rest-sum t))
               ((case-match x (('sum-list ('list . &)) t))
                (if (light-pp-term-list-p (cdr (cadr x)))
                    (mv (+ rest-sum (len (cdr (cadr x)))) t)
                  (mv 0 nil)))
               (t
                (mv 0 nil)))))
      (''nil
       (mv 0 t))
      (('quote x)
       (cond ((natp x)
              (mv x t))
             ((nat-listp x)
              (mv (sum-list x) t))
             (t (mv 0 nil))))
      (& (mv 0 nil)))
    ///
    (verify-guards quarternaryp-sum-aux
      :hints (("Goal"
               :in-theory (e/d (WELL-FORMED-NEW-SUM) ())))))

  (define quarternaryp-sum ((sum well-formed-new-sum))
    :returns (res booleanp)
    (b* (((mv res valid)
          (quarternaryp-sum-aux sum)))
      (and valid
           (quarternaryp res)))))

(define c-spec-meta-aux (s pp-lst coughed-pp-lst c-lst quarternaryp)
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-term-listp pp-lst)
                          (rp-term-listp c-lst)))
  :prepwork ((local
              (in-theory (disable natp))))
  (b* ( #|((mv s-coughed pp-coughed c)
       (c-cough c))||#
       #|(s (s-sum-merge s-coughed s))||#
       #|((mv pp pp-limit) (pp-sum-merge pp-coughed pp))||#

       #|(a '((in1 . 255) (in2 . 255)))||#
       #|(in-term `(c-spec (list (sum-list ,s) (sum-list ,pp) (sum-list ,c))))||#
       #|(bad-one nil)||#;(equal ''12659579451152 (cadr (cadr c))))

       #|(- (and bad-one
       (cw "processing bad one now... ~%")))||#
       #|(val1 (m-eval in-term a))||#

       ((mv s-coughed s)
        (c-fix-s-args s))
       #|((mv pp-coughed pp)
       (c-fix-pp-args pp (expt 2 30)))||#

       #|(- (and bad-one
       (cw "s-coughed:~p0~%pp-coughed:~p1~%pp:~p2~%s:~p3~%c:~p4~%~%"
       s-coughed  pp-coughed  pp  s c)))||#

       (c-term
        (create-c-instance s
                           (pp-lst-to-pp pp-lst)
                           (create-list-instance c-lst)))
       (pp-coughed (pp-lst-to-pp coughed-pp-lst))

       #|(- (and bad-one
       (cw "Created c-term:~p0 ~%"
       c-term)))||#

       #|(cond
       ((and (equal s ''nil) ; ;
       (equal c/d ''0) ; ;
       (case-match pp (('list ('binary-and & &)) t))) ; ;
       ''0) ; ;
       (t ; ;
       `(c ,s ,pp ,c/d)))||#

       #|(- (and (not (pp-orderedp pp))
       (cw "This pp on c-spec-meta-aux is not ordered! ~p0 ~%" ; ; ; ;
       pp)))||#
       #|(- (and (not (pp-orderedp pp-coughed))
       (cw "This pp-coughed on c-spec-meta-aux is not ordered! ~p0 ~%" ; ; ; ;
       pp-coughed)))||#
       (result (cond ((and (equal s-coughed ''nil)
                           (equal pp-coughed ''nil))
                      (if (quotep c-term)
                          c-term
                        (if quarternaryp
                            `(rp 'bitp ,c-term)
                          c-term)))
                     (t
                      (b* ((res `(c-res ,s-coughed ,pp-coughed ,c-term)))
                        (if quarternaryp
                            `(rp 'bitp ,res)
                          res)))))

       #|(val2 (m-eval result a))||#
       #|(- (or (equal val1 val2)
       (hard-error 'c-spec-meta-aux
       "Input and output vals are not the same!~p0~%in:~p1~%out:~p2~%"
       (list (cons #\0 (list val1 val2))
       (cons #\1 in-term)
       (cons #\2 result)))))||#
       )
    result))

(define c-spec-meta (term)
  ;; term should be `(c-spec well-formed-new-sum)
  ;; well-formed-new-sum should be given to new-sum-merge-aux
  ;; result of new-sum-merge-aux (mv s pp c/d)
  ;; this should be made into a c term and get  coughed-out
  ;; then returns `(c-res ,s-coughed ,pp-coughed ,c/d-cleaned)

  ;; later try to attach bitp to the returned value.
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  (b* ((result
        (case-match term
          (('c-spec sum)
           (if (well-formed-new-sum sum)
               (b* ((;;(mv s pp c)
                     (mv s pp-lst coughed-pp-lst c-lst)
                     (new-sum-merge sum :cough-pp t))
                    (quarternaryp (quarternaryp-sum sum))

                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#)
                 (c-spec-meta-aux s pp-lst coughed-pp-lst c-lst quarternaryp))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (& term))))
    (mv result t)))

;; (c-spec-meta `(c-spec (cons (binary-and (bit-of a 0) (bit-of b 0))
;;                             (cons (binary-or (binary-and (bit-of a 0) (bit-of b 0))
;;                                              (binary-and (bit-of a 0) (bit-of b 0)))
;;                                   'nil))))

(define s-spec-meta-aux (s pp-lst c-lst)
  :returns (res rp-termp
                :hyp (and (rp-termp s)
                          (rp-term-listp pp-lst)
                          (rp-term-listp c-lst)))
  (b* (#|(a '((in1 . 255) (in2 . 255)))||#
       #|(val1 (m-eval `(s-spec (list (sum-list ,s) (sum-list ,pp) (sum-list ,c))) a))||#

       (?limit (expt 2 40))
       (pp (pp-lst-to-pp pp-lst))
       ((mv pp c-lst)
        (case-match s
          (''nil
           (mv pp c-lst)
           #|(b* (((mv s-coughed pp-coughed c) (c-cough c))
           ((mv pp &) (pp-sum-merge pp pp-coughed))) ;
           (s-of-s-fix s-coughed pp c limit))||#)
          (&
           (s-of-s-fix s pp c-lst))))
       ;;(pp (s-fix-args pp))
       #|(- (and (not (pp-orderedp pp))
       (cw "This pp in s-spec-meta-aux is not ordered! ~p0 ~%" ; ;
       pp)))||#
       (c (create-list-instance c-lst))
       (res (create-s-instance pp c))
       #|(val2 (m-eval res a))||#
       #|(- (or (equal val1 val2)
       (hard-error 's-spec-meta-aux
       "Input and output vals are not the same! ~p0 ~%"
       (list (cons #\0 (list val1 val2))))))||#)
    res))

(define s-spec-meta (term)

  ;; term should be `(s-pec well-formed-new-sum)
  ;; well-formed-new-sum should be given to new-sum-merge-aux
  ;; result of new-sum-merge-aux (mv s pp c/d)
  ;; s-of-s-fix should be called on s
  ;; result should be returned `(s pp-new c/d-new)

  ;; later try to attach bitp to the returned value.
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  (b* ((result (case-match term
                 (('s-spec sum)
                  (cond ((well-formed-new-sum sum)
                         (b* (((mv s pp-lst & c-lst);;(mv s pp c)
                               (new-sum-merge sum :cough-pp nil)))
                           (s-spec-meta-aux s pp-lst c-lst)))
                        (t
                         (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                                 term))))
                 (& term))))
    (mv result t)))

(define s-c-spec-meta (term)
  :returns (mv (res rp-termp
                    :hyp (rp-termp term))
               (dont-rw dont-rw-syntaxp))
  :prepwork ((local
              (defthm lemma1
                (IS-RP (LIST 'RP ''BITP x))
                :hints (("Goal"
                         :in-theory (e/d (is-rp) ()))))))
  (b* ((result
        (case-match term
          (('s-c-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp-lst coughed-pp-lst c-lst);;(mv s pp c)
                     (new-sum-merge sum :cough-pp t))
                    (quarternaryp (quarternaryp-sum sum))

                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#
                    (s-res (s-spec-meta-aux s pp-lst c-lst))
                    (c-res (c-spec-meta-aux s pp-lst coughed-pp-lst c-lst quarternaryp))
                    (res `(cons ,s-res (cons ,c-res 'nil)))
                    #|(- (if (search-pattern res)
                    (cw "pattern found s-c-spec-meta ~%")
                    nil))||#)
                 res)
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('c-s-spec sum)
           (if (well-formed-new-sum sum)
               (b* (((mv s pp-lst coughed-pp-lst c-lst);;(mv s pp c)
                     (new-sum-merge sum :cough-pp t))
                    (quarternaryp (quarternaryp-sum sum))
                    (s-res (s-spec-meta-aux s pp-lst c-lst))
                    (c-res (c-spec-meta-aux s pp-lst coughed-pp-lst c-lst quarternaryp)))
                 `(cons ,c-res (cons ,s-res 'nil)))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (('s-spec sum)
           (cond ((well-formed-new-sum sum)
                  (b* (((mv s pp-lst & c-lst);;(mv s pp c)
                        (new-sum-merge sum :cough-pp nil)))
                    (s-spec-meta-aux s pp-lst c-lst)))
                 (t
                  (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                          term))))
          (('c-spec sum)
           (if (well-formed-new-sum sum)
               (b* ((;;(mv s pp c)
                     (mv s pp-lst coughed-pp-lst c-lst)
                     (new-sum-merge sum :cough-pp t))
                    (quarternaryp (quarternaryp-sum sum))

                    #|(- (and (not quarternarp)
                    (cw "s-c-spec This term is not quarternarp ~p0 ~&" sum)))||#)
                 (c-spec-meta-aux s pp-lst coughed-pp-lst c-lst quarternaryp))
             (progn$ (cw "term is not well-formed-new-sum ~p0 ~%" term)
                     term)))
          (& term))))
    (mv result t)))

#|

(s-spec-meta `(s-spec (cons (binary-and (bit-of a 0) (bit-of b 0))
                            (cons (binary-or (binary-and (bit-of a 0) (bit-of b 0))
                                             (binary-and (bit-of a 0) (bit-of b 0)))
                                  (cons (binary-and (bit-of a 0) (bit-of b 0))
                                        (cons (binary-and (bit-of a 1) (bit-of
                                                                        b 0))
                                              'nil
                                              ))))))
||#
;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  ;; (local
  ;;  (defthm lemma1
  ;;    (EQUAL (NOT (ATOM Y)) (CONSP Y))))

  ;; (local
  ;;  (in-theory (disable
  ;;              (:DEFINITION PP-TERM-P)
  ;;              (:DEFINITION rp-termp)
  ;;              (:DEFINITION ASSOC-EQUAL)
  ;;              (:DEFINITION NOT)
  ;;              (:definition assoc-equal)
  ;;              (:definition pairlis2)
  ;;              (:definition pairlis$)
  ;;              (:DEFINITION GLOBAL-TABLE)
  ;;              (:DEFINITION GET-GLOBAL)
  ;;              (:DEFINITION c-merge)
  ;;              (:DEFINITION W)
  ;;              (:REWRITE ACL2::MV-NTH-OF-CONS)

  ;;              +-is-SUM
  ;;              mod2-is-m2
  ;;              floor2-if-f2
  ;;              c-is-f2
  ;;              D-IS-D2
  ;;              s-is-m2
  ;;              s-spec-is-m2
  ;;              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
  ;;              c-spec-is-f2
  ;;              s-c-spec-is-list-m2-f2
  ;;              c-s-spec-is-list-m2-f2
  ;;              S-OF-C-TRIG-def
  ;;              )))

  ;; (local
  ;;  (defthm pairlis$-opener
  ;;    (equal (pairlis$ (cons x rest) y)
  ;;           (CONS (CONS x (car y))
  ;;                 (PAIRLIS$ rest
  ;;                           (cdr y))))
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (pairlis$) ())))))

  ;; (local
  ;;  (defthm pairlis$-nil
  ;;    (equal (pairlis$ nil y)
  ;;           nil)
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (pairlis$) ())))))

  ;; (local
  ;;  (defthm assoc-equal-opener
  ;;    (equal (assoc-equal x (cons (cons key val) b))
  ;;           (if (equal x key)
  ;;               (cons key val)
  ;;             (assoc-equal x b)))
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (assoc-equal) ())))))

  ;; (local
  ;;  (defthm assoc-equal-nil
  ;;    (equal (assoc-equal key nil)
  ;;           nil)
  ;;    :hints (("Goal"
  ;;             :in-theory (e/d (assoc-equal) ())))))

  ;; (local
  ;;  (defthm rp-evl-of-variable-redef
  ;;    (implies (and (SYMBOLP ACL2::X)
  ;;                  ACL2::X)
  ;;             (EQUAL (RP-EVL ACL2::X ACL2::A)
  ;;                    (CDR (ASSOC-EQUAL ACL2::X ACL2::A))))))

  ;; (local
  ;;  (define if$ (x y z)
  ;;    (if x y z)
  ;;    ///
  ;;    (defthm if$-implies
  ;;      (implies (if$ x y z)
  ;;               (if x y z))
  ;;      :rule-classes :forward-chaining)
  ;;    (defthm rp-evl-of-if-call-redef
  ;;      (implies (and (consp acl2::x)
  ;;                    (equal (car acl2::x) 'if))
  ;;               (equal (rp-evl acl2::x acl2::a)
  ;;                      (if$ (rp-evl (cadr acl2::x) acl2::a)
  ;;                           (rp-evl (caddr acl2::x) acl2::a)
  ;;                           (rp-evl (cadddr acl2::x) acl2::a)))))

  ;;    (defthm if$-test-correct
  ;;      (implies x
  ;;               (equal (if$ x y z)
  ;;                      y)))

  ;;    (defthm if$-test-false
  ;;      (implies (not x)
  ;;               (equal (if$ x y z)
  ;;                      z)))

  ;;    (defthm if$-case-1
  ;;      (iff (if$ x x t)
  ;;           t))

  ;;    (defthm if$-case-2
  ;;      (equal (if$ x y y)
  ;;             y))

  ;;    (defthm eq-is-equal
  ;;      (equal (eq x y)
  ;;             (equal x y)))

  ;;    (defthm if$-of-repeated-boolean
  ;;      (implies (booleanp x)
  ;;               (equal (if$ x x nil)
  ;;                      x)))

  ;;    (defthm if$-test-of-constants
  ;;      (and (iff (if$ test t nil)
  ;;                test)
  ;;           (implies (booleanp test)
  ;;                    (equal (if$ test t nil)
  ;;                           test))
  ;;           (equal (if$ test nil t)
  ;;                  (not test))
  ;;           (equal (if$ test t t)
  ;;                  t)
  ;;           (equal (if$ test nil nil)
  ;;                  nil)))))

  ;; (local
  ;;  (in-theory (disable rp-evl-of-variable)))

  ;; (local
  ;;  (defthm dummy-lemma2
  ;;    (implies (or (EQUAL (CAR (RP-EVL Y CMR::ENV))
  ;;                        'BINARY-AND)
  ;;                 (EQUAL (CAR (RP-EVL Y CMR::ENV))
  ;;                        'AND-LIST))
  ;;             (equal (EQUAL (RP-EVL Y CMR::ENV) ''1)
  ;;                    nil))))

  ;; (local
  ;;  (in-theory (enable extra-s-can-be-pp)))

  ;; (local
  ;;  (defthm EXTRA-S-CAN-BE-PP-def
  ;;    (equal (EXTRA-S-CAN-BE-PP pp c)
  ;;           (AND (EQUAL c ''0)
  ;;                (CASE-MATCH PP (('LIST ('BINARY-AND & &)) T))))))

  (local
   (in-theory (disable
               +-is-SUM
               mod2-is-m2
               floor2-if-f2
               c-is-f2
               ;;  D-IS-D2
               s-is-m2
               s-spec-is-m2
               SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
               c-spec-is-f2
               s-c-spec-is-list-m2-f2
               c-s-spec-is-list-m2-f2
               S-OF-C-TRIG-def)))

  (with-output
    :off :all
    :gag-mode nil

    (def-formula-checks
      mult-formula-checks
      (;pp-sum-merge
;s-sum-merge
       binary-append
;pp-lists-to-term-pp-lst
;pp-term-to-pp-lists
       --
       sum-list
;s-c-spec-meta
;s-spec-meta
;c-spec-meta
       binary-and
       and-list
       sort-sum
       rp::c-s-spec
       rp::s-c-spec
       rp::c-spec
       rp::s-spec
       bit-of
       svl::bits
       svl::4vec-bitand
       svl::4vec-bitor
       svl::4vec-?
       svl::4vec-?*
       sv::4vec-bitxor
       svl::4vec-bitnot
       svl::4vec-bitnot$
       adder-b+
       s-of-c-trig
       binary-?
       binary-xor
       binary-or
       binary-not
       bit-fix
       c-res
; d
       c
       m2
;d2
       f2
       times2
       s
       binary-sum
;sort-sum-meta
;evenpi
;d-sum
       sv::3vec-fix
       sv::4vec-fix
;c-s-spec-meta
       ))))

(defmacro ss (&rest args)
  `(s-spec (list . ,args)))

(defmacro dd (&rest args)
  `(d-spec (list . ,args)))

(defmacro cc (&rest args)
  `(c-spec (list . ,args)))

(defmacro sc (&rest args)
  `(s-c-spec (list . ,args)))

(defmacro cs (&rest args)
  `(c-s-spec (list . ,args)))
