#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "loghead")
(local (include-book "arithmetic"))


;;
;; meta rule to simplify loghead of a sum
;;


;Returns a term representing the conjunctionof TERM1 and TERM2.
(defund make-conjunction (term1 term2)
  (declare (type t term1 term2))
  (if (equal term1 ''t)  
      term2 ;conjoining something with "true" has no effect
    (if (equal term2 ''t)
        term1 ;conjoining something with "true" has no effect
      `(if ,term1 ,term2 'nil))))


(defund call-to-loghead-with-n-or-greater-size (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))))
  (and (consp term)
       (equal 'loghead (car term))
       (let ((size-param (cadr term)))
         (or (equal n size-param)
             (and (quotep n)
                  (quotep size-param)
                  (integerp (cadr n))
                  (integerp (cadr size-param))
                  (<= (cadr n) (cadr size-param)))))))

;if term isn't a call to loghead of n, just return term
(defund strip-loghead-from-term (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))
                  :guard-hints (("Goal" :in-theory (enable call-to-loghead-with-n-or-greater-size)))))
  (if (call-to-loghead-with-n-or-greater-size n term)
      (caddr term)
    term))

;assumes the sum nest has already been somewhat normalized (right associated, etc.)
(defun strip-logheads-from-sum (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))))
  (if (not (consp term))
      term
    (case (car term)
          (binary-+ `(binary-+ ,(strip-logheads-from-sum n (cadr term)) ;(strip-loghead-from-term n (cadr term))
                               ,(strip-logheads-from-sum n (caddr term))))
          (unary-- `(unary-- ,(strip-loghead-from-term n (cadr term))))
          (otherwise (strip-loghead-from-term n term)))))

;;We could perhaps make this more efficient by first doing a check that there
;;is at least one loghead call to strip off, thus avoiding reconstructing the
;;whole term when there is no stripping of logheads to be done.
(defun strip-logheads-from-sum-aux (term)
  (declare (xargs :guard (and (pseudo-termp term))))

  (if (and (consp term)
           (equal (car term) 'loghead))
      `(loghead ,(cadr term) ,(strip-logheads-from-sum (cadr term) (caddr term)))
    term))

;(strip-logheads-from-sum-aux '(loghead '16 (binary-+ (loghead '16 x) (loghead '16 y))))

(defun hyp-for-addend (n term)
  (declare (xargs :guard (and (pseudo-termp n)
                              (pseudo-termp term))
                  :guard-hints (("Goal" :in-theory (enable call-to-loghead-with-n-or-greater-size)))))
  (if (call-to-loghead-with-n-or-greater-size n term)
      `(integerp ,(caddr term))
    `(integerp ,term)
    ))

;returns a list of things which the hyp must claim are integers - bzo right now, that's all the addends, with the logheads stipped off!  can we do better?
(defun hyp-for-addends (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))))
  (if (not (consp term))
      `(integerp ,term)
    (case (car term)
          (binary-+ (make-conjunction 
                     (hyp-for-addends n (cadr term))
                     (hyp-for-addends n (caddr term))))
          (unary-- (hyp-for-addend n (cadr term)))
          (otherwise (hyp-for-addend n term)))))

(defun hyp-for-strip-logheads-from-sum-aux (term)
  (declare (xargs :guard (and (pseudo-termp term))))
  (if (and (consp term)
           (equal (car term) 'loghead))
      (hyp-for-addends (cadr term) (caddr term))
    nil ;what should this be?
    ))

;(hyp-for-strip-logheads-from-sum-aux '(loghead '16 (binary-+ (loghead '16 x) (loghead '16 y))))

(defevaluator loghead-sum-eval loghead-sum-eval-lst
  ((binary-+ x y)
   (unary-- x)
   (loghead n x)
   (if test x y)
   (integerp x)
   ))

(defthm eval-of-hyp-for-addends-helper
  (implies (loghead-sum-eval (hyp-for-addends n term) alist)
           (integerp (loghead-sum-eval term alist)))
  :hints (("Goal" :in-theory (enable MAKE-CONJUNCTION
                                     CALL-TO-LOGHEAD-WITH-N-OR-GREATER-SIZE)
           :do-not '(generalize eliminate-destructors))))

(defthm eval-of-hyp-for-addends-helper2
  (implies (loghead-sum-eval (hyp-for-addends n term) alist)
           (integerp (loghead-sum-eval (strip-logheads-from-sum n term) alist)))
  :hints (("Goal" :in-theory (enable make-conjunction
                                     STRIP-LOGHEAD-FROM-TERM)
           :do-not '(generalize eliminate-destructors))))

(defthm car-of-HYP-FOR-ADDENDS-isnt-quote
  (not (EQUAL 'COMMON-LISP::QUOTE
              (CAR (HYP-FOR-ADDENDS N term))))
  :hints (("Goal" :in-theory (enable MAKE-CONJUNCTION)
           :do-not '(generalize eliminate-destructors))))


(defthm fix-does-nothing
  (implies (acl2-numberp x)
           (equal (fix x)
                  x)))

(local
 (defthm hack
; This is needed for the proof of meta-rule-helper because of the change for
; ACL2 Version 3.4 to fix a "long-standing potential infinite loop in the
; rewriter" (see :doc note-3-4).  Specifically, source function rewrite-equal
; no longer calls the full rewriter on the equality of the cars of two known
; conses.
   (implies (not (equal (car x) (car y)))
            (not (equal x y)))))

(defthm meta-rule-helper
  (implies (and (loghead-sum-eval (hyp-for-addends n term) alist))
           (equal (loghead (loghead-sum-eval n alist)
                           (loghead-sum-eval term alist))
                  (loghead (loghead-sum-eval n alist)
                           (loghead-sum-eval (strip-logheads-from-sum n term) alist))))
  :hints (("Goal" :in-theory (e/d (make-conjunction
                                     strip-loghead-from-term
                                     CALL-TO-LOGHEAD-WITH-N-OR-GREATER-SIZE) 
                                  (UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;i think this prevents specious simplification
                                   ))
           :do-not '(generalize eliminate-destructors))))

(defthm meta-rule-eric
  (implies (loghead-sum-eval (hyp-for-strip-logheads-from-sum-aux term) alist)
           (equal (loghead-sum-eval term alist)
                  (loghead-sum-eval (strip-logheads-from-sum-aux term) alist)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (loghead)))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors))))


;; ;test
;; (thm
;;  (implies (and (integerp x) 
;;                (integerp y)
;;                (integerp z)
;;                (integerp w)
;;                )
;;           (equal (loghead 16 (+ y (loghead 444 z) w (- (loghead 32 x))))
;;                  (loghead 16 (+ y z w (- x)))))
;;  :hints (("Goal" :in-theory '(meta-rule-eric))))
                 
