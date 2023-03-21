
;   vw-eval.lisp             Warren A. Hunt, Jr. and Vivek Ramanathan

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.


; Started in August, 2020.  Edited many times.  Example usage
; at the end of this file.

; (ld "vw-eval.lisp" :ld-pre-eval-print t)
; (certify-book "vw-eval.lisp" ?)
; (include-book "vw-eval.lisp")

(in-package "ACL2")

(set-inhibit-warnings "Double-rewrite")
(set-inhibit-warnings "Non-rec")

(include-book "std/util/bstar" :dir :system)
(include-book "constants")
(include-book "arith-fp")
(include-book "records")
(include-book "names-and-indices")
(include-book "vw-eval-fns")

;; for documentation
(include-book "xdoc/constructors" :dir :system)

(defmacro fun (fn)
  `(pos ,fn *fns*))

(defun rational-quotep (x)
  (declare (xargs :guard t))
  (and (quotep x)
       (consp (cdr x))
       (rationalp (cadr x))
       (null (cddr x))))

(defun num-quotep (x)
  (declare (xargs :guard t))
  (and (quotep x)
       (consp (cdr x))
       ;; allow quoted value to store a floating-point number
       (nump (cadr x))
       (null (cddr x))))

(defthm num-quotep-is-rational-quotep
  (implies (num-quotep x)
           (rational-quotep x)))

(defun rational-quote-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (rational-quotep (car x))
         (rational-quote-listp (cdr x)))))

(defthm symbol-rational-list-alistp-forward-consp-cdr
  (implies (and (symbol-rational-list-alistp a)
                (alist-entry-consp a)
                (hons-assoc-equal x a))
           (consp (cdr (hons-assoc-equal x a))))
  :rule-classes :forward-chaining)

(defthm rationalp-cadr-symbol-rational-list-alistp
  (implies (and (symbol-rational-list-alistp a)
                (alist-entry-consp a)
                (hons-get x a))
           (rationalp (car (cdr (hons-assoc-equal x a))))))

(defthm true-listp-cdr-symbol-rational-list-alistp
  (implies (symbol-rational-list-alistp a)
           (true-listp (cdr (hons-assoc-equal name a)))))

(defthm rationalp-nth-exists
  (implies (and (rational-listp l)
                (or (and (natp a)
                         (< a (len l)))
                    (nth a l)))
           (rationalp (nth a l))))

(defthm rational-listp-symbol-rational-list-alistp
  (implies (symbol-rational-list-alistp a)
           (rational-listp (cdr (hons-assoc-equal name a)))))

(defthm rational-listp-cddr-hons-assoc-equal
  (implies (symbol-rational-list-alistp a)
           (rational-listp (cddr (hons-assoc-equal name a)))))

(defthm true-listp-cddr-hons-assoc-equal
  (implies (symbol-rational-list-alistp a)
           (true-listp (cddr (hons-assoc-equal name a)))))

;; We must be very careful with time!  We want to keep time as a
;; rational everywhere it is used to calculate when something happens.

;; (find-first-index 3 '(5 4 3 2 1))  ;; good
;; (find-first-index 0 '(5 4 3 2 1))  ;; bad



(encapsulate
  ()
  (defun find-first-index-help (time time-list result)
    (declare (xargs :guard (and (rationalp time)
                                (rational-listp time-list)
                                (<= 0 time)
                                (natp result))))
    (if (atom time-list)
        nil
      (if (>= time (car time-list))
          result
        (find-first-index-help time (cdr time-list) (1+ result)))))

  (local
   (defthm natp-or-null-find-first-index-help
     (implies (natp result)
              (or (natp (find-first-index-help time time-list result))
                  (null (find-first-index-help time time-list result))))
     :rule-classes :type-prescription))

  (local
   (defthm find-first-index-help-in-bounds
     (implies (and (natp result)
                   (find-first-index-help time time-list result))
              (< (find-first-index-help time time-list result)
                 (+ (len time-list)
                    result)))
     :rule-classes :linear))

  (defun find-first-index (time time-list)
    (declare (xargs :guard (and (rationalp time)
                                (rational-listp time-list)
                                (<= 0 time))))
    (find-first-index-help time time-list 0))

  (defthm natp-or-null-find-first-index
    (or (natp (find-first-index time time-list))
        (null (find-first-index time time-list)))
    :rule-classes :type-prescription)

  (defthm find-first-index-in-bounds
    (implies (find-first-index time time-list)
             (< (find-first-index time time-list)
                (len time-list)))
    :rule-classes (:linear)))

(in-theory (disable find-first-index))

(encapsulate
  ()
  (local
   (defthm nth-find-first-index
     (implies (and (rational-listp time-list)
                   (find-first-index time time-list))
              (rationalp
               (nth (find-first-index time time-list)
                    time-list)))))

  (local
   (defthm nth-find-first-index-1
    (implies (and (rational-listp time-list)
                  (< 0 (find-first-index time time-list)))
             (rationalp
              (nth (1- (find-first-index time time-list))
                   time-list)))))

  (local
   (defthm rationalp-nth-in-bounds
     (implies (and (rational-listp time-list)
                   (<= 0 i)
                   (< i (len time-list)))
              (rationalp
               (nth i time-list)))))

  (defun back (var-list time-list back-time)
    "Calculates the value at a previous time (back-time) in the ~
     simulation history of VAR-LIST."
    (declare (xargs :guard (and (consp var-list)
                                (rational-listp var-list)
                                (consp time-list)
                                (rational-listp time-list)
                                ;; (= (len var-list) (len time-list))
                                (rationalp back-time))
                    :guard-hints (("Goal" :in-theory (disable )))))
    (b* (;; If the ``back'' access reaches back before the simulation
         ;; started, we return a value of 0.
         ((unless (and (mbt (rationalp back-time))
                       (<= 0 back-time)))
          (r2f 0))
         ;; Find first time in list of times that is less than or equal
         ;; to back-time.
         ;; We assume the times in time-list are strictly decreasing
         (i (find-first-index back-time time-list))
         ((unless i) (r2f 0))
         (Vi (nth i var-list))      ;; float expected
         ((when (= i 0)) (mbe :logic (rfix Vi)
                              :exec  Vi))
         (i-1 (1- i))
         (Vi-1 (nth i-1 var-list))  ;; float expected
         ;; Note: Ti-1 > back-time >= Ti
         (Ti   (nth i   time-list)) ;; rationalp expected
         (Ti   (mbe :logic (rfix Ti)
                    :exec Ti))
         (Ti-1 (nth i-1 time-list)) ;; rationalp expected
         (Ti-1 (mbe :logic (rfix Ti-1)
                    :exec Ti-1))

         ;; We should be able to prove this check away, because i must
         ;; be less than the length of time-list and var-list. The
         ;; lengths of time-list and var-list must be the same.
         ((unless (and Vi
                       Vi-1))
          (r2f 0))
         (Vi   (mbe :logic (rfix Vi)
                    :exec Vi))
         (Vi-1 (mbe :logic (rfix Vi-1)
                    :exec Vi-1))
         ;; Consider adding this check to the guard in simulate-step:
         ;; the list of $time$ values in the history must be strictly
         ;; decreasing.
         ((when (< Ti-1 Ti))
          (prog2$ (cw "back: simulator error! Ti: ~p0, Ti-1: ~p1.~%"
                      Ti Ti-1)
                  (r2f 0)))
         ;; time values are stored as rationals. We need to
         ;; convert them to floating point when needed.
         (T-fp-diff (f- (r2f Ti-1) (r2f Ti)))
         ((when (= T-fp-diff (r2f 0)))
          (prog2$ (cw "back: floating-point rounding error! Ti: ~p0, Ti-1: ~p1.~%"
                      Ti Ti-1)
                  (r2f 0))))
      ;; we use a linear approximation to calculate the value at
      ;; back-time
      ;; Vi + ((Vi-1 - Vi)/(Ti-1 - Ti)) * (back-time - Ti)
      (f+ Vi (f* (f/ (f- Vi-1 Vi)
                     T-fp-diff)
                 (f- (r2f back-time) (r2f Ti))))))

  (defthm rationalp-back
    (rationalp (back var-list time-list back-time))
    :rule-classes :type-prescription))

(in-theory (disable back))

(defun-inline $time$< ($time$ value)
  (declare (xargs :guard (and (rationalp $time$)
                              (<= 0 $time$)
                              (rationalp value)
                              (<= 0 value))))
  #-raw (if (< $time$ value) 1 0)
  #+raw (if (< $time$ value) 1.0d0 0.0d0))

(defthm rationalp-$time$<
  (rationalp ($time$< $time$ value)))

(in-theory (disable $time$<))

(defun $time$-$hn$< ($hn$ $time$ value)
  (declare (xargs :guard (and (rationalp $hn$)
                              (<= 0 $hn$)
                              (rationalp $time$)
                              (<= 0 $time$)
                              (<= $hn$ $time$)
                              (rationalp value)
                              (<= 0 value))))
  ($time$< (- $time$ $hn$)
           value))

(defthm rationalp-$time$-$hn$<
  (rationalp ($time$-$hn$< $hn$ $time$ value)))

(in-theory (disable $time$-$hn$<))

;; some help for pulse waveform generator
(defun $time$<mod- ($time$ tdelay period compare-value)
  (declare (xargs :guard (and (rationalp $time$)
                              (<= 0 $time$)
                              (rationalp tdelay)
                              (<= 0 tdelay)
                              (rationalp period)
                              (< 0 period)
                              ;; any rational number
                              (rationalp compare-value)
                              (< 0 compare-value))))
  (if (< (mod (- $time$ tdelay) period)
         compare-value)
      (r2f 1)
    (r2f 0)))

(defthm rationalp-$time$<mod-
  (rationalp ($time$<mod- $time$ tdelay period compare-value)))

(in-theory (disable $time$<mod-))

(defun $time$-$hn$<mod- ($hn$ $time$ tdelay period compare-value)
  (declare (xargs :guard (and (rationalp $hn$)
                              (<= 0 $hn$)
                              (rationalp $time$)
                              (<= 0 $time$)
                              (<= $hn$ $time$)
                              (rationalp tdelay)
                              (<= 0 tdelay)
                              (rationalp period)
                              (< 0 period)
                              ;; any rational number
                              (rationalp compare-value)
                              (< 0 compare-value))))
  ($time$<mod- (- $time$ $hn$) tdelay period compare-value))

(defthm rationalp-$time$-$hn$<mod-
  (rationalp ($time$-$hn$<mod- $hn$ $time$ tdelay period compare-value)))

(in-theory (disable $time$-$hn$<mod-))

(defun $time$<mod-fn ($time$ args)
  (declare (xargs :guard (and (rationalp $time$)
                              (<= 0 $time$)
                              (= (len args) 3)
                              (rational-quotep (car args))
                              (<= 0 (unquote (car args)))
                              (rational-quotep (cadr args))
                              (< 0 (unquote (cadr args)))
                              (rational-quotep (caddr args))
                              (< 0 (unquote (caddr args))))))
  ($time$<mod- $time$
               (unquote (car args))
               (unquote (cadr args))
               (unquote (caddr args))))

(defthm rationalp-$time$<mod-fn
  (rationalp ($time$<mod-fn $time$ args)))

(in-theory (disable $time$<mod-fn))

(defun $time$-$hn$<mod-fn ($hn$ $time$ args)
  (declare (xargs :guard (and (rationalp $hn$)
                              (<= 0 $hn$)
                              (rationalp $time$)
                              (<= 0 $time$)
                              (<= $hn$ $time$)
                              (= (len args) 3)
                              (rational-quotep (car args))
                              (<= 0 (unquote (car args)))
                              (rational-quotep (cadr args))
                              (< 0 (unquote (cadr args)))
                              (rational-quotep (caddr args))
                              (< 0 (unquote (caddr args))))))
  ($time$<mod-fn (- $time$ $hn$) args))

(defthm rationalp-$time$-$hn$<mod-fn
  (rationalp ($time$-$hn$<mod-fn $hn$ $time$ args)))

(in-theory (disable $time$-$hn$<mod-fn))

; Now we define our vw langauge.

(defmacro nargs (x n)
  (declare (xargs :guard (natp n)))
  (if (= n 0)
      `(null ,x)
    (if (= n 1)
        `(and (consp ,x)
              (null (cdr ,x)))
      (list 'and
            `(consp ,x)
            `(nargs (cdr ,x) ,(- n 1))))))

(defun vw-eval-termp (x)
  (declare (xargs :guard t))
  (b* (((when (atom x))
        (symbolp x))

       (fn (car x))
       (args (cdr x)))

    (case fn
      (quote
       ;; raw values are fp in raw mode!
       (num-quotep x)
       ;; (rational-quotep x)
       )

      (back
       (and (nargs args 2)
            (let ((name (car args))
                  (back (cadr args)))
              (and (symbolp name)
                   (not (booleanp name))
                   (rational-quotep back)))))

      ($time$<
       (and (nargs args 1)
            (rational-quotep (car args))
            (<= 0 (unquote (car args)))))

      ($time$-$hn$<
       (and (nargs args 1)
            (rational-quotep (car args))
            (<= 0 (unquote (car args)))))

      ($time$<mod-
       (and (nargs args 3)
            (rational-quotep (car args))
            (<= 0 (unquote (car args)))
            (rational-quotep (cadr args))
            (< 0 (unquote (cadr args)))
            (rational-quotep (caddr args))
            (< 0 (unquote (caddr args)))))

      ($time$-$hn$<mod-
       (and (nargs args 3)
            (rational-quotep (car args))
            (<= 0 (unquote (car args)))
            (rational-quotep (cadr args))
            (< 0 (unquote (cadr args)))
            (rational-quotep (caddr args))
            (< 0 (unquote (caddr args)))))

      (if (and (nargs args 3)
               (vw-eval-termp (car args))
               (vw-eval-termp (cadr args))
               (vw-eval-termp (caddr args))))

      (f-not  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f0-    (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-abs  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-1/x  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-sqrt (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-sin  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-cos  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-tan  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-tanh (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f-exp  (and (nargs args 1)
                   (vw-eval-termp (car args))))
      (f+     (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (f-     (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (f*     (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (f/     (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (f<     (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (f=     (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (f-mod  (and (nargs args 2)
                   (vw-eval-termp (car args))
                   (vw-eval-termp (cadr args))))
      (otherwise nil))))

;; For list of vw-eval-termps
(defun vw-eval-term-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (vw-eval-termp (car xs))
         (vw-eval-term-listp (cdr xs)))))

; The VWSIM Evaluator

(defun vw-eval (x a)
  (declare (xargs :guard
                  (and (vw-eval-termp x)
                       (symbol-rational-list-alistp a)
                       (alist-entry-consp a))
                  :verify-guards nil))
  (b* (((when (atom x))
        (let ((pair (hons-get x a)))
          (if pair
              (if (or (eq x '$time$)
                      (eq x '$hn$))
                  ;; $time$ and $hn$ are stored as rationals. When
                  ;; requested, we coerce the values to double-floats.
                  (r2f (mbe :logic (rfix (car (cdr pair)))
                            :exec        (car (cdr pair))))
                ;; these values are already stored as double-floats in
                ;; the record.
                (mbe :logic (rfix (car (cdr pair)))
                     :exec        (car (cdr pair))))
            (prog2$ (cw "vw-eval:  Simulation variable lookup failure: ~p0 !!!~%" x)
                    (r2f 0)))))

       (fn (car x))
       (fn-num (fun fn))

       (args (cdr x))
       (arg1 (if (<= #.*if-index* fn-num)
                 (vw-eval (car args) a)
               0))
       (arg2 (if (<= #.*f+-index* fn-num)
                 (vw-eval (cadr args) a)
               0)))

    (case fn-num
      (#.*quote-index*
       (r2f (mbe :logic (rfix (car args))
                 :exec        (car args))))

      (#.*back-index*
       ;; Example symbolic call: (back a-name back-time)
       (let* ((var (car args))
              (delay (unquote (cadr args)))
              (time-list (cdr (hons-get '$time$ a)))
              (var-list (cdr (hons-get var a))))
         (if (and (consp var-list)
                  (consp time-list))
             (let* ((back-time (- (car time-list) delay))
                    (val (back var-list time-list back-time)))
               (r2f (mbe :logic (rfix val)
                         :exec val)))
           (r2f 0))))

      (#.*$time$<-index*
       (let* ((time-list (cdr (hons-get '$time$ a))))
         (if (and (consp time-list)
                  (rationalp (car time-list)) ;; remove check?
                  (<= 0 (car time-list)))
             ($time$< (car time-list)
                      (unquote (car args)))
           ;; why can't we have (er hard ...) here instead of cw?
           (prog2$ (cw "vw-eval: $time$<: $time$ is empty or ~
                                         non-rational in the ~
                                         record.~%")
                   (r2f 0)))))

      (#.*$time$-$hn$<-index*
       (b* ((time-list (cdr (hons-get '$time$ a)))
            (hn-list   (cdr (hons-get '$hn$ a)))
            ((unless (and (consp time-list)
                          (consp hn-list)))
             (prog2$ (cw "vw-eval: $time-$hn$<mod-: $time$ or $hn$ is ~
                                         empty or non-rational in ~
                                         the record.~%")
                     (r2f 0)))
            ($hn$ (car hn-list))
            ($time$ (car time-list))
            ((unless (and (rationalp $time$)
                          (rationalp $hn$)
                          (<= 0 $time$)
                          (<= 0 $hn$)
                          (<= $hn$ $time$)))
             (prog2$ (cw "vw-eval: $time-$hn$<: $time$ or $hn$ is ~
                                         non-rational or non-negative.~%")
                     (r2f 0)))
            (compare-value (unquote (car args))))
         ($time$-$hn$< $hn$ $time$ compare-value)))

      (#.*$time$<mod--index*
       (b* ((time-list (cdr (hons-get '$time$ a)))
            ((unless (consp time-list))
             (prog2$ (cw "vw-eval: $time$<mod-: $time$ empty in the ~
                                          record.~%")
                     (r2f 0)))
            ($time$ (car time-list))
            ((unless (and (rationalp $time$)
                          (<= 0 $time$)))
             (prog2$ (cw "vw-eval: $time$<mod-: $time$ non-rational ~
                                         in the record.~%")
                     (r2f 0))))
         ($time$<mod-fn $time$ args)))

      (#.*$time$-$hn$<mod--index*
       (b* ((time-list (cdr (hons-get '$time$ a)))
            (hn-list   (cdr (hons-get '$hn$ a)))
            ((unless (and (consp time-list)
                          (consp hn-list)))
             (prog2$ (cw "vw-eval: $time-$hn$<mod-: $time$ or $hn$ is ~
                                         empty or non-rational in ~
                                         the record.~%")
                     (r2f 0)))
            ($hn$ (car hn-list))
            ($time$ (car time-list))
            ((unless (and (rationalp $time$)
                          (rationalp $hn$)
                          (<= 0 $time$)
                          (<= 0 $hn$)
                          (<= $hn$ $time$)))
             (prog2$ (cw "vw-eval: $time-$hn$<mod-: $time$ or $hn$ is ~
                                         non-rational or non-negative.~%")
                     (r2f 0))))
         ($time$-$hn$<mod-fn $hn$ $time$ args)))

      (#.*if-index*
       (let ((arg2 (vw-eval (cadr args) a))
             (arg3 (vw-eval (caddr args) a)))
         (if (not (= arg1 (r2f 0)))
             arg2
           arg3)))

      (#.*f-not-index*   (f-not arg1))
      (#.*f0--index*     (f0- arg1))
      (#.*f-abs-index*   (f-abs arg1))
      (#.*f-1/x-index*   (if (= arg1 (r2f 0))
                             (prog2$ (cw "vw-eval: f-1/x dividing by 0.~%")
                                     (r2f 0))
                           (f-1/x arg1)))
      (#.*f-sqrt-index*  (if (< arg1 (r2f 0))
                             (prog2$ (cw "vw-eval: f-sqrt of negative number.~%")
                                     (r2f 0))
                           (f-sqrt arg1)))
      (#.*f-sin-index*   (f-sin  arg1))
      (#.*f-cos-index*   (f-cos  arg1))
      (#.*f-tan-index*   (f-tan  arg1))
      (#.*f-tanh-index*  (f-tanh arg1))
      (#.*f-exp-index*   (f-exp  arg1))
      (#.*f+-index*      (f+ arg1 arg2))
      (#.*f--index*      (f- arg1 arg2))
      (#.*f*-index*      (f* arg1 arg2))
      (#.*f/-index*      (if (= arg2 (r2f 0))
                             (prog2$ (cw "vw-eval: f/ dividing by 0.~%") 0)
                           (f/ arg1 arg2)))
      (#.*f<-index*      (f< arg1 arg2))
      (#.*f=-index*      (f= arg1 arg2))
      (#.*f-mod-index*   (if (= arg2 (r2f 0))
                             (prog2$ (cw "vw-eval: f-mod using 0 divisor") 0)
                           (f-mod arg1 arg2)))
      (otherwise (r2f 0)))))

(defthm rationalp-vw-eval
  (rationalp (vw-eval x a))
  :rule-classes :type-prescription)

(verify-guards vw-eval
  ;; we enable pos to calculate position results for the function
  ;; calls
  :hints (("Goal" :in-theory (enable pos))))

(assert-event (equal (vw-eval '(f+ '3
                                   (f* x '5))
                              (make-fast-alist '((x 4))))
                     23))

(defun vw-eval-list (xs a)
  (declare (xargs :guard (and (vw-eval-term-listp xs)
                              (symbol-rational-list-alistp a)
                              (alist-entry-consp a))))
  (if (atom xs)
      nil
    (cons (vw-eval (car xs) a)
          (vw-eval-list (cdr xs) a))))

(defthm rational-listp-vw-eval-list
  (implies (vw-eval-term-listp xs)
           (rational-listp (vw-eval-list xs a))))

(defthm len-vw-eval-list
  (equal (len (vw-eval-list xs a))
         (len xs)))

(defun vw-eval-fold (x a)
  ;; Seed a with *f-constants*
; Simplifies the term "x" by evaluating expressions that contain only
; quoted numbers and symbols in the alist "a". This is a precise
; operation that only involves rational number arithmetic. Hence, we
; do not evaluate trig functions (sin, cos, tan, ...).
  (declare (xargs :guard
                  (and (vw-eval-termp x)
                       (symbol-rational-list-alistp a)
                       (alist-entry-consp a))
                  :verify-guards nil))
  (b* (((when (atom x))
        (b* ((pair (hons-get x a)))
          (if pair
              (mbe :logic (kwote (rfix (car (cdr pair))))
                   :exec  (kwote       (car (cdr pair))))
            x)))

       (fn (car x))
       (fn-num (fun fn))
       (args (cdr x))

       (arg1 (if (<= #.*if-index* fn-num)
                 (vw-eval-fold (car args) a)
               nil))

       (arg2 (if (<= #.*f+-index* fn-num)
                 (vw-eval-fold (cadr args) a)
               nil)))

    (case fn-num
      (#.*quote-index* (mbe :logic (kwote (rfix (car args)))
                            :exec  x))

      ((#.*back-index*
        #.*$time$<-index*
        #.*$time$-$hn$<-index*
        #.*$time$<mod--index*
        #.*$time$-$hn$<mod--index*)
       x)

      (#.*if-index*
       (let ((test arg1))
         (if (quotep test)
             (if (not (= (unquote test) 0))
                 (vw-eval-fold (cadr args) a)
               (vw-eval-fold (caddr args) a))
           (list 'if
                 test
                 (vw-eval-fold (cadr args) a)
                 (vw-eval-fold (caddr args) a)))))

      (#.*f-not-index*   (if (quotep arg1)
                             (kwote (if (= (unquote arg1) 0) 1 0))
                           (list fn arg1)))

      (#.*f0--index*     (if (quotep arg1)
                             (kwote (- (unquote arg1)))
                           (list fn arg1)))
      (#.*f-abs-index*   (if (quotep arg1)
                             (kwote (abs (unquote arg1)))
                           (list fn arg1)))
      (#.*f-1/x-index*   (if (quotep arg1)
                             (if (= (unquote arg1) 0)
                                 (prog2$ (cw "vw-eval: f-1/x dividing by 0.~%")
                                         (kwote 0))
                               (kwote (/ (unquote arg1))))
                           (list fn arg1)))
      (#.*f-sqrt-index*  (list fn arg1))
      (#.*f-sin-index*   (list fn arg1))
      (#.*f-cos-index*   (list fn arg1))
      (#.*f-tan-index*   (list fn arg1))
      (#.*f-tanh-index*  (list fn arg1))
      (#.*f-exp-index*   (list fn arg1))
      (#.*f+-index*      (if (and (quotep arg1)
                                  (quotep arg2))
                             (kwote (+ (unquote arg1) (unquote arg2)))
                           (if (equal arg1 (kwote 0))
                               arg2
                             (if (equal arg2 (kwote 0))
                                 arg1
                               (list fn arg1 arg2)))))
      (#.*f--index*      (if (and (quotep arg1)
                                  (quotep arg2))
                             (kwote (- (unquote arg1) (unquote arg2)))
                           (if (equal arg2 (kwote 0))
                               arg1
                             (list fn arg1 arg2))))
      (#.*f*-index*      (if (and (quotep arg1)
                                  (quotep arg2))
                             (kwote (* (unquote arg1) (unquote arg2)))
                           (if (or (equal arg1 (kwote 0))
                                   (equal arg2 (kwote 0)))
                               (kwote 0)
                             (if (equal arg1 (kwote 1))
                                 arg2
                               (if (equal arg2 (kwote 1))
                                   arg1
                                 (list fn arg1 arg2))))))
      (#.*f/-index*      (if (and (quotep arg1)
                                  (quotep arg2))
                             (if (= (unquote arg2) 0)
                                 (prog2$ (cw "vw-eval: f/ dividing by 0.~%")
                                         (kwote 0))
                               (kwote (/ (unquote arg1) (unquote arg2))))
                           (list fn arg1 arg2)))
      (#.*f<-index*      (if (and (quotep arg1)
                                  (quotep arg2))
                             (kwote (if (< (unquote arg1) (unquote arg2)) 1 0))
                           (list fn arg1 arg2)))
      (#.*f=-index*      (if (and (quotep arg1)
                                  (quotep arg2))
                             (kwote (if (= (unquote arg1) (unquote arg2)) 1 0))
                           (list fn arg1 arg2)))
      (#.*f-mod-index*   (if (and (quotep arg1)
                                  (quotep arg2))
                             (if (= (unquote arg2) 0)
                                 (prog2$ (cw "vw-eval: f-mod using 0 divisor")
                                         (kwote 0))
                               (kwote (mod (unquote arg1) (unquote arg2))))
                           (list fn arg1 arg2)))
      (otherwise x))))

(encapsulate
  ()
  (local
   (defthm cadr-quote-vw-eval-fold
     (implies (quotep (vw-eval-fold x a))
              (rationalp (cadr (vw-eval-fold x a))))))

  (local
   (defthm consp-quoted-number-vw-eval-fold
     (implies (equal (car (vw-eval-fold x a))
                     'quote)
              (consp (cdr (vw-eval-fold x a))))))

  (verify-guards vw-eval-fold
    :hints (("Goal" :in-theory (enable pos)))))

(defthm vw-eval-termp-vw-eval-fold
  (implies (vw-eval-termp x)
           (vw-eval-termp (vw-eval-fold x a)))
  :rule-classes :type-prescription)

;; We prove that given a subset of the record used for vw-eval,
;; vw-eval-fold does not change the result.

(defun record-subsetp (r-subset r)
  (declare (xargs :guard (and (symbol-rational-list-alistp r-subset)
                              (symbol-rational-list-alistp r)
                              )))
  (if (atom r-subset)
      t
    (let* ((pair (car r-subset))
           (name (car pair)))
      (and (equal pair (hons-assoc-equal name r))
           (record-subsetp (cdr r-subset) r)))))

(encapsulate
  ()
  (local
   (defthm f-mod-0
     (equal (f-mod 0 x)
            0)
     :hints
     (("Goal" :in-theory (enable f-mod)))))

  (local
   (defthm rationalp-cadr-symbol-vw-eval-fold
     (implies (and (vw-eval-termp term)
                   (equal (car (vw-eval-fold term r-subset))
                          'quote))
              (rationalp (cadr (vw-eval-fold term r-subset))))))

  (local
   (defthm record-subset-first-item-in-list-same
     (implies (and (record-subsetp r-subset r)
                   (hons-assoc-equal term r-subset))
              (equal (cadr (hons-assoc-equal term r-subset))
                     (cadr (hons-assoc-equal term r))))))

  (local
   (defthm rationalp-mod
     (implies (and (rationalp x)
                   (rationalp y))
              (rationalp (mod x y)))))

  (defthm vw-eval-same-for-vw-eval-fold
    (implies (and (vw-eval-termp term)
                  (symbol-rational-list-alistp r)
                  (symbol-rational-list-alistp r-subset)
                  (record-subsetp r-subset r))
             (equal (vw-eval (vw-eval-fold term r-subset) r)
                    (vw-eval term r)))
    :hints
    (("Goal" :in-theory (e/d (f-not f0- f-abs f-1/x f-sqrt f-sin f-cos f-tan f-tanh f-exp
                                    f+ f- f* f/ f< f= f-mod)
                             (not mod true-listp))))))

; The waveform vw-eval-termp generators

; The following events are for creating VWSIM input sources

; equations from
; https://cseweb.ucsd.edu/classes/wi10/cse241a/assign/hspice_sa.pdf

(defun f-exp-src-sym
  (v1           ;; initial value
   v2           ;; pulsed value
   trise_delay  ;; rise delay time
   tau_rise     ;; rise time constant
   tfall_delay  ;; fall delay time
   tau_fall     ;; fall time
   )
  (declare (xargs :guard (and (rational-quotep v1)
                              (rational-quotep v2)
                              (rational-quotep trise_delay)
                              (<= 0 (unquote trise_delay))
                              (rational-quotep tau_rise)
                              (< 0 (unquote tau_rise))
                              (rational-quotep tfall_delay)
                              (< 0 (unquote tfall_delay))
                              (rational-quotep tau_fall)
                              (< 0 (unquote tau_fall)))))
  (let ((expr1 `(f+ ,v1
                    (f* (f- ,v2 ,v1)
                        (f- '1 (f-exp
                                (f0- (f/ (f- $time$ ,trise_delay)
                                         ,tau_rise))))))))
  `(if ($time$< ,trise_delay)
       ,v1
     (if ($time$< ,tfall_delay)
         ,expr1
       (f+ ,expr1
           (f* (f- ,v1 ,v2)
               (f- '1 (f-exp
                       (f0- (f/ (f- $time$ ,tfall_delay)
                                ,tau_fall))))))))))

(defthm vw-eval-termp-f-exp-src-sym
  (implies
   (and (vw-eval-termp v1)
        (vw-eval-termp v2)
        (rational-quotep trise_delay)
        (<= 0 (unquote trise_delay))
        (vw-eval-termp tau_rise)
        (rational-quotep tfall_delay)
        (<= 0 (unquote tfall_delay))
        (vw-eval-termp tau_fall))
   (vw-eval-termp
    (f-exp-src-sym v1 v2 trise_delay tau_rise tfall_delay tau_fall))))


(defun f-pulse-src-sym (v1 v2 tdelay trise tfall width period)
  (declare (xargs :guard (and (rational-quotep v1)
                              (rational-quotep v2)
                              (rational-quotep tdelay)
                              (<= 0 (unquote tdelay))
                              (rational-quotep trise)
                              (< 0 (unquote trise))
                              (rational-quotep tfall)
                              (< 0 (unquote tfall))
                              (rational-quotep width)
                              (< 0 (unquote width))
                              (rational-quotep period)
                              (< 0 (unquote period))
                              (<= (+ (unquote trise) (unquote tfall)
                                     (unquote width))
                                  (unquote period)))))
  ;; Let td=tdelay, per=period, tstop=time the simulation ends
  ;; example timeline:
  ;; ----+xxxxxx-----------+xxxxxx-----------+xxxxxx----+
  ;;    td               td+per           td+(2*per)   tstop

  ;; As seen above, the pulse is generated at td, td + per, td +
  ;; (2*per).  Notice that the pulse is repeated at td+k*per intervals
  ;; NOT k*(td+per). We must account for the td offset of the pulse!

  (let* ((offset-time `(f- $time$ ,tdelay))
         (mtd `(f-mod ,offset-time ,period)))
    `(if ($time$< ,tdelay)
         ,v1
       (if ($time$<mod- ,tdelay ,period ,trise)
           (f+ ,v1 (f* (f/ (f- ,v2 ,v1) ,trise) ,mtd))
         (if ($time$<mod- ,tdelay ,period ',(+ (unquote trise)
                                               (unquote width)))
             ,v2
           (if ($time$<mod- ,tdelay ,period ',(+ (unquote trise)
                                                 (unquote width)
                                                 (unquote tfall)))
               (f+ ,v2 (f* (f/ (f- ,v1 ,v2) ,tfall)
                           (f- ,mtd (f+ ,trise ,width))))
             ,v1))))))

(defthm vw-eval-termp-f-pulse-src-sym
  (implies (and (rational-quotep v1)
                (rational-quotep v2)
                (rational-quotep tdelay)
                (<= 0 (unquote tdelay))
                (rational-quotep trise)
                (< 0 (unquote trise))
                (rational-quotep tfall)
                (< 0 (unquote tfall))
                (rational-quotep width)
                (< 0 (unquote width))
                (rational-quotep period)
                (< 0 (unquote period)))
           (vw-eval-termp (f-pulse-src-sym v1 v2 tdelay trise tfall width period))))


; Some current/voltage/phase waveform helper functions...

(defun pwl-expr-okp (pwl-expr)
  (declare (xargs :guard t))
  (if (atom pwl-expr)
      (null pwl-expr)
    (and (consp (cdr pwl-expr))
         (let ((time (car pwl-expr))
               (value (cadr pwl-expr)))
           (and
            (rational-quotep time)
            (<= 0 (unquote time))
            (if (consp (cddr pwl-expr))
                (let ((next-time (car (cddr pwl-expr))))
                  (and (rational-quotep next-time)
                       (< (unquote time) (unquote next-time))))
              (null (cddr pwl-expr)))
            (rational-quotep value)
            (pwl-expr-okp (cddr pwl-expr)))))))

(defun f-pwl-src-sym-help (l prev-time prev-val)
  (declare (xargs :guard (and (pwl-expr-okp l)
                              (rational-quotep prev-time)
                              (rational-quotep prev-val))))
  (if (atom l)
      prev-val
    (if (atom (cdr l))
        nil
      (let* ((now-time (car l))
             (now-val  (cadr l))
             (t-diff   `(f- ,now-time ,prev-time))
             (val-diff `(f- ,now-val ,prev-val))
             (slope    `(f/ ,val-diff ,t-diff)))
        `(if ($time$< ,now-time)
             (f+ ,prev-val
                 (f* ,slope
                     (f- $time$ ,prev-time)))
           ,(f-pwl-src-sym-help (cddr l) now-time now-val))))))

(defthm vw-eval-term-f-pwl-src-sym-help
  (implies (and (pwl-expr-okp l)
                (vw-eval-termp prev-time)
                (vw-eval-termp prev-val))
           (vw-eval-termp (f-pwl-src-sym-help l prev-time prev-val))))

(defun f-pwl-src-sym (l)
  (declare (xargs :guard (pwl-expr-okp l)))
  (if (atom l)
      (cw "f-pwl-src-sym: Empty PWL list provided!~%")
    (if (not (equal (car l) ''0))
        (cw "f-pwl-src-sym: Must specify time values starting at ~
             0.~p0 ~%" l)
      (f-pwl-src-sym-help (cddr l) ''0 (cadr l)))))

(defthm vw-eval-term-listp-f-pwl-src-sym
  (implies (pwl-expr-okp l)
           (vw-eval-termp (f-pwl-src-sym l))))

(defun f-sin-src-sym
    (voffset     ;; offset
     vpeak       ;; amplitude (peak)
     freq        ;; frequency
     tdelay      ;; time delay
     damp_factor ;; damping factor
     phase       ;; phase delay
     )
  "Sinusoidal input source"
  (declare (xargs :guard (and (rational-quotep voffset)
                              (rational-quotep vpeak)
                              (rational-quotep freq)
                              (<= 0 (unquote freq))
                              (rational-quotep tdelay)
                              (<= 0 (unquote tdelay))
                              (rational-quotep damp_factor) ;; damping factor in Hertz
                              (<= 0 (unquote damp_factor))
                              (rational-quotep phase) ;; phase delay in degrees
                              (<= 0 (unquote phase))
                              )))
  `(if ($time$< ,tdelay)
       (f+ ,voffset
           (f* ,vpeak
               (f-sin (f* *pi* (f/ ,phase '180)))))
     (f+ ,voffset
         (f* ,vpeak
             (f* (f-exp (f* (f0- (f- $time$ ,tdelay))
                            ,damp_factor))
                 (f-sin (f+ (f* (f* '2 *pi*)
                                (f* ,freq
                                    (f- $time$ ,tdelay)))
                            (f* *pi*
                                (f/ ,phase '360)))))))))

(defthm vw-eval-termp-f-sin-src-sym
  (implies (and (vw-eval-termp voffset)
                (vw-eval-termp vpeak)
                (vw-eval-termp freq)
                (rational-quotep tdelay)
                (<= 0 (unquote tdelay))
                (vw-eval-termp damp_factor)
                (vw-eval-termp phase))
           (vw-eval-termp
            (f-sin-src-sym voffset vpeak freq tdelay damp_factor phase))))

(defun phase-equation-at-$time$-$hn$ (term)
  ;; We do not store the phase in a voltage-based simulation. We
  ;; rewrite the phase-equation in terms of (- $time$ $hn$) to
  ;; calculate phi_{n-1}.
  (declare (xargs :guard (vw-eval-termp term)))
  (b* (((when (atom term))
        (if (equal term '$time$)
          '(f- $time$ $hn$)
        term))

       (fn (car term))
       (args (cdr term))

       ((when (eq fn 'quote))
        term)

       ((when (eq fn 'back))
        ;; Example symbolic call: (back a-name back-time)
        term)

       ((when (eq fn 'if))
        `(if ,(phase-equation-at-$time$-$hn$ (car args))
             ,(phase-equation-at-$time$-$hn$ (cadr args))
           ,(phase-equation-at-$time$-$hn$ (caddr args))))

       ((when (eq fn '$time$<))
        (cons '$time$-$hn$< args))

       ;; we assume that $time$-$hn$< is not already in the term
       ((when (eq fn '$time$-$hn$<))
        (prog2$ (cw "phase-equation-at-$time$-$hn$: the term already ~
                     contains a call to $time$-$hn$<. This is bad!~%")
                term))

       ((when (eq fn '$time$<mod-))
        (cons '$time$-$hn$<mod- args))

       ((when (eq fn '$time$-$hn$<mod-))
        (prog2$ (cw "phase-equation-at-$time$-$hn$: the term already ~
                     contains a call to $time$-$hn$<mod-. This is ~
                     bad!~%")
                term)))
    (case fn
      (f-not  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-not ,arg1)))
      (f0-    (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f0- ,arg1)))
      (f-abs  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-abs ,arg1)))
      (f-1/x  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-1/x ,arg1)))
      (f-sqrt (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-sqrt ,arg1)))
      (f-sin  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-sin ,arg1)))
      (f-cos  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-cos ,arg1)))
      (f-tan  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-tan ,arg1)))
      (f-tanh (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-tanh ,arg1)))
      (f-exp  (let ((arg1 (phase-equation-at-$time$-$hn$ (car args))))
                `(f-exp  ,arg1)))
      (f+ (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
            `(f+ ,arg1 ,arg2)))
      (f- (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
            `(f- ,arg1 ,arg2)))
      (f* (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
            `(f* ,arg1 ,arg2)))
      (f/ (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
            `(f/ ,arg1 ,arg2)))
      (f< (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
            `(f< ,arg1 ,arg2)))
      (f= (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
            `(f= ,arg1 ,arg2)))
      (f-mod (let ((arg1 (phase-equation-at-$time$-$hn$ (car args)))
                   (arg2 (phase-equation-at-$time$-$hn$ (cadr args))))
               `(f-mod ,arg1 ,arg2)))
      (otherwise term))))

(defthm vw-eval-termp-phase-equation-at-$time$-$hn$
  (implies (vw-eval-termp term)
           (vw-eval-termp
            (phase-equation-at-$time$-$hn$ term))))

(defun r2f-term (x)
; Coerces (as appropriate) the quoted rationals in the term "x" to
; double-floats.
  (declare (xargs :guard
                  (vw-eval-termp x)
                  :verify-guards nil))
  (b* (((when (atom x))
        x)

       (fn (car x))
       (args (cdr x)))

    (case fn
      (quote (mbe :logic (kwote (rfix (r2f (car args))))
                  :exec  (kwote       (r2f (car args)))))

      ;; perform rational comparisons/computations
      (back x)

      (if (list fn
                (r2f-term (car args))
                (r2f-term (cadr args))
                (r2f-term (caddr args))))


      ;; perform rational comparisons/computations
      (($time$< $time$-$hn$< $time$<mod- $time$-$hn$<mod-)
       x)

      (f-not  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))

      (f0-    (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-abs  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))

      ;; (otherwise x))))

      (f-1/x  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-sqrt (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-sin  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-cos  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-tan  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-tanh (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f-exp  (let ((arg1 (r2f-term (car args))))
                (list fn arg1)))
      (f+     (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (f-     (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (f*     (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (f/     (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (f<     (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (f=     (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (f-mod  (let ((arg1 (r2f-term (car args)))
                    (arg2 (r2f-term (cadr args))))
                (list fn arg1 arg2)))
      (otherwise x))))

(defthm vw-eval-termp-r2f-term
  (implies (vw-eval-termp x)
           (vw-eval-termp (r2f-term x)))
  :hints
  (("Goal" :in-theory (disable member-equal))))

(defthm r2f-term-is-identity-in-logic-mode
  (implies (vw-eval-termp x)
           (equal (r2f-term x) x)))

(verify-guards r2f-term)

(defun r2f-term-list (xs)
  (declare (xargs :guard (vw-eval-term-listp xs)))
  (if (atom xs)
      nil
    (cons (r2f-term (car xs))
          (r2f-term-list (cdr xs)))))

(defthm vw-eval-term-listp-r2f-term-list
  (implies (vw-eval-term-listp xs)
           (vw-eval-term-listp
            (r2f-term-list xs))))
