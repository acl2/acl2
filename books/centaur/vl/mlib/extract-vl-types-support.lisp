; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "VL")

(include-book "centaur/sv/svex/4vec" :dir :system)
(include-book "std/strings/hexify" :dir :System)
(include-book "std/strings/decimal" :dir :System)
(include-book "std/basic/two-nats-measure" :dir :System)


#!VL
(defsection get-extracted-vl-type-array-ranges
  (local
   (in-theory (e/d ()
                   (expt distributivity
                         floor acl2::loghead acl2::logtail mod
                         sv::4vec-part-select
                         sv::4vec-p
                         sv::4vec-part-install))))

  (local
   (defthm natp-of-*
     (implies (and (natp x) (natp y))
              (<= 0 (* x y)))))

  (local
   (defthm natp-of-+
     (implies (and (natp x) (natp y))
              (<= 0 (+ x y)))))

  
  (define vl-coretype-collected-dims-p (x)
    :enabled t
    (if (atom x)
        (equal x nil)
      (and (consp (car x))
           (consp (cdar x))
           (b* (((list* slice-size msb lsb) (car x)))
             (and (natp slice-size)
                  (natp msb)
                  (natp lsb)
                  (>= msb lsb)))
           (vl-coretype-collected-dims-p (cdr x))))
    ///
    (defthm vl-coretype-collected-dims-p-of-append
      (implies (and (vl-coretype-collected-dims-p x)
                    (vl-coretype-collected-dims-p y))
               (vl-coretype-collected-dims-p (append x y))))
    (defthm when-vl-coretype-collected-dims-p-is-consp
      (implies (and (vl-coretype-collected-dims-p x)
                    (consp x))
               (and (consp (car x))
                    (consp (cdar x))
                    (b* (((list* slice-size msb lsb) (car x)))
                      (and (natp slice-size)
                           (natp msb)
                           (natp lsb)
                           ;;(>= msb lsb)
                           ))))
      :rule-classes (:forward-chaining :type-prescription))

    (defthm vl-coretype-collected-dims-p-of-vals
      (implies (and (and (natp rest-size)
                         (natp msb)
                         (natp lsb)
                         (>= msb lsb))
                    (vl-coretype-collected-dims-p rest))
               (vl-coretype-collected-dims-p (cons (list* rest-size msb lsb) rest)))))

  (define get-extracted-vl-type-array-ranges ((start natp)
                                              (width natp)
                                              (dims vl-coretype-collected-dims-p)
                                              (args true-listp)
                                              &optional
                                              (vec-name "")
                                              (allow-redundant-args 'nil)
                                              )

    :returns (mv res-start res-width)

    (cond ((or (atom dims)
               (atom args))
           (progn$
            (and (consp args)
                 (or allow-redundant-args
                     (raise "Too many arguments are passed to access a vl-coretype (~s0)~%" vec-name)))
            (mv start width)))
          (t (b* ((cur-arg (car args))
                  ((unless (natp cur-arg))
                   (progn$ (raise "A a non-natp value is given for an index argument: ~p0 (~s1) ~%"
                                  cur-arg vec-name)
                           (mv start width)))
                  ((list* slice-size msb lsb) (car dims))
                  ((unless (and (<= cur-arg msb)
                                (>= cur-arg lsb)))
                   (progn$ (raise "Given argument '~p0' is out of bounds for the given vector (~s1). MSB (upperbound) is ~p2 and LSB (lowerbound) is ~p3 ~%"
                                  cur-arg vec-name msb lsb)
                           (mv start width)))
                  (index (- cur-arg lsb))

                  (offset (* index slice-size))
                  (start (+ start offset)))
               (get-extracted-vl-type-array-ranges start
                                                   slice-size
                                                   (cdr dims)
                                                   (cdr args)
                                                   vec-name
                                                   allow-redundant-args))))
    ///
    (defret natp-of-start-of-<fn>
      (implies (and (natp start)
                    (vl-coretype-collected-dims-p dims))
               (and (natp res-start)
                    (integerp res-start)
                    (<= 0 res-start))))
    (defret natp-of-width-of-<fn>
      (implies (and (natp width)
                    (vl-coretype-collected-dims-p dims))
               (and (natp res-width)
                    (integerp res-width)
                    (<= 0 res-width)))))

  )



(define str::hexify-4vec ((x sv::4vec-p))
  :returns (res stringp)
  (if (integerp x)
      (str::hexify x)
    (str::cat "(" (str::hexify (sv::4vec->upper x))
              " . " (str::hexify (sv::4vec->lower x))
              ")")))

(define str::binify-4vec ((x sv::4vec-p))
  :returns (res stringp)
  (if (integerp x)
      (str::binify x)
    (str::cat "(" (str::binify (sv::4vec->upper x))
              " . " (str::binify (sv::4vec->lower x))
              ")")))

(define collect-and-cdr-lists-that-start-with (x (lst acl2::true-list-listp))
  :returns (result acl2::true-list-listp :hyp (acl2::true-list-listp lst))
  (if (atom lst)
      nil
    (b* ((rest (collect-and-cdr-lists-that-start-with x (cdr lst))))
      (if (and (consp (car lst))
               (equal (caar lst) x))
          (cons (cdar lst) rest)
        rest))))

(define extract-vl-types-generate-debug-vector-functions ((debug-fn-name symbolp)
                                                          (debug-vector-fn-name symbolp)
                                                          (pkg-sym symbolp))
  (b* ((debug-vector-fn-name (or debug-vector-fn-name 'debug-extracted-vl-type-array))
       (debug-vector-loop-fn-name
        (intern-in-package-of-symbol
         (str::cat (symbol-name debug-vector-fn-name) "-LOOP")
         pkg-sym)))
    `(defines ,debug-vector-fn-name

       (define ,debug-vector-fn-name ((value sv::4vec-p)
                                      (dims vl-coretype-collected-dims-p)
                                      (excludes (and (acl2::true-list-listp excludes)
                                                     (true-listp excludes)))
                                      (depth-limit integerp)
                                      &optional
                                      ((trace stringp) '"")
                                      ((measure-cnt natp) '0) ;; only here to prove the measure.
                                      )
         :measure (acl2::nat-list-measure (list (len dims) measure-cnt))
         :no-function t
         :normalize nil
         (declare (ignorable measure-cnt))
         (cond ((atom dims)
                (b* ((result ,(if debug-fn-name `(,debug-fn-name value excludes depth-limit) 'value))
                     ((when (equal trace "")) (list result)))
                  (list (,(if debug-fn-name 'cons 'list) trace result))))
               ((< depth-limit 1)
                (b* ((result `(:value ,value
                                      :hex ,(str::hexify-4vec value)
                                      :limit-reached))
                     ((when (equal trace "")) (list result)))
                  (list (cons trace result))))
               (t (b* (((list* slice-size msb lsb) (car dims))
                       (result (,debug-vector-loop-fn-name lsb
                                                           slice-size
                                                           (1+ (- msb lsb))
                                                           value
                                                           (cdr dims)
                                                           excludes
                                                           (1- depth-limit)
                                                           trace)))
                    result))))

       (define ,debug-vector-loop-fn-name ((lsb-offset natp)
                                           (slice-size natp)
                                           (cnt natp)
                                           (value sv::4vec-p)
                                           (dims vl-coretype-collected-dims-p)
                                           (excludes (and (acl2::true-list-listp excludes)
                                                          (true-listp excludes)))
                                           (depth-limit integerp)
                                           (trace stringp))
         :measure (acl2::nat-list-measure (list (len dims) cnt))
         :no-function t
         :normalize nil
         (if (zp cnt)
             nil
           (b* ((cnt (1- cnt))
                (rest (,debug-vector-loop-fn-name lsb-offset
                                                  slice-size
                                                  cnt
                                                  value
                                                  dims
                                                  excludes
                                                  depth-limit
                                                  trace))
                (user-index (+ cnt lsb-offset))
                (cur-slice-value
                 (sv::4vec-part-select (* slice-size cnt) slice-size value)
                 #|(acl2::part-select value
                 :low (* slice-size cnt)
                 :width slice-size)|#)
                (cur-slice-trace (str::cat trace
                                           "["
                                           (str::nat-to-dec-string user-index)
                                           "]"))
                ((when (member-equal (list user-index) excludes))
                 rest)
                ((when (member-equal (list user-index '*) excludes))
                 (append rest
                         `((,cur-slice-trace :value ,cur-slice-value
                                             :hex ,(str::hexify-4vec cur-slice-value)
                                             :fields-excluded))))

                (excludes (collect-and-cdr-lists-that-start-with user-index excludes))

                (cur-slice-res (,debug-vector-fn-name cur-slice-value
                                                      dims
                                                      excludes
                                                      depth-limit
                                                      cur-slice-trace
                                                      cnt)))
             (append rest cur-slice-res)))))))

(local (in-theory (enable sv::4vec-p-when-integerp)))

(make-event
 (extract-vl-types-generate-debug-vector-functions nil nil 'pkg-sym))



#!VL
(define vl-types->acl2-types-parse-args ((args stringp)
                                         (pkg-sym symbolp))
  :mode :program
  (b* (((when (equal args ""))
        nil)
       (bracket-i (search "[" args))
       (dot-i (search "." args)))
    (cond ((and (not bracket-i)
                (not dot-i))
           (list (intern-in-package-of-symbol args pkg-sym)))
          ((equal dot-i 0)
           (vl-types->acl2-types-parse-args (subseq args 1 nil) pkg-sym))
          ((or (not bracket-i)
               (and dot-i
                    (equal (min bracket-i dot-i) dot-i)))
           (b* ((this (subseq args 0 dot-i))
                (rest (subseq args (1+ dot-i) nil))
                (rest (vl-types->acl2-types-parse-args rest pkg-sym)))
             (cons (intern-in-package-of-symbol this pkg-sym)
                   rest)))
          ((equal bracket-i 0)
           (b* ((close-bracket-i (search "]" args))
                ((Unless close-bracket-i)
                 (raise "Could not find close bracket for args: ~s0~%" args))
                (num (explode (subseq args 1 close-bracket-i)))
                ((unless (str::dec-digit-char-list*p num))
                 (raise "Invalid sequence of indices are given: ~p0. There needs to be a positive integer between brackets.~%" args))

                ((mv num & &) (Str::parse-nat-from-charlist num 0 0))

                (rest (vl-types->acl2-types-parse-args
                       (subseq args (1+ close-bracket-i) nil)
                       pkg-sym)))
             (cons num rest)))
          (t (b* ((this (subseq args 0 bracket-i))
                  (rest (subseq args bracket-i nil))
                  (rest (vl-types->acl2-types-parse-args rest pkg-sym)))
               (cons (intern-in-package-of-symbol this pkg-sym)
                     rest))))))

(define vl-types->acl2-types-parse-args-list ((args-lst string-listp)
                                              (pkg-sym symbolp))
  :mode :program
  (if (atom args-lst)
      nil
    (cons (vl-types->acl2-types-parse-args (car args-lst) pkg-sym)
          (vl-types->acl2-types-parse-args-list (cdr args-lst) pkg-sym))))
