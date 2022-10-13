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

(include-book "scopestack")
(include-book "../expr")

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/part-install" :dir :system)

;; (include-book "projects/apply/top" :dir :system)

(progn

  (defthm natp-of-expt
    (implies (and (natp x) (natp y))
             (<= 0 (expt x y))))

  (defthm natp-of-*
    (implies (and (natp x) (natp y))
             (<= 0 (* x y))))

  (defthm natp-of-+
    (implies (and (natp x) (natp y))
             (<= 0 (+ x y))))
  (local
   (in-theory (e/d ()
                   (expt distributivity
                         floor acl2::loghead acl2::logtail mod
                         bitops::part-select-width-low$inline)))))

#!VL
(defsection vl-coretype-collect-dims

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

  (define vl-coretype-collect-dims-aux ((dims vl-dimensionlist-p)
                                        (acc-size natp))
    :returns (mv (out-dims true-listp)
                 (res-size natp :hyp (natp acc-size)
                           :rule-classes (:type-prescription :rewrite)))
    :verify-guards nil
    (if (atom dims)
        (mv nil acc-size)
      (b* (((mv rest acc-size) (vl-coretype-collect-dims-aux (cdr dims) acc-size))
           (dim (car dims))

           ;; now pull msb and lsb:
           ((unless (equal (vl-dimension-kind dim) :range))
            (mv (raise "(equal (vl-dimension-kind dim) :range) failed for: " dim) 0))
           (msb (vl-range->msb (vl-dimension->range dim)))
           ((unless (equal (vl-expr-kind msb) :vl-literal))
            (mv (raise "(equal (vl-expr-kind msb) :vl-literal) failed for: " dim) 0))
           (msb-val (vl-literal->val msb))
           ((unless (equal (vl-value-kind msb-val) :vl-constint))
            (mv (raise "(equal (vl-value-kind msb-val) :vl-constint) failed for: " dim) 0))
           (msb-val-val (vl-constint->value msb-val))
           (lsb (vl-range->lsb (vl-dimension->range dim)))
           ((unless (equal (vl-expr-kind lsb) :vl-literal))
            (mv (raise "(equal (vl-expr-kind lsb) :vl-literal) failed for: " dim) 0))
           (lsb-val (vl-literal->val lsb))
           ((unless (equal (vl-value-kind lsb-val) :vl-constint))
            (mv (raise "(equal (vl-value-kind lsb-val) :vl-constint) failed for: " dim) 0))
           (lsb-val-val (vl-constint->value lsb-val))
           ((Unless (>= msb-val-val lsb-val-val))
            (mv (raise "(>= msb-val-val lsb-val-val) failed for: " dim) 0)))
        (mv (cons (list* acc-size msb-val-val lsb-val-val)
                  rest)
            (* acc-size (+ 1 msb-val-val (- lsb-val-val))))))
    ///
    (defret vl-coretype-collected-dims-p-<fn>
      (vl-coretype-collected-dims-p out-dims)
      :hyp (and (vl-dimensionlist-p dims)
                (natp acc-size))
      :rule-classes (:forward-chaining
                     :type-prescription
                     :rewrite))
    (verify-guards vl-coretype-collect-dims-aux))

  (define vl-coretype-collect-dims (x)
    :guard (and (vl-datatype-p x)
                (equal (vl-datatype-kind x)
                       :VL-CORETYPE))
    :returns (mv (collected-dims vl-coretype-collected-dims-p
                                 :hyp (and (vl-datatype-p x)
                                           (equal (vl-datatype-kind x)
                                                  :VL-CORETYPE))
                                 :rule-classes (:forward-chaining
                                                :type-prescription
                                                :rewrite))
                 (size natp))
    ;; Returns dimension triples For example, say we have:
    ;; bit [1:0][3:0] packed_and_unpacked [2:0][7:2]
    ;; Then, the function will return:
    ;; ((48 2 . 0) (8 7 . 2) (4 1 . 0) (1 3 . 0))
    ;; each entry is: size of each entry, msb and lsb.
    ;; For example (4 1 . 0) signifies indices from 1 and 0, and each entry (1 or
    ;; 0) can be represented with 4 bits.
    ;; The  second return  value  signifies the  total size  of  the vector  in
    ;; question. In the case of the above function, it will be 144.
    (b* (((vl-coretype x) x)
         ((unless (or (equal x.name :vl-logic)
                      (equal x.name :vl-bit)))
          (mv (raise "(or (equal x.name :vl-logic)
                    (equal x.name :vl-bit))
 failed for: " x) 0))
         ((unless (equal x.signedp nil))
          (mv (raise "(equal x.signedp nil) failed for: " x) 0))

         ((mv dims2 acc-size) (vl-coretype-collect-dims-aux x.pdims 1))

         ((mv dims1 acc-size) (vl-coretype-collect-dims-aux x.udims acc-size))
         (collected-dims (append dims1 dims2)))
      (mv collected-dims acc-size)))

  )

(define collect-and-cdr-lists-that-start-with (x (lst true-list-listp))
  :returns (result true-list-listp :hyp (true-list-listp lst))
  (if (atom lst)
      nil
    (b* ((rest (collect-and-cdr-lists-that-start-with x (cdr lst))))
      (if (and (consp (car lst))
               (equal (caar lst) x))
          (cons (cdar lst) rest)
        rest))))

#!VL
(define vl-enum-values->acl2-types-cases ((values vl-exprlist-p)
                                          (items vl-enumitemlist-p))
  :returns (mv string-to-int-cases int-to-string-cases)
  (if (or (atom values)
          (atom items))
      (if (equal values items) (mv nil nil)
        (mv (raise "Expected items and values to be of the same length~%") nil))
    (b* (((mv string-to-int-cases int-to-string-cases)
          (vl-enum-values->acl2-types-cases (cdr values) (cdr items)))
         ((unless (equal (vl-expr-kind (car values)) :vl-literal))
          (mv (raise "(equal (vl-expr-kind (car values)) :vl-literal) failed for values=~p0~%" values)
              nil))
         ((vl-literal x) (car values))

         ((unless (equal (vl-value-kind x.val) :vl-constint))
          (mv (raise "(equal (vl-value-kind x.val) :vl-constint) failed for x=~p0~%" x)
              nil))

         ((unless (equal (vl-value-kind x.val) :vl-constint))
          (mv (raise "(equal (vl-value-kind x.val) :vl-constint) failed for x=~p0~%" x)
              nil))
         (value (vl-constint->value x.val))
         ((vl-enumitem cur) (car items))
         ((unless (equal cur.range nil))
          (mv (raise "Unexpected enumitem (~p0). Check for (equal cur.range nil) has failed.~%" cur)
              nil))
         (int-to-string-case
          `(,value ,cur.name))
         (string-to-int-case
          `(,cur.name ,value)))
      (mv (cons string-to-int-case string-to-int-cases)
          (cons int-to-string-case int-to-string-cases)))))

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
                ((unless (str::dec-digit-char-listp num))
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

(define extract-vl-types-generate-macros
  (accessor-macro-name
   changer-macro-name-aux
   changer-macro-name
   ranges-fn-name pkg-sym)
  `(
    (define ,changer-macro-name-aux (args)
      :mode :program
      (b* (((when (atom args)) nil)
           ((unless (and (consp (cdr args))
                         (stringp (car args))))
            (raise "Args should be given as pairs, first element of each is a string and the second is the desired value to update"))
           (rest (,changer-macro-name-aux (cddr args)))
           (cur-arg (vl-types->acl2-types-parse-args
                     (car args) ',pkg-sym))
           ((mv start width)
            (,ranges-fn-name 0 cur-arg)))
        (cons (list 'value (list 'acl2::part-install
                                 (cadr args)
                                 'value
                                 :low start :width width))
              rest)))

    (defmacro ,changer-macro-name (value &rest args)
      (b* ((assignments (,changer-macro-name-aux args)))
        (list 'b*
              (cons (list 'value value)
                    assignments)
              'value)))

    (defmacro ,accessor-macro-name
        (value &optional (args '""))
      (b* ((args (vl-types->acl2-types-parse-args
                  args ',pkg-sym))
           ((mv start width)
            (,ranges-fn-name 0 args)))
        (list 'acl2::part-select
              value :low start :width width)))))

(define extract-vl-types-generate-debug-vector-functions ((debug-fn-name symbolp)
                                                          (debug-vector-fn-name symbolp)
                                                          (pkg-sym symbolp))
  (b* ((debug-vector-fn-name (if debug-fn-name debug-vector-fn-name 'debug-extracted-vl-type-array))
       (debug-vector-loop-fn-name
        (intern-in-package-of-symbol
         (str::cat (symbol-name debug-vector-fn-name) "-LOOP")
         pkg-sym)))
    `(defines ,debug-vector-fn-name

       (define ,debug-vector-fn-name ((value integerp)
                                      (dims vl-coretype-collected-dims-p)
                                      (excludes (and (true-list-listp excludes)
                                                     (true-listp excludes)))
                                      &optional
                                      ((trace stringp) '"")
                                      ((measure-cnt natp) '0) ;; only here to prove the measure.
                                      )
         :measure (acl2::nat-list-measure (list (len dims) measure-cnt))
         :no-function t
         (declare (ignorable measure-cnt))
         (if (atom dims)
             (b* ((result ,(if debug-fn-name `(,debug-fn-name value excludes) 'value))
                  ((when (equal trace "")) (list result)))
               (list (,(if debug-fn-name 'cons 'list) trace result)))
           (b* (((list* slice-size msb lsb) (car dims))
                (result (,debug-vector-loop-fn-name lsb
                                                    slice-size
                                                    (1+ (- msb lsb))
                                                    value
                                                    (cdr dims)
                                                    excludes
                                                    trace)))
             result)))

       (define ,debug-vector-loop-fn-name ((lsb-offset natp)
                                           (slice-size natp)
                                           (cnt natp)
                                           (value integerp)
                                           (dims vl-coretype-collected-dims-p)
                                           (excludes (and (true-list-listp excludes)
                                                          (true-listp excludes)))
                                           (trace stringp))
         :measure (acl2::nat-list-measure (list (len dims) cnt))
         :no-function t
         (if (zp cnt)
             nil
           (b* ((cnt (1- cnt))
                (rest (,debug-vector-loop-fn-name lsb-offset
                                                  slice-size
                                                  cnt
                                                  value
                                                  dims
                                                  excludes
                                                  trace))
                (user-index (+ cnt lsb-offset))
                (cur-slice-value
                 (acl2::part-select value
                                    :low (* slice-size cnt)
                                    :width slice-size))
                (cur-slice-trace (str::cat trace
                                           "["
                                           (str::nat-to-dec-string user-index)
                                           "]"))
                ((when (member-equal (list user-index) excludes))
                 rest)
                ((when (member-equal (list user-index '*) excludes))
                 (append rest
                         `((,cur-slice-trace :value ,cur-slice-value
                                             :hex ,(str::hexify cur-slice-value)
                                             :fields-excluded))))

                (excludes (collect-and-cdr-lists-that-start-with user-index excludes))

                (cur-slice-res (,debug-vector-fn-name cur-slice-value
                                                      dims
                                                      excludes
                                                      cur-slice-trace
                                                      cnt)))
             (append rest cur-slice-res)))))))

(make-event
 (extract-vl-types-generate-debug-vector-functions nil nil 'pkg-sym))

#!VL
(defines vl-types->acl2-types

  (define vl-structmemberlist->acl2-types (members structp pkg-sym)
    :guard (and (vl-structmemberlist-p members)
                )
    :mode :program
    :returns (mv member-range-cases
                 member-debug-clauses
                 member-events
                 (total-size natp))
    (if (atom members)
        (mv nil nil nil 0)
      (b* (((mv rest-range-cases rest-debug-clauses rest-events rest-size)
            (vl-structmemberlist->acl2-types (cdr members) structp  pkg-sym))

           ((mv this-range-case this-debug-clause this-events this-size)
            (vl-structmember->acl2-types (car members)
                                         (and structp rest-size)
                                         pkg-sym)))
        (mv (cons this-range-case rest-range-cases)
            (cons this-debug-clause rest-debug-clauses)
            (append this-events rest-events)
            (if structp
                (+ this-size rest-size)
              (max this-size rest-size))))))

  (define vl-structmember->acl2-types (member offset pkg-sym)
    :guard (vl-structmember-p member)
    :returns (mv range-case-statement debug-clause events size)
    ;; when creating assignemnts, we assume there is a rest-args, which is a true-listp
    (b* (((vl-structmember member) member))
      (case (vl-datatype-kind member.type)
        (:VL-CORETYPE
         (b* (((mv collected-dims size) (vl-coretype-collect-dims member.type))
              (member.symbol (intern-in-package-of-symbol member.name pkg-sym))
              (ranges-case-statement
               `(,member.symbol
                 (b* (,@(and offset
                             `((offset ,offset)
                               (start (+ start offset))))
                      (width ,size)
                      (collected-dims ',collected-dims))
                   (get-extracted-vl-type-array-ranges start width
                                                       collected-dims rest-args
                                                       ,member.name nil))))
              (events nil)
              (debug-clause
               `(and (not (member-equal (list ',member.symbol) excludes))
                     (list
                      (cons ,member.name
                            (b* ((start ,(if offset offset 0))
                                 (width ,size)
                                 (value (acl2::part-select value :low start :width width))
                                 ((when (member-equal (list ',member.symbol '*) excludes))
                                  `(:value ,value :hex ,(str::hexify value) :fields-excluded))

                                 (excludes (collect-and-cdr-lists-that-start-with ',member.symbol excludes))
                                 (collected-dims ',collected-dims))
                              (debug-extracted-vl-type-array value collected-dims excludes)))))))
           (mv ranges-case-statement debug-clause events size)))

        (::VL-USERTYPE
         (b* (((vl-usertype x) member.type)
              ((mv events size)
               (vl-types->acl2-types-new-type x.name x.res pkg-sym))
              ((mv dims2 size) (vl-coretype-collect-dims-aux x.pdims size))
              ((mv dims1 size) (vl-coretype-collect-dims-aux x.udims size))
              (collected-dims (append dims1 dims2))
              (ranges-fn-name (intern-in-package-of-symbol (str::cat x.name "-RANGES") pkg-sym))
              (debug-fn-name (intern-in-package-of-symbol (str::cat x.name "-DEBUG-FN") pkg-sym))
              (debug-vector-fn-name (intern-in-package-of-symbol (str::cat x.name "-VECTOR-DEBUG-FN") pkg-sym))
              (member.symbol (intern-in-package-of-symbol member.name pkg-sym))
              (ranges-case-statement
               `(,member.symbol
                 ,(if collected-dims
                      `(b* (,@(and offset
                                   `((offset ,offset)
                                     (start (+ start offset))))
                            (width ,size)
                            (collected-dims ',collected-dims)
                            ((mv start width)
                             (get-extracted-vl-type-array-ranges start width
                                                                 collected-dims
                                                                 rest-args
                                                                 ,member.name t))
                            (rest-args (nthcdr ,(len collected-dims) rest-args))
                            ((mv start width) (if (equal rest-args nil)
                                                  (mv start width)
                                                (,ranges-fn-name start rest-args))))
                         (mv start width))
                    `(,ranges-fn-name ,(if offset
                                           `(+ start ,offset)
                                         'start)
                                      rest-args))))
              (debug-clause
               `(and (not (member-equal (list ',member.symbol) excludes))
                     (list
                      (cons ,member.name
                            (b* ((start ,(if offset offset 0))
                                 (width ,size)
                                 (value (acl2::part-select value :low start :width width))
                                 ((when (member-equal (list ',member.symbol '*) excludes))
                                  `(:value ,value :hex ,(str::hexify value) :fields-excluded))
                                 (excludes (collect-and-cdr-lists-that-start-with ',member.symbol
                                                                                  excludes))
                                 ,@(and collected-dims
                                        `((collected-dims ',collected-dims))))
                              ,(if collected-dims
                                   `(,debug-vector-fn-name value collected-dims excludes)
                                 `(,debug-fn-name value excludes))))))))
           (mv ranges-case-statement debug-clause events size)))
        (otherwise
         (progn$ (raise "Unexpected vl-structmember type: ~p0 ~%" member)
                 (mv nil nil nil 0))))))

  (define vl-types->acl2-types-new-type (name vl-datatype (pkg-sym symbolp))
    :returns (mv (events)
                 (size natp))
    (b* (((unless (stringp name))
          (mv (raise "(stringp name) is failed for: ~p0 ~%" name) 0))
         ((unless (vl-datatype-p vl-datatype))
          (mv (raise "(stringp name) is failed for: ~p0 ~%" name) 0))
         (ranges-fn-name (intern-in-package-of-symbol (str::cat name "-RANGES") pkg-sym))
         (debug-fn-name (intern-in-package-of-symbol (str::cat name "-DEBUG-FN") pkg-sym))
         (debug-vector-fn-name (intern-in-package-of-symbol (str::cat name "-VECTOR-DEBUG-FN") pkg-sym))
         (debug-macro-name (intern-in-package-of-symbol (str::cat name "-DEBUG") pkg-sym))

         (changer-macro-name-aux (INTERN-IN-PACKAGE-OF-SYMBOL (str::cat "CHANGE-" name "-AUX") pkg-sym))
         (changer-macro-name (INTERN-IN-PACKAGE-OF-SYMBOL (str::cat "CHANGE-" name) pkg-sym))
         (accessor-macro-name (INTERN-IN-PACKAGE-OF-SYMBOL name pkg-sym)))
      (case (vl-datatype-kind vl-datatype)
        (:vl-coretype
         (b* (((mv collected-dims size) (vl-coretype-collect-dims vl-datatype))

              ;; accessor function expects indices only in a list such as '(1 2 3)
              (events
               `((define ,ranges-fn-name
                   ((start natp) (args true-listp))
                   (b* ((width ,size)
                        ((when (atom args)) (mv start width))
                        (dims ',collected-dims))
                     (get-extracted-vl-type-array-ranges start width dims args
                                                         ,name nil)))
                 ,@(extract-vl-types-generate-macros
                    accessor-macro-name
                    changer-macro-name-aux changer-macro-name ranges-fn-name pkg-sym)

                 (define ,debug-fn-name ((value integerp)
                                         (excludes (and (true-list-listp excludes)
                                                        (true-listp excludes))))
                   (declare (ignorable excludes))
                   (b* ((value (acl2::loghead ,size value)))
                     ,(cond ((atom collected-dims)
                             'value)
                            ((atom (cdr collected-dims))
                             `(list :value
                                    value
                                    :hex (str::hexify value)
                                    :bin (str::binify value)))
                            (t
                             `(debug-extracted-vl-type-array value ',collected-dims excludes)))))

                 ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                    debug-vector-fn-name
                                                                    pkg-sym)

                 (defmacro ,debug-macro-name (value &key exclude)
                   (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                     (list ',debug-fn-name value (list 'quote excludes))))

                 #|(defmacro ,accessor-macro-name (value &optional (args '""))
                 (list ',accessor-fn-name value
                 (list 'quote
                 (vl-types->acl2-types-parse-args
                 args ',pkg-sym))))|#)))
           (mv events size)))
        (:vl-struct
         (b* (((vl-struct x) vl-datatype)
              ((unless (equal x.pdims nil))
               (mv (raise "(equal x.pdims nil) failed for: " x) 0))
              ((unless (equal x.udims nil))
               (mv (raise "(equal x.udims nil) failed for: " x) 0))
              ((mv member-cases member-debug-clauses member-events size)
               (vl-structmemberlist->acl2-types x.members t pkg-sym))

              (this-events
               `((define ,ranges-fn-name
                   ((start natp) (args true-listp))
                   (b* ((width ,size)
                        ((when (atom args)) (mv start width))
                        (cur-arg (car args))
                        (rest-args (cdr args)))
                     (case cur-arg
                       ,@member-cases
                       (otherwise
                        (progn$ (raise "An invalid field (~p0) is given for vl-struct type ~s1 ~%" cur-arg ,name)
                                (mv start width))))))
                 ,@(extract-vl-types-generate-macros
                    accessor-macro-name
                    changer-macro-name-aux changer-macro-name ranges-fn-name pkg-sym)

                 (define ,debug-fn-name ((value integerp)
                                         (excludes (and (true-list-listp excludes)
                                                        (true-listp excludes))))
                   (declare (ignorable excludes))
                   (flatten
                    (list ;; :value (acl2::loghead ,size value)
                     ,@member-debug-clauses)))

                 ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                    debug-vector-fn-name
                                                                    pkg-sym)

                 (defmacro ,debug-macro-name (value &key exclude)
                   (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                     (list ',debug-fn-name value (list 'quote excludes))))

                 )))
           (mv (append member-events this-events) size)))
        (:vl-union
         ;; TODO: BOZO: not checking taggedp, signedp, and packedp fields at all...
         (b* (((vl-union x) vl-datatype)
              ((unless (equal x.pdims nil))
               (mv (raise "(equal x.pdims nil) failed for: " x) 0))
              ((unless (equal x.udims nil))
               (mv (raise "(equal x.udims nil) failed for: " x) 0))
              ((Unless (equal x.taggedp nil))
               (mv (raise "(equal x.taggedp nil) failed for: " x) 0))
              ((mv member-cases member-debug-clauses member-events size)
               (vl-structmemberlist->acl2-types x.members nil pkg-sym))

              (this-events
               `((define ,ranges-fn-name
                   ((start natp) (args true-listp))
                   (b* ((width ,size)
                        ((when (atom args)) (mv start width))
                        (cur-arg (car args))
                        (rest-args (cdr args)))
                     (case cur-arg
                       ,@member-cases
                       (otherwise
                        (progn$ (raise "An invalid field (~p0) is given for vl-struct type ~s1 ~%" cur-arg ,name)
                                (mv start width))))))
                 ,@(extract-vl-types-generate-macros
                    accessor-macro-name
                    changer-macro-name-aux changer-macro-name ranges-fn-name pkg-sym)

                 (define ,debug-fn-name ((value integerp)
                                         (excludes (and (true-list-listp excludes)
                                                        (true-listp excludes))))
                   (declare (ignorable excludes))
                   (flatten ;; :value (acl2::loghead ,size value)
                    (list ,@member-debug-clauses)))

                 ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                    debug-vector-fn-name
                                                                    pkg-sym)

                 (defmacro ,debug-macro-name (value &key exclude)
                   (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                     (list ',debug-fn-name value (list 'quote excludes))))
                 )))
           (mv (append member-events this-events) size)))
        (:vl-enum
         (b* (((vl-enum x) vl-datatype)
              ((unless (equal x.pdims nil))
               (mv (raise "(equal x.pdims nil) failed for: " x) 0))
              ((unless (equal x.udims nil))
               (mv (raise "(equal x.udims nil) failed for: " x) 0))
              ((unless (equal (vl-datatype-kind x.basetype)
                              :vl-coretype))
               (mv (raise "Expected to have :vl-coretype for the given vl-enum type: ~p0.~%" x) 0))
              ((mv & size) (vl-coretype-collect-dims x.basetype))
              ((mv string-to-int-cases int-to-string-cases)
               (vl-enum-values->acl2-types-cases x.values x.items))

              (this-events
               `((define ,ranges-fn-name
                   ((start natp) (args true-listp))
                   (b* ((width ,size)
                        ((when args)
                         (progn$ (raise "Unexpected arguments are passed: ~p0 ~%" args)
                                 (mv start width))))
                     (mv start width)))

                 (define ,accessor-macro-name ((value))
                   :guard (or (integerp value)
                              (stringp value))

                   (if (integerp value)
                       (case value
                         ,@int-to-string-cases
                         (otherwise :invalid-enumitem ;;value
                                    ))
                     (case-match value
                       ,@string-to-int-cases
                       (& (progn$ (cw "Invalid enum type given: ~s0 ~%" value)
                                  -1)
                          ;;value
                          ))))

                 (define ,debug-fn-name ((value integerp)
                                         (excludes))
                   (declare (ignorable excludes))
                   (list :value value
                         :string
                         (,accessor-macro-name value)))

                 ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                    debug-vector-fn-name
                                                                    pkg-sym)

                 (defmacro ,debug-macro-name (value)
                   (list ',debug-fn-name value nil))

                 #|(defmacro ,changer-macro-name ((old-value)
                 (new-value))
                 (declare (ignorable old-value))
                 (list 'acl2::loghead ,size new-value))|#
                 #|(defmacro ,macro-name (value &optional (args '""))
                 (list ',fn-name value
                 (list 'quote
                 (vl-types->acl2-types-parse-args
                 args ',pkg-sym))))|#)))
           (mv this-events size)))
        (otherwise
         (mv (raise "Unexpected vl-datatype: ~p0 ~%" vl-datatype)  0)
         ))))
  )

(define vl-typedef->acl2-types (x pkg-sym)
  :mode :program
  (b* (((unless (vl-typedef-p x))
        (raise "Expected to get a vl::vl-typedef-p"))
       ((vl-typedef x) x)
       ((mv events ?size)
        (vl-types->acl2-types-new-type x.name x.type pkg-sym)))
    events))

#|

(make-event
`(encapsulate
nil
,@(vl-typedef->acl2-types (@ test) 's)))

|#

;; :i-am-here

(define extract-vl-types-fn (design
                             (module acl2::maybe-stringp)
                             vl-types
                             pkg-sym)
  :mode :program
  (if (atom vl-types)
      nil
    (b* ((rest (extract-vl-types-fn design module (cdr vl-types) pkg-sym))
         (vl-typedef
          (if module
              (b* ((ss (vl::vl-scopestack-init design))
                   (mod (vl::vl-scopestack-find-definition module ss))
                   (mod-ss (vl::vl-scopestack-push mod ss)))
                (vl::vl-scopestack-find-item (car vl-types) mod-ss))
            (vl::vl-scopestack-find-item (car vl-types)
                                         (vl::vl-scopestack-init design))))
         (events (vl::vl-typedef->acl2-types vl-typedef pkg-sym)))
      (append events rest))))

(defmacro extract-vl-types (design module &rest vl-types)
  `(make-event
    (b* ((events (extract-vl-types-fn ,design ,module ',vl-types
                                      ;; to  prevent  conflicts when  the  same
                                      ;; type  is  extracted  across  different
                                      ;; books with different design constants:
                                      (pkg-witness (symbol-package-name ',design))
                                      ;;(intern-in-package-of-symbol "PKG-SYM" ',design)
                                      )))
      `(encapsulate
         nil
         (local
          (in-theory (e/d ()
                          (expt distributivity
                                floor acl2::loghead acl2::logtail mod
                                bitops::part-select-width-low$inline))))
         ,@events
         ))))

;;(include-book "xdoc/debug" :dir :system)

(defxdoc extract-vl-types
  :parents (mlib)
  :short "Extract Verilog data types to access them with ACL2 functions"
  :long "<p>Signature:</p>

@({(extract-vl-types design module &rest vl-types)})

<p>Example call:</p>
@({
(vl::extract-vl-types  *my-good-simplified-svex-design*
                       \"my_module_name\"
                       \"my_data_struct\" \"my_data_struct2\")
})

<p> The above call will generate an event that submits ACL2 accessor functions for \"my_data_struct\", \"my_data_struct2\", and their children if there are any. </p>

<ul>
<li> \"design\" should be the \"good\" output from @(see vl::vl-design->sv-design) stage.</li>
<li> \"module-name\" can be nil or a Verilog module name. When nil, the program only searches for globally defined data structures. When non-nil, it searches in the scope of that given module name. </li>
<li> \"vl-types\" can be a number of Verilog data structures. The program will generate accessor functions for these data structures as well as their children. These data types can be \"struct\", \"enum\", \"union\", or packed/unpacked vectors.
</li>

</ul>

<p> Using the generated functions, users can access a part of a given data structure. For example, if we have a large struct with a lot of fields, say named \"t_main\", then the program will generate a macro with the same name: |t_main| (since Verilog is case-sensitive, or function/macro names for the accessors are also made case-sensitive). Say that we have a variable called \"main\" in our conjectures representing a signal of type \"t_main\" (assuming we use (@see acl2::defsvtv) semantics). Then, we can access individual fields of this signal using the generated |t_main| macro. For example: (|t_main| main \"data[0].dword[3]\"), (|t_main| main \"uop.size\") etc.</p>

<p> In case of enumarated types, their generator functions can take a string or an integer, and return corresponding integer or string values, respectively.
</p>

<p> vl::extract-vl-types will also generate \"change\" macros for every type. For example: (change-|t_main| main \"data[0].dword[3]\" 12) will set the \"data[0].dword[3]\" of main to 12. More arguments can be passed to change other entries in the same call: (change-|t_main| main \"data[0].dword[3]\" 12 \"uop.size\" 0).
</p>

<p> The program will also created \"debug\" macros for every type. For example: (|t_main|-debug main) will return a large term that has all the entries for a given concrete value \"main\". Debug functions can also take a list of fields to exclude from printing. For example: (|t_main|-debug main :exclude (\"uop.size\" \"data[0]\" \"data[1].dword\" \"data[2].*\")). When there is a \".*\" at the end of a skipped argument (e.g., \"data[2].*\"), then the value of that argument (e.g., \"data[2]\") will be included but not its fields. </p>

"

  )
