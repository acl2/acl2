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
(include-book "../loader/filemap")
(include-book "../loader/read-file")

(include-book "extract-vl-types-support")

;;(include-book "centaur/bitops/part-select" :dir :system)
;;(include-book "centaur/bitops/part-install" :dir :system)

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


  (defthm 4vec-p-of-*
    (implies (and (integerp x) (integerp y))
             (sv::4vec-p (* x y)))
    :hints (("Goal"
             :in-theory (e/d (sv::4vec-p) ()))))

  (defthm 4vec-p-of-+
    (implies (and (integerp x) (integerp y))
             (sv::4vec-p (+ x y)))
    :hints (("Goal"
             :in-theory (e/d (sv::4vec-p) ()))))

  (defthm TRUE-LIST-LISTP-of-PAIRLIS$
    (implies (acl2::true-list-listp lst)
             (acl2::true-list-listp (pairlis$ x lst)))
    :hints (("Goal"
             :in-theory (e/d (pairlis$ acl2::true-list-listp) ()))))

  (defthmd 4VEC-P-WHEN-INTEGERP
    (Implies (integerp x)
             (sv::4vec-p x))
    :hints (("Goal"
             :in-theory (e/d (sv::4vec-p) ()))))

  (defthm 4VEC-P-WHEN-INTEGERP-type-prescription
    (Implies (integerp x)
             (sv::4vec-p x))
    :rule-classes :type-prescription
    :hints (("Goal"
             :in-theory (e/d (sv::4vec-p) ()))))

  (defthm integerp-of-4vec-part-select
    (implies (and (natp lsb)
                  (natp width)
                  (integerp val))
             (integerp (sv::4vec-part-select lsb width val)))
    :rule-classes (:rewrite :type-prescription)
    :hints (("Goal"
             :in-theory (e/d (SV::4VEC
                              SV::4VEC-CONCAT
                              sv::2vec
                              SV::4VEC-RSH
                              SV::4VEC-SHIFT-CORE
                              sv::4vec-part-select SV::4VEC-ZERO-EXT
                                                   SV::4VEC->UPPER
                                                   sv::4vec->lower)
                             ()))))
  )

(local
 (in-theory (e/d ()
                 (expt distributivity
                       floor acl2::loghead acl2::logtail mod
                       sv::4vec-part-select
                       sv::4vec-p
                       sv::4vec-part-install))))

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

         ((when (equal (vl-value-kind x.val) :vl-weirdint))
          ;; Do not recognize weird-int cases. This will keep it more conservative.
          (progn$
           (cw "Warning: A weird-int case is detected when parsing an ENUM type. Generated functions may not have all the enum type entries. This happened for this entry: ~p0~%" x)
           (mv string-to-int-cases int-to-string-cases)))

         ((unless (equal (vl-value-kind x.val) :vl-constint))
          (mv (raise "~p1 failed for x=~p0~%" x
                     '(equal (vl-value-kind x.val) :vl-constint))
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

(define extract-vl-types-generate-macros
  (&key
   ((name stringp) 'name)
   (accessor-macro-name 'accessor-macro-name)
   (changer-macro-name-aux 'changer-macro-name-aux)
   (changer-macro-name 'changer-macro-name)
   (ranges-fn-name 'ranges-fn-name)
   ((pkg-sym symbolp) 'pkg-sym)
   (constant-value 'nil))
  (declare (ignorable name constant-value))
  `(
    (define ,changer-macro-name-aux (args)
      :parents nil
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
        (cons (list 'value
                    (list 'sv::4vec-part-install
                          start width
                          'value (cadr args))
                    #|(list 'acl2::part-install
                    (cadr args)
                    'value
                    :low start :width width)|#)
              rest)))

    ;;(defsection ,changer-macro-name
    ;;:short (str::cat "Modifier for the VL type @(see |" ,name "|)")
    ;;:long "<p>See @(see vl::extract-vl-types) to see how to use this modifier. </p>"
    (defmacro ,changer-macro-name (,@(if constant-value nil '(value)) &rest args)
      (b* (,@(and constant-value
                  `((__FUNCTION__ ',changer-macro-name)
                    ((std::extract-keyword-args
                      :other-args args
                      (value ',constant-value))
                     args)))
           (assignments (,changer-macro-name-aux args)))
        (list 'b*
              (cons (list 'value value)
                    assignments)
              'value)))
    ;;)

    ;;(defsection ,(intern-in-package-of-symbol (str::cat name " (accessor)") pkg-sym)
    ;;  :short (str::cat "Accessor for the VL type @(see |" ,name "|).")
    ;;  :long "<p>See @(see vl::extract-vl-types) to see how to use this accessor.</p>"
    (defmacro ,accessor-macro-name
        (,@(if constant-value '(&rest args) '(value &optional (args '""))))
      (b* (,@(and constant-value
                  `((__FUNCTION__ ',accessor-macro-name)
                    ((std::extract-keyword-args
                      :other-args args
                      (value ',constant-value))
                     args)
                    ((unless (and (atom (cdr args))
                                  (stringp (or (car args) ""))))
                     (raise "Expected to get one string but got: ~p0" args))
                    (args (or (car args) ""))))
           (args (vl-types->acl2-types-parse-args
                  args ',pkg-sym))
           ((mv start width)
            (,ranges-fn-name 0 args)))
        (list 'sv::4vec-part-select start width value)
        #|(list 'acl2::part-select
        value :low start :width width)|#))
    ;;    )
    ))

(defines vl-types->acl2-types

  (define vl-structmemberlist->acl2-types ((members vl-structmemberlist-p)
                                           (structp booleanp)
                                           (orig-def-alist alistp)
                                           (pkg-sym symbolp))
    :mode :program
    :returns (mv member-range-cases
                 member-debug-clauses
                 member-events
                 (total-size natp))
    (if (atom members)
        (mv nil nil nil 0)
      (b* (((mv rest-range-cases rest-debug-clauses rest-events rest-size)
            (vl-structmemberlist->acl2-types (cdr members) structp orig-def-alist  pkg-sym))

           ((mv this-range-case this-debug-clause this-events this-size)
            (vl-structmember->acl2-types (car members)
                                         (and structp rest-size)
                                         orig-def-alist
                                         pkg-sym
                                         nil)))
        (mv (cons this-range-case rest-range-cases)
            (cons this-debug-clause rest-debug-clauses)
            (append this-events rest-events)
            (if structp
                (+ this-size rest-size)
              (max this-size rest-size))))))

  (define vl-structmember->acl2-types ((member vl-structmember-p)
                                       (offset maybe-natp)
                                       (orig-def-alist alistp)
                                       (pkg-sym symbolp)
                                       (fake-usertype-p booleanp) ;; when parsing vl-usertype, a temp vl-structmember is created to reuse the code in this program. In those cases, fake-usertype-p is set to t.
                                       )
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
                                 (value (sv::4vec-part-select start width value))
                                 #|(value (acl2::part-select value :low start :width width))|#
                                 ((when (member-equal (list ',member.symbol '*) excludes))
                                  `(:value ,value :hex ,(str::hexify-4vec value) :fields-excluded))
                                 #|((when (< depth-limit 1))
                                 `(:value ,value :hex ,(str::hexify value) :limit-reached))|#

                                 (excludes (collect-and-cdr-lists-that-start-with ',member.symbol excludes))
                                 (collected-dims ',collected-dims))
                              (debug-extracted-vl-type-array value collected-dims excludes (1- depth-limit))))))))
           (mv ranges-case-statement debug-clause events size)))

        (:VL-USERTYPE
         (b* (((vl-usertype x) member.type)
              ((mv events size)
               (vl-types->acl2-types-new-type x.name x.res orig-def-alist pkg-sym))
              ((mv dims2 size) (vl-coretype-collect-dims-aux x.pdims size))
              ((mv dims1 size) (vl-coretype-collect-dims-aux x.udims size))
              (collected-dims (append dims1 dims2))
              (x.symbol (intern-in-package-of-symbol x.name pkg-sym))
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
                      (list*
                       ,member.name
                       '(:type ,@(and collected-dims '(:vector)) ,x.symbol)
                       (b* ((start ,(if offset offset 0))
                            (width ,size)
                            (value (sv::4vec-part-select start width value))
                            #|(value (acl2::part-select value :low start :width width))|#

                            ,@(and (not fake-usertype-p)
                                   `(((when (member-equal (list ',member.symbol '*) excludes))
                                      `(:value ,value :hex ,(str::hexify-4vec value) :fields-excluded))
                                     (excludes (collect-and-cdr-lists-that-start-with ',member.symbol
                                                                                      excludes))))
                            ,@(and collected-dims
                                   `((collected-dims ',collected-dims))))
                         ,(if collected-dims
                              `(,debug-vector-fn-name value collected-dims excludes
                                                      ,(if fake-usertype-p `depth-limit `(1- depth-limit)))
                            `(,debug-fn-name value excludes ,(if fake-usertype-p `depth-limit `(1- depth-limit))))))))))
           (mv ranges-case-statement debug-clause events size)))
        (otherwise
         (progn$ (raise "Unexpected vl-structmember type: ~p0 ~%" member)
                 (mv nil nil nil 0))))))

  (define vl-types->acl2-types-new-type (name
                                         vl-datatype
                                         (orig-def-alist alistp)
                                         (pkg-sym symbolp)
                                         &key
                                         (constant-value 'nil))
    :returns (mv (events)
                 (size natp))
    (b* (((unless (stringp name))
          (mv (raise "(stringp name) is failed for: ~p0 ~%" name) 0))
         ((unless (vl-datatype-p vl-datatype))
          (mv (raise "(vl-datatype-p vl-datatype) is failed for: ~p0 ~%" name) 0))
         (symbol (intern-in-package-of-symbol name pkg-sym))
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
               `((defsection ,symbol
                   :autodoc nil
                   :set-as-default-parent t
                   :short ,(str::cat "Accessor, modifier, and debug functions for the extracted " name " VL coretype.")
                   :long ,(str::cat
                           (if (assoc-equal name orig-def-alist) (cdr (assoc-equal name orig-def-alist)) "")
                           "<p>For this type, 3 ACL2 functions/macros are created for users. An accessor: @({(|" name "| value field),})</p> <p>A modifier: @({(change-|"name"| value field-newval-pairs),}) </p> <p>And a debug function to print all the fields: @({(|"name"|-debug value optional-args).})</p><p>These are generated with @(see vl::extract-vl-types). See @(see vl::extract-vl-types) to learn how to use these functions.</p>")

                   (define ,ranges-fn-name ((start natp) (args true-listp))
                     ;;:short ,(str::cat "Calculate the bit locations that a
                     ;;certain field is stored for @(see |" name "|) VL
                     ;;coretype. Not intended to be called by users.")
                     :parents nil
                     (b* ((width ,size)
                          ((when (atom args)) (mv start width))
                          (dims ',collected-dims))
                       (get-extracted-vl-type-array-ranges start width dims args
                                                           ,name nil)))
                   ,@(extract-vl-types-generate-macros)

                   (define ,debug-fn-name ((value sv::4vec-p)
                                           (excludes (and (acl2::true-list-listp excludes)
                                                          (true-listp excludes)))
                                           (depth-limit integerp))
                     :parents nil
                     :normalize nil
                     ;;:short ,(str::cat "Debug aux function for  @(see " name ") VL coretype. Not intended to be called by users.")
                     (declare (ignorable excludes depth-limit))
                     (b* ((value (sv::4vec-part-select 0 ,size value)))
                       ,(cond ((atom collected-dims)
                               'value)
                              ((atom (cdr collected-dims))
                               `(list :value value
                                      :hex (str::hexify-4vec value)
                                      :bin (str::binify-4vec value)))
                              (t
                               `(debug-extracted-vl-type-array value ',collected-dims excludes depth-limit)))))

                   ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                      debug-vector-fn-name
                                                                      pkg-sym)

                   ;;(defsection ,debug-macro-name
                   ;;short ,(str::cat "Debug macro for  @(see " name ") VL coretype.")
                   ;;:long "<p>See @(see vl::extract-vl-types) for explanation of arguments and how to use the debug functionality.</p>"

                   (defmacro ,debug-macro-name (value &key exclude (depth-limit '1000))
                     (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                       (list ',debug-fn-name value (list 'quote excludes)
                             depth-limit)))

                   (table extracted-vl-types ',symbol
                          '((:type :vl-coretype)
                            (:accessor-macro-name ,accessor-macro-name)
                            (:changer-macro-name ,changer-macro-name)
                            (:ranges-fn-name ,ranges-fn-name)
                            (:debug-macro-name ,debug-macro-name)
                            (:debug-fn-name ,debug-fn-name)
                            (:debug-vector-fn-name ,debug-vector-fn-name)))

                   ;;  )
                   ))))
           (mv events size)))
        (:vl-struct
         (b* (((vl-struct x) vl-datatype)
              ((unless (equal x.pdims nil))
               (mv (raise "(equal x.pdims nil) failed for: " x) 0))
              ((unless (equal x.udims nil))
               (mv (raise "(equal x.udims nil) failed for: " x) 0))
              ((mv member-cases member-debug-clauses member-events size)
               (vl-structmemberlist->acl2-types x.members t orig-def-alist pkg-sym))

              (this-events
               `((defsection ,symbol
                   :autodoc nil
                   :set-as-default-parent t
                   :short ,(str::cat "Accessor, modifier, and debug functions for the extracted " name " VL struct type. ")
                   :long ,(str::cat
                           (if (assoc-equal name orig-def-alist) (cdr (assoc-equal name orig-def-alist)) "")
                           "<p>For this type, 3 ACL2 functions/macros are created for users. An accessor: @({(|" name "| value field),})</p> <p>A modifier: @({(change-|"name"| value field-newval-pairs),}) </p> <p>And a debug function to print all the fields: @({(|"name"|-debug value optional-args).})</p><p>These are generated with @(see vl::extract-vl-types). See @(see vl::extract-vl-types) to learn how to use these functions.</p>")

                   (define ,ranges-fn-name ((start natp) (args true-listp))
                     ;;:short ,(str::cat "Calculate the bit locations that a
                     ;;certain field is stored for @(see |" name "|) VL struct
                     ;;type. Not intended to be called by users.")
                     :parents nil
                     (b* ((width ,size)
                          ((when (atom args)) (mv start width))
                          (cur-arg (car args))
                          (rest-args (cdr args)))
                       (case cur-arg
                         ,@member-cases
                         (otherwise
                          (progn$ (raise "An invalid field (~p0) is given for vl-struct type ~s1 ~%" cur-arg ,name)
                                  (mv start width))))))

                   ,@(extract-vl-types-generate-macros)

                   (define ,debug-fn-name ((value sv::4vec-p)
                                           (excludes (and (acl2::true-list-listp excludes)
                                                          (true-listp excludes)))
                                           (depth-limit integerp))
                     :parents nil
                     :normalize nil
                     ;;:short ,(str::cat "Debug aux function for  @(see |" name "|) VL struct type. Not intended to be called by users.")
                     (declare (ignorable excludes))
                     (cond ((< depth-limit 1)
                            (list :value value
                                  :hex (str::hexify-4vec value)
                                  :limit-reached))
                           (t
                            (flatten
                             (list ;; :value (acl2::loghead ,size value)
                              ,@member-debug-clauses)))))

                   ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                      debug-vector-fn-name
                                                                      pkg-sym)

                   ;;(defsection ,debug-macro-name
                   ;;:short ,(str::cat "Debug macro for  @(see |" name "|) VL struct type.")
                   ;;:long "<p>See @(see vl::extract-vl-types) for explanation of arguments and how to use the debug functionality.</p>"

                   (defmacro ,debug-macro-name (value &key exclude (depth-limit '1000))
                     (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                       (list ',debug-fn-name value (list 'quote excludes) depth-limit)))
                   ;;)

                   (table extracted-vl-types ',symbol
                          '((:type :vl-struct)
                            (:accessor-macro-name ,accessor-macro-name)
                            (:changer-macro-name ,changer-macro-name)
                            (:ranges-fn-name ,ranges-fn-name)
                            (:debug-macro-name ,debug-macro-name)
                            (:debug-fn-name ,debug-fn-name)
                            (:debug-vector-fn-name ,debug-vector-fn-name)
                            ))

                   ))))
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
               (vl-structmemberlist->acl2-types x.members nil orig-def-alist pkg-sym))

              (this-events
               `((defsection ,symbol
                   :autodoc nil
                   :set-as-default-parent t
                   :short ,(str::cat "Accessor, modifier, and debug functions for the extracted " name " VL union type. ")
                   :long ,(str::cat
                           (if (assoc-equal name orig-def-alist) (cdr (assoc-equal name orig-def-alist)) "")
                           "<p>For this type, 3 ACL2 functions/macros are created for users. An accessor: @({(|" name "| value field),})</p> <p>A modifier: @({(change-|"name"| value field-newval-pairs),}) </p> <p>And a debug function to print all the fields: @({(|"name"|-debug value optional-args).})</p><p>These are generated with @(see vl::extract-vl-types). See @(see vl::extract-vl-types) to learn how to use these functions.</p>")

                   (define ,ranges-fn-name ((start natp) (args true-listp))
                     ;;:short ,(str::cat "Calculate the bit locations that a certain field is stored for @(see |" name "|) VL union type. Not intended to be called by users.")
                     :parents nil
                     (b* ((width ,size)
                          ((when (atom args)) (mv start width))
                          (cur-arg (car args))
                          (rest-args (cdr args)))
                       (case cur-arg
                         ,@member-cases
                         (otherwise
                          (progn$ (raise "An invalid field (~p0) is given for vl-struct type ~s1 ~%" cur-arg ,name)
                                  (mv start width))))))

                   ,@(extract-vl-types-generate-macros)

                   (define ,debug-fn-name ((value sv::4vec-p)
                                           (excludes (and (acl2::true-list-listp excludes)
                                                          (true-listp excludes)))
                                           (depth-limit integerp))
                     :parents nil
                     :normalize nil
                     (declare (ignorable excludes))
                     (cond ((< depth-limit 1)
                            (list :value value
                                  :hex (str::hexify-4vec value)
                                  :limit-reached))
                           (t
                            (flatten ;; :value (acl2::loghead ,size value)
                             (list ,@member-debug-clauses)))))

                   ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                      debug-vector-fn-name
                                                                      pkg-sym)

                   ;;(defsection ,debug-macro-name
                   ;;:short ,(str::cat "Debug macro for  @(see |" name "|) VL union type.")
                   ;;:long "<p>See @(see vl::extract-vl-types) for explanation of arguments and how to use the debug functionality.</p>"

                   (defmacro ,debug-macro-name (value &key exclude (depth-limit '1000))
                     (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                       (list ',debug-fn-name value (list 'quote excludes) depth-limit)))
                   ;;)

                   (table extracted-vl-types ',symbol
                          '((:type :vl-union)
                            (:accessor-macro-name ,accessor-macro-name)
                            (:changer-macro-name ,changer-macro-name)
                            (:ranges-fn-name ,ranges-fn-name)
                            (:debug-macro-name ,debug-macro-name)
                            (:debug-fn-name ,debug-fn-name)
                            (:debug-vector-fn-name ,debug-vector-fn-name)
                            ))

                   ))))
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
               `((defsection ,symbol
                   :autodoc nil
                   :set-as-default-parent t
                   :short ,(str::cat "Accessor function for the extracted " name " VL enum type. ")
                   :long ,(str::cat
                           (if (assoc-equal name orig-def-alist) (cdr (assoc-equal name orig-def-alist)) "")
                           "<p>For this type, 2 ACL2 functions/macros are created for users. An accessor: @({(|" name "| value-int-or-string),})</p> <p>And a debug function to print all the fields: @({(|"name"|-debug value).})</p><p>These are generated with @(see vl::extract-vl-types). See @(see vl::extract-vl-types) to learn how to use these functions.</p>"
                           "<p> Definition of the accessor function: </p>@(def |" (symbol-name accessor-macro-name) "|)")

                   (define ,ranges-fn-name ((start natp) (args true-listp))
                     ;;:short ,(str::cat "Calculate the bit locations that a certain field is stored for @(see |" name "|) VL enum type. Not intended to be called by users.")
                     :parents nil
                     (b* ((width ,size)
                          ((when args)
                           (progn$ (raise "Unexpected arguments are passed: ~p0 ~%" args)
                                   (mv start width))))
                       (mv start width)))

                   (define ,accessor-macro-name ((value))
                     ;;:short ,(str::cat "Accessor function for @(see |" name "|) VL enum type. When given an integer, it returns the string equivalent; when given a string, it returns the integer equivalant for this enum type.")
                     :guard (or (sv::4vec-p value)
                                (stringp value))
                     :parents nil
                     (cond ((integerp value)
                            (case value
                              ,@int-to-string-cases
                              (otherwise :invalid-enumitem ;;value
                                         )))
                           ((sv::4vec-p value)
                            value)
                           (t
                            (case-match value
                              ,@string-to-int-cases
                              (& (progn$ (cw "Invalid enum type given: ~s0 ~%" value)
                                         (sv::4vec-x))
                                 ;;value
                                 )))))

                   (define ,debug-fn-name ((value sv::4vec-p)
                                           (excludes)
                                           (depth-limit integerp))
                     (declare (ignorable excludes depth-limit))
                     :parents nil
                     :normalize nil
                     (list :value value
                           :string
                           (,accessor-macro-name value)))

                   ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                      debug-vector-fn-name
                                                                      pkg-sym)

                   (defmacro ,debug-macro-name (value &key (depth-limit '1000))
                     (list ',debug-fn-name value nil depth-limit))


                   (table extracted-vl-types ',symbol
                          '((:type :vl-enum)
                            (:accessor-macro-name ,accessor-macro-name)
                            (:ranges-fn-name ,ranges-fn-name)
                            (:debug-macro-name ,debug-macro-name)
                            (:debug-fn-name ,debug-fn-name)
                            (:debug-vector-fn-name ,debug-vector-fn-name)
                            ))
                   ))))
           (mv this-events size)))

        (:vl-usertype
         (b* (;; Creating a tempororary struct logic so I can use the same code
              ;; in vl-structmember->acl2-types to process :vl-usertype
              (tmp-struct-member (make-vl-structmember :type vl-datatype
                                                       :name name))
              ((mv range-case-statement debug-clause member-events size)
               (vl-structmember->acl2-types tmp-struct-member 0 orig-def-alist pkg-sym t))
              (this-events
               `((,@(if constant-value
                        '(progn)
                      `(defsection ,symbol
                         :autodoc nil
                         :set-as-default-parent t
                         :short ,(str::cat "Accessor, modifier, and debug functions for the extracted " name " VL-usertype (possibly a variable/wire) ")
                         :long ,(str::cat
                                 (if (assoc-equal name orig-def-alist) (cdr (assoc-equal name orig-def-alist)) "")
                                 "<p>For this VL-usertype, 3 ACL2 functions/macros are created for users. An accessor: @({(|" name "| value field),})</p> <p>A modifier: @({(change-|"name"| value field-newval-pairs),}) </p> <p>And a debug function to print all the fields: @({(|"name"|-debug value optional-args).})</p><p>These are generated with @(see vl::extract-vl-types). See @(see vl::extract-vl-types) to learn how to use these functions.</p>")
                         ))
                  (define ,ranges-fn-name ((start natp) (args true-listp))
                    ;;:short ,(str::cat "Calculate the bit locations that a certain field is stored for @(see |" name "|) VL union type. Not intended to be called by users.")
                    :parents nil
                    (b* ((width ,size)
                         ((when (atom args)) (mv start width))
                         (rest-args args))
                      ,(second range-case-statement)))

                  ,@(extract-vl-types-generate-macros :constant-value constant-value)

                  (define ,debug-fn-name ((value sv::4vec-p)
                                          (excludes (and (acl2::true-list-listp excludes)
                                                         (true-listp excludes)))
                                          (depth-limit integerp))
                    :parents nil
                    :normalize nil
                    (declare (ignorable excludes))
                    ,debug-clause)

                  ;; I believe below is not necessary. But I am not sure so
                  ;; leaving it here just in case...
                  ,(extract-vl-types-generate-debug-vector-functions debug-fn-name
                                                                     debug-vector-fn-name
                                                                     pkg-sym)

                  (defmacro ,debug-macro-name (,@(if constant-value nil '(value))
                                               &key exclude (depth-limit '1000)
                                               ,@(and constant-value `((value ',constant-value))))
                    (b* ((excludes (vl-types->acl2-types-parse-args-list exclude ',pkg-sym)))
                      (list ',debug-fn-name value (list 'quote excludes) depth-limit)))

                  (table extracted-vl-types ',symbol
                         '((:type :vl-usertype)
                           (:constant-value ,constant-value)
                           (:accessor-macro-name ,accessor-macro-name)
                           (:changer-macro-name ,changer-macro-name)
                           (:ranges-fn-name ,ranges-fn-name)
                           (:debug-macro-name ,debug-macro-name)
                           (:debug-fn-name ,debug-fn-name)
                           (:debug-vector-fn-name ,debug-vector-fn-name)
                           ))
                  ;;)
                  ))))
           (mv (append member-events
                       this-events)
               size)))

        (otherwise
         (mv (raise "Unexpected vl-datatype: ~p0 ~%" vl-datatype)  0)
         )))))

#|(define vl-typedef->acl2-types (name vl-datatype orig-def-alist pkg-sym)
:mode :program
(b* (((mv events ?size)
(vl-types->acl2-types-new-type name vl-datatype orig-def-alist pkg-sym)))
events))|#

#|

(time$ (with-output
:off :all
(make-event
`(encapsulate
nil
,@(vl-typedef->acl2-types (@ test) nil 's)))
))
|#

;; :i-am-here

(defsection extract-vl-types-create-xdoc-for-types

  (defines vl-datatype->all-children-names

    (define vl-structmemberlist->all-children-names ((member-lst vl-structmemberlist-p))
      :mode :program
      (if (atom member-lst)
          nil
        (b* (((vl-structmember member) (car member-lst))
             (cur-children (vl-datatype->all-children-names member.type))
             ;;(cur-children (cons member.name cur-children))
             )
          (append cur-children
                  (vl-structmemberlist->all-children-names (cdr member-lst))))))

    (define vl-datatype->all-children-names ((x vl-datatype-p))
      (case (vl-datatype-kind x)
        (:vl-coretype nil)
        (:vl-struct
         (b* (((vl-struct x) x)
              (children-names (vl-structmemberlist->all-children-names x.members)))
           (remove-duplicates children-names)))
        (:vl-union
         (b* (((vl-union x) x)
              (children-names (vl-structmemberlist->all-children-names x.members)))
           (remove-duplicates children-names)))
        (:vl-enum
         nil)
        (:vl-usertype
         (b* (((vl-usertype x) x))
           (remove-duplicates (cons x.name
                                    (vl-datatype->all-children-names x.res))))))))

  (define strsubst-vl-vars ((old-val character-listp)
                            (new-val character-listp)
                            (all-string character-listp)
                            &optional
                            (delimeters '(acl2::explode " :][-;()*/+{}'
")))
    :mode :program
    :guard (natp (len old-val))
    :measure (len all-string)
    (if (or (atom all-string)
            (not old-val)
            (not (mbt (natp (len old-val)))))
        nil
      (b* ((i (search old-val all-string))
           ((unless (natp i)) all-string)
           (okp (and (or (eq i 0)
                         (member-equal (nth (1- i) all-string) delimeters))
                     (or (equal (len all-string) (+ i (len old-val)))
                         (member-equal (nth (+ i (len old-val)) all-string) delimeters))))
           ((unless okp)
            (append (take (1+ i) all-string)
                    (strsubst-vl-vars old-val new-val (nthcdr (1+ i) all-string) delimeters))))
        (append (take i all-string)
                new-val
                (strsubst-vl-vars old-val new-val
                                  (nthcdr (+ i (len old-val)) all-string)
                                  delimeters)))))

  (define extract-vl-types-insert-xdoc-links ((doc-string stringp)
                                              (link-strings string-listp))
    :mode :program
    (if (atom link-strings)
        doc-string
      (b* ((doc-string (implode (strsubst-vl-vars
                                 (explode (car link-strings))
                                 (explode (str::cat "@(see |" (car link-strings) "|)"))
                                 (explode doc-string)))))
        (extract-vl-types-insert-xdoc-links doc-string (cdr link-strings)))))

  (define extract-vl-types-create-xdoc-for-types (ss ;; vl-scopestack
                                                  vl-type-names
                                                  all-vl-type-names
                                                  state)
    (declare (ignorable all-vl-type-names))
    :mode :program
    (b* (((when (atom vl-type-names)) (mv nil state))
         ((mv rest state)
          (extract-vl-types-create-xdoc-for-types ss (cdr vl-type-names) all-vl-type-names state))

         (this.name (car vl-type-names))

         (x (vl::vl-scopestack-find-item this.name ss))
         ((unless (or (vl-typedef-p x)
                      (vl-vardecl-p x)
                      (vl-paramdecl-p x)))
          (mv rest state))

         ;; Get original Verilog definition:
         ((mv minloc maxloc)
          (cond ((vl-typedef-p x)
                 (mv (vl-typedef->minloc x) (vl-typedef->maxloc x)))
                ((vl-vardecl-p x)
                 (b* (((vl-location loc) (vl-vardecl->loc x)))
                   ;; making the column 0 because the start location can eat away the declaration type.
                   (mv (change-vl-location loc :col 0) nil)))
                ((vl-paramdecl-p x)
                 (b* (((vl-location loc) (vl-paramdecl->loc x)))
                   ;; making the column 0 because the start location can eat away the declaration type.
                   (mv (change-vl-location loc :col 0) nil)))
                (t (mv (raise "Unexpected vl-type for x: ~p0" x) nil))))


         ((mv okp result & state) (vl-read-file (vl-location->filename minloc)))
         ((unless okp)
          (progn$ (cw "Couldn't read file ~p0 for ~p1 ~%"
                      (vl-location->filename minloc) this.name)
                  (mv rest state)))
         (string
          (cond (maxloc
                 (vl-string-between-locs (vl-echarlist->string result)
                                         minloc
                                         maxloc))
                (t
                 ;; when maxloc is unknown, find the first instance of
                 ;; ";" to figure out when the declaration ends.
                 (b* ((string (vl-echarlist->string result))
                      (start (vl-string-findloc string minloc))
                      (end (search ";" string :start2 start))
                      (end (or end
                               ;; if ";" is not found, then at least return one line:
                               (vl-string-findloc
                                string
                                (make-vl-location :line (1+ (vl-location->line minloc))
                                                  :col 0)))))
                   (subseq string start (min (length string) end))))))



         ;; insert xdoc hyperlinks to quickly navigate children types.
         (string (extract-vl-types-insert-xdoc-links string all-vl-type-names))
         (string (str::strsubst ">" "@('>')" string))
         (string (str::strsubst "<" "@('<')" string))

         (string (str::cat "<p>Original Verilog Definition: <code>" string "</code></p>"))
         (string
          (str::cat
           string
           "<p> Source <a href=\"file://" (vl-location->filename  minloc) "\">file</a>:"
           (vl-location->filename minloc) "<br />"
           "Lines: " (str::int-to-dec-string (vl-location->line minloc))
           "-" (if maxloc (str::int-to-dec-string (vl-location->line maxloc)) "?")
           ".</p>"))

         )
      (mv `((,(car vl-type-names) . ,string) ,@rest)
          state))))

#!VL
(define extract-vl-paramdecl ((paramdecl vl-paramdecl-p) orig-def-alist pkg-sym)
  :mode :program

  (b* (((vl-paramdecl x) paramdecl)
       (events
        (case (vl-paramtype-kind x.type)
          (:vl-explicitvalueparam
           (b* (((vl-explicitvalueparam x) x.type)
                (constant-value-name (intern-in-package-of-symbol (str::cat "*"x.name"*") pkg-sym))

                ((mv extra-events &)
                 (if (member-equal
                      (vl-datatype-kind x.type)
                      '(:vl-usertype :vl-coretype))
                     (vl-types->acl2-types-new-type x.name x.type
                                                    orig-def-alist pkg-sym
                                                    :constant-value constant-value-name)
                   (mv nil nil))))
             `((defsection ,(intern-in-package-of-symbol x.name pkg-sym)
                 :short ,(str::cat "An extracted VL type parameter with a constant value of "
                                   (cond ((integerp x.final-value)
                                          (str::int-to-dec-string x.final-value))
                                         ((sv::4vec-p x.final-value)
                                          (str::cat "'("
                                                    (str::int-to-dec-string (sv::4vec->upper x.final-value))
                                                    " . "
                                                    (str::int-to-dec-string (sv::4vec->lower x.final-value))
                                                    ")"))
                                         (t "??")))
                 :long ,(str::cat
                         (if (assoc-equal x.name orig-def-alist) (cdr (assoc-equal x.name orig-def-alist)) "")
                         "@(def *|"x.name"|*)"
                         (if extra-events
                             (str::cat "<p>Since this constant value is a special user type, 3 ACL2 functions/macros are created for users: an accessor, a modifier and a debugger.</p><p> An accessor: @({(|" x.name "| optional-field),})</p> <p>A modifier: @({(change-|"x.name"| field-newval-pairs),}) </p> <p>And a debug function to print all the fields: @({(|"x.name"|-debug optional-args).})</p><p>These are generated with @(see vl::extract-vl-types). See @(see vl::extract-vl-types) to learn how to use these functions. Note that since this type is a constant, these functions/macros do not explicitly take the \"value\". Instead, it uses the value of <tt>*|"x.name"|*</tt> by default. Passing an extra key argument \":value\" to any one of these macros/functions can override the value used.</p>")
                           ""))
                 :autodoc nil
                 :set-as-default-parent t
                 (defconst ,constant-value-name
                   ,x.final-value))
               ,@extra-events)))
          (& (raise "Unsupported vl-paramtype-kind: ~p0 for ~p1" x.type x.name)))))
    events))

(define extract-vl-types-fn (design
                             (module acl2::maybe-stringp)
                             (package acl2::maybe-stringp)
                             names-to-extract
                             all-names-to-extract
                             pkg-sym
                             &optional
                             (ss 'nil)
                             (state 'state))
  :mode :program
  (if (atom names-to-extract)
      (mv nil state)
    (b* ((ss (or ss
                 (cond (module
                        (b* ((ss (vl::vl-scopestack-init design))
                             (mod (vl::vl-scopestack-find-definition module ss))
                             (mod-ss (vl::vl-scopestack-push mod ss)))
                          mod-ss))
                       (package
                        (b* ((ss (vl::vl-scopestack-init design))
                             (pkg (vl::vl-scopestack-find-package package ss))
                             (pkg-ss (vl::vl-scopestack-push pkg ss)))
                          pkg-ss))
                       (t (vl::vl-scopestack-init design)))))

         (cur-name (car names-to-extract))
         (cur (vl::vl-scopestack-find-item cur-name ss))

         ((mv name type)
          (cond ((vl-typedef-p cur)
                 (mv (vl-typedef->name cur) (vl-typedef->type cur)))
                ((vl-vardecl-p cur)
                 (mv (vl-vardecl->name cur) (vl-vardecl->type cur)))
                ((vl-paramdecl-p cur)
                 (mv cur-name (and (equal (vl-paramtype-kind (vl-paramdecl->type cur)) :vl-explicitvalueparam)
                                   (vl-explicitvalueparam->type (vl-paramdecl->type cur)))))
                (t (mv "" nil))))
         ;;----
         ;; create doc strings for each data type that comes along:
         (?all-included-type-names (append (list name)
                                           (and type (vl-datatype->all-children-names type))
                                           all-names-to-extract))
         (all-included-type-names (remove-duplicates all-included-type-names))
         ((mv orig-def-alist state)
          (extract-vl-types-create-xdoc-for-types ss all-included-type-names all-included-type-names state))
         ;;---

         ((mv events state)
          (cond ((or (vl-typedef-p cur)
                     (vl-vardecl-p cur))
                 (b* (((mv events ?size)
                       (vl-types->acl2-types-new-type name type orig-def-alist pkg-sym)))
                   (mv events state)))
                ((vl-paramdecl-p cur)
                 (b* ((events (extract-vl-paramdecl cur orig-def-alist pkg-sym)))
                   (mv events state)))
                (t
                 (mv (if cur
                         (raise "Given name was found in the scopestack but it wasn't a known type: ~p0" cur)
                       (raise "Given name was not found in the scopestack: ~p0" cur-name))
                     state))))

         ((mv rest state) (extract-vl-types-fn design module package (cdr names-to-extract) all-names-to-extract pkg-sym ss)))
      (mv (append events rest) state))))

#!VL
(defconst *extract-vl-types-theory*
  '(vl::vl-coretype-collected-dims-p
    (:type-prescription vl::when-vl-coretype-collected-dims-p-is-consp)
    (:rewrite acl2::o<-of-nat-list-measure)
    (:type-prescription vl::vl-coretype-collected-dims-p)
    (:rewrite acl2::nfix-when-natp)
    (:type-prescription len)
    (:rewrite acl2::append-when-not-consp)
    (:rewrite acl2::natp-when-integerp)
    (:rewrite acl2::natp-when-gte-0)
    (:definition string-append-lst)
    (:type-prescription acl2::true-listp-of-flatten)
    (:definition string-append)
    ;;(:rewrite acl2::consp-under-iff-when-true-listp)
    (:type-prescription nfix)
    (:definition str::fast-string-append-lst)
    (:type-prescription acl2::true-list-listp)
    (:definition not)
    (:type-prescription vl::collect-and-cdr-lists-that-start-with)
    (:type-prescription natp)
    (:type-prescription o<)
    (:type-prescription acl2::true-listp-append)
    (:type-prescription binary-append)
    (:rewrite TRUE-LIST-LISTP-of-PAIRLIS$)

    ;;(:rewrite  vl::string-listp-when-no-nils-in-vl-maybe-string-listp)

    ;;(:rewrite acl2::cdr-nthcdr)
    (:type-prescription str::true-listp-of-explode)
    ;;(:rewrite commutativity-of-+)
    (:type-prescription zp)
    (:type-prescription o-p)
    ;;(:rewrite str::explode-of-implode)
    ;;(:type-prescription subsetp-equal)

    ;;(:rewrite acl2::member-of-cons)
    ;;(:rewrite acl2::commutativity-2-of-+)
    (:type-prescription str::hexify-4vec)
    ;;(:rewrite acl2::open-small-nthcdr)
    (:forward-chaining vl::when-vl-coretype-collected-dims-p-is-consp)
    (:type-prescription acl2::true-listp-nthcdr-type-prescription)
    (:type-prescription str::stringp-of-nat-to-dec-string)

    ;;(:rewrite vl::vl-maybe-string-list-p-of-cons)
    (:definition return-last)
    ;;(:rewrite acl2::subsetp-refl)
    ;;(:rewrite str::make-character-list-is-identity-under-charlisteqv)
    (:rewrite acl2::append-of-cons)
    ;;(:rewrite flag::flag-equiv-lemma)
    (:rewrite vl::true-list-listp-of-collect-and-cdr-lists-that-start-with)
    (:rewrite associativity-of-+)
    (:type-prescription str::binify)
    ;;(:type-prescription vl::vl-maybe-string-list-p)
    (:type-prescription acl2::stringp-of-implode)
    (:rewrite unicity-of-0)
    (:rewrite  vl::natp-of-start-of-get-extracted-vl-type-array-ranges)

    (:compound-recognizer acl2::natp-compound-recognizer)
    (:compound-recognizer acl2::zp-compound-recognizer)
    (:rewrite acl2::o-p-of-nat-list-measure)
    (:definition atom)
    (:executable-counterpart <)
    (:executable-counterpart binary-+)
    (:executable-counterpart len)
    (:executable-counterpart not)
    (:rewrite car-cons)
    (:rewrite acl2::len-of-cons)
    (:definition synp)
    (:executable-counterpart consp)
    (:executable-counterpart equal)
    (:executable-counterpart nfix)
    (:rewrite cdr-cons)
    (:rewrite acl2::lower-bound-of-len-when-sublistp)
    (:rewrite vl::prefixp-of-self)
    (:rewrite acl2::sublistp-when-prefixp)
    (:elim car-cdr-elim)
    (:type-prescription len)
    ;;(:type-prescription bitops::part-select-width-low$inline)
    (:definition string-listp)
    (:e eqlablep)
    ;;(:rewrite sv::fix-of-number)
    (:executable-counterpart equal)
    (:definition eql)

    (:rewrite SV::4VEC-P-OF-4VEC-PART-SELECT)
    (:rewrite 4VEC-P-WHEN-INTEGERP)))

#!VL
(defmacro extract-vl-types (&rest args)
  (b* ((parents     (cdr (extract-keyword-from-args :parents args)))
       (design      (cdr (extract-keyword-from-args :design args)))
       (module      (cdr (extract-keyword-from-args :module args)))
       (package     (cdr (extract-keyword-from-args :package args)))
       (pkg-sym     (cdr (extract-keyword-from-args :pkg-sym args)))
       (names-to-extract (throw-away-keyword-parts args)))

    `(encapsulate nil
       (local (include-book "std/lists/len" :dir :system))
       (with-output
         :off :all
         :on (comment error)
         (make-event
          (b* (((mv events state)
                (extract-vl-types-fn ,design ,module ,package ',names-to-extract ',names-to-extract
                                     ;; to  prevent  conflicts when  the  same
                                     ;; type  is  extracted  across  different
                                     ;; books with different design constants:
                                     (or ',pkg-sym (pkg-witness (symbol-package-name ',design)))
                                     ;;(intern-in-package-of-symbol "PKG-SYM" ',design)
                                     )))
            (value
             `(progn
                ,@(and ',parents
                       '((local
                          (xdoc::set-default-parents ,@parents))))

                (local
                 (in-theory *extract-vl-types-theory* ))

                ,@events)
             )))))))

;;(include-book "xdoc/debug" :dir :system)

(defxdoc extract-vl-types
  :parents (mlib)
  :short "Extract Verilog data types to access them with ACL2 functions"
  :long "<p>Signature:</p>

@({
(extract-vl-types  :design design-name
                   [:module module-name-to-add-to-scope] ;; optional
                   [:parents parents-for-generated-docs] ;; optional
                   ... vl-types: list of datatype/constant/wire names ...)
})
<p>Example call:</p>
@({
(vl::extract-vl-types  :design *my-good-simplified-svex-design*
                       :module \"my_module_name\"
                       :parents (my-extracted-vl-types)
                       \"my_data_struct\" \"my_data_struct2\")
})

<p> The above call will generate an event that submits ACL2 accessor, modifier, and debug functions for \"my_data_struct\", \"my_data_struct2\", and their children if there are any. </p>

<ul>
<li> \"design\" should be the \"good\" output from @(see vl::vl-design->sv-design) stage.</li>
<li> \"module\" can be nil or a Verilog module name. When nil, the program only searches for globally defined data structures. When non-nil, it searches in the scope of that given module name. </li>
<li> \"vl-types\" can be a number of Verilog data structures, constants, or wires. The program will generate accessor functions for these data structures as well as their children. These data types can be \"struct\", \"enum\", \"union\", or packed/unpacked vectors. For constants, a defconst event will be submitted. Users may find it useful to pass some wire names in cases they are declared as a vector in the given module.
</li>

</ul>

<h3>Accessors</h3>

<p> Using the generated functions, users can access a part of a given data structure. For example, if we have a large struct with a lot of fields, say named \"t_main\", then the program will generate a macro with the same name: |t_main| (reminder: Verilog is case-sensitive and so are our symbol/function names). Say that we have a variable called \"main\" in our conjectures representing a signal of type \"t_main\" (assuming we use @(see acl2::defsvtv)). Then, we can access individual fields of this signal using the generated |t_main| macro. For example:</p>
@({
(|t_main| main \"data[0].dword[3]\")
(|t_main| main \"uop.size\")
})

<p> In case of enumarated types, their generator functions can take a string or an integer, and return corresponding integer or string values, respectively.
</p>

<h3> Modifiers </h3>

<p> vl::extract-vl-types will also generate \"change\" macros for every type. For example:</p>
@({(change-|t_main| main \"data[0].dword[3]\" 12)})
<p> will set the \"data[0].dword[3]\" field of main to 12.</p>

<p> More arguments can be passed to change other entries in the same call:</p>
@({(change-|t_main| main \"data[0].dword[3]\" 12 \"uop.size\" 0)})

<p> If a field is repeated in the arguments or a field is passed that has an
overlap with a previos argument, then the most recent one will override the previous one(s). </p>

<h3> Debug Functions </h3>

<p> The program will also created \"debug\" macros/functions for every type. For example: </p>
@({(|t_main|-debug main)})
<p> will return a large term that has all the entries for a given concrete value \"main\". Arguments to these debug functions are:</p>
<ul>
<li> A list of fields to exclude from printing. For example:
@({
(|t_main|-debug main :exclude (\"uop.size\"
                               \"data[0]\"
                               \"data[1].dword\"
                               \"data[2].*\"))
})
When there is a \".*\" at the end of a skipped argument (e.g., \"data[2].*\"), then the value of that argument (e.g., \"data[2]\") will be included but not its fields. Without the \".*\", then nothing about that field (e.g., \"data[0]\") will be included.  </li>

<li> A depth limit (natural number). When set to a large number, the debug functions will dive into the children and call the debug functions of all the subfields. Users can set this to a small natural number to limit the depth of the function calls. In that case, the debug functions dive upto the specified level only.
@({
(|t_main|-debug main :exclude (\"uop.size\"
                               \"data[2].*\")
                     :depth-limit 2)
})
</li>

</ul>

<h3>Minimal Non-local Book Inclusion</h3>

<p>The extract-vl-types event requires a significant part of the VL library to be loaded, but the generated macros only require a few utilities.  Those requirements are included in the book \"centaur/vl/mlib/extract-vl-types-support\".  Therefore, you can do the following in a book if you want to minimize what that book nonlocally includes:</p>

@({
 (include-book \"centaur/vl/mlib/extract-vl-types-support\" :dir :system)
 (local (include-book \"centaur/vl/mlib/extract-vl-types\" :dir :system))

 (vl::extract-vl-types ...)
 })

<p>Similarly, vl-extract-types can be used locally to an encapsulate as
follows (note the use of make-event to wrap the macro call of
extract-vl-types:</p>

@({
 (include-book \"centaur/vl/mlib/extract-vl-types-support\" :dir :system)
 (encapsulate nil
   (local (include-book \"centaur/vl/mlib/extract-vl-types\" :dir :system))
   (make-event '(vl::extract-vl-types ...)))
 })

"

  )
