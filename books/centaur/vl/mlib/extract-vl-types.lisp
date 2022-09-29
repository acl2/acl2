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

(progn
  (local
   (defthm natp-of-expt
     (implies (and (natp x) (natp y))
              (<= 0 (expt x y)))))
  (local
   (defthm natp-of-*
     (implies (and (natp x) (natp y))
              (<= 0 (* x y)))))
  (local
   (defthm natp-of-+
     (implies (and (natp x) (natp y))
              (<= 0 (+ x y)))))
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

  (define extracted-vl-type-array-accessor ((value integerp)
                                (dims vl-coretype-collected-dims-p)
                                (args)
                                &optional
                                (vec-name "")
                                (allow-redundant-args 'nil)
                                )

    :returns (res integerp)

    (cond ((and (atom dims)
                (consp args))
           (progn$
            (or allow-redundant-args
                (raise "Too many arguments are passed to access a vl-coretype (~s0)~%" vec-name))
            (ifix value)))
          ((atom dims)
           (ifix value))
          ((and (atom args)
                (not (natp args)))
           (b* (((unless (equal args nil))
                 (progn$ (raise "Args should be a true-listp of natural numbers or a natural number but given ~p0 instead (~s0)~%" args vec-name)
                         0))
                ;;((list* slice-size msb lsb) (car dims))
                ;;(size (* slice-size (+ msb 1 (- lsb))))
                )
             ;;(acl2::loghead size value)
             (ifix value)
             ))
          (t (b* ((cur-arg (if (natp args) args (car args)))
                  ((unless (natp cur-arg))
                   (progn$ (raise "A a non-natp value is given for an index argument: ~p0 (~s1) ~%"
                                  cur-arg vec-name)
                           0))
                  ((list* slice-size msb lsb) (car dims))
                  ((unless (and (<= cur-arg msb)
                                (>= cur-arg lsb)))
                   (progn$ (raise "Given argument '~p0' is out of bounds for the given vector (~s1). MSB (upperbound) is ~p2 and LSB (lowerbound) is ~p3 ~%"
                                  cur-arg vec-name msb lsb)
                           0))
                  (index (- cur-arg lsb))

                  (value ;;(if (equal slice-size 0)
                   ;;  (acl2::part-select value :low index :width 1)
                   (acl2::part-select value
                                      :low (* slice-size index)
                                      :width slice-size))
                  ((when (natp args)) value))
               (extracted-vl-type-array-accessor value
                                                 (cdr dims)
                                                 (cdr args)
                                                 vec-name
                                                 allow-redundant-args)))))

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
(define vl-enumitemlist->acl2-types-cases ((lst vl-enumitemlist-p)
                                           &optional
                                           ((cnt natp) '0))
  (if (atom lst)
      nil
    (b* ((rest (vl-enumitemlist->acl2-types-cases (cdr lst) (1+ cnt)))
         ((vl-enumitem cur) (car lst))
         ((unless (equal cur.range nil))
          (raise "Unexpected enumitem (~p0). Check for (equal cur.range nil) has failed.~%" cur))
         (cur.value (if cur.value
                        (b* (((unless (equal (vl-expr-kind cur.value) :vl-literal))
                              (raise "(equal (vl-expr-kind cur.value) :vl-literal) failed for cur=~p0~%" cur))
                             (val (vl-literal->val cur.value))
                             ((unless (equal (vl-value-kind val) :vl-constint))
                              (raise "(equal (vl-value-kind val) :vl-constint) failed for val=~p0~%" val))
                             (val (vl-constint->value val)))
                          val
                          )
                      cnt))
         (case-statement
          `(,cur.value ,cur.name)))
      (cons case-statement rest))))

#!VL
(define vl-enum-values->acl2-types-cases ((values vl-exprlist-p)
                                          (items vl-enumitemlist-p))
  (if (or (atom values)
          (atom items))
      (if (equal values items) nil
        (raise "Expected items and values to be of the same length~%"))
    (b* ((rest (vl-enum-values->acl2-types-cases (cdr values) (cdr items)))
         ((unless (equal (vl-expr-kind (car values)) :vl-literal))
          (raise "(equal (vl-expr-kind (car values)) :vl-literal) failed for values=~p0~%" values))
         ((vl-literal x) (car values))

         ((unless (equal (vl-value-kind x.val) :vl-constint))
          (raise "(equal (vl-value-kind x.val) :vl-constint) failed for x=~p0~%" x))

         ((unless (equal (vl-value-kind x.val) :vl-constint))
          (raise "(equal (vl-value-kind x.val) :vl-constint) failed for x=~p0~%" x))
         (value (vl-constint->value x.val))
         ((vl-enumitem cur) (car items))
         ((unless (equal cur.range nil))
          (raise "Unexpected enumitem (~p0). Check for (equal cur.range nil) has failed.~%" cur))

         (case-statement
          `(,value ,cur.name)))
      (cons case-statement rest))))

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

#!VL
(defines vl-types->acl2-types

  (define vl-structmemberlist->acl2-types (members structp pkg-sym)
    :guard (and (vl-structmemberlist-p members)
                )
    :mode :program
    :returns (mv member-cases
                 member-events
                 (total-size natp))
    (if (atom members)
        (mv nil nil 0)
      (b* (((mv rest-cases rest-events rest-size)
            (vl-structmemberlist->acl2-types (cdr members) structp  pkg-sym))

           ((mv this-case this-events this-size)
            (vl-structmember->acl2-types (car members)
                                         (and structp rest-size)
                                         pkg-sym)))
        (mv (cons this-case rest-cases)
            (append this-events rest-events)
            (if structp
                (+ this-size rest-size)
              (max this-size rest-size))))))

  (define vl-structmember->acl2-types (member offset pkg-sym)
    :guard (vl-structmember-p member)
    :returns (mv case-statement events size)
    ;; when creating assignemnts, we assume there is a rest-args, which is a true-listp
    (b* (((vl-structmember member) member))
      (case (vl-datatype-kind member.type)
        (:VL-CORETYPE
         (b* (((mv collected-dims size) (vl-coretype-collect-dims member.type))
              (case-statement
               `(,(INTERN-IN-PACKAGE-OF-SYMBOL member.name pkg-sym)
                 (b* (,@(and offset 
                             `((value (acl2::part-select value :low ,offset :width ,size))))
                      (dims ',collected-dims))
                   (extracted-vl-type-array-accessor value dims rest-args ,member.name nil))))
              (events nil))
           (mv case-statement events size)))

        (::VL-USERTYPE
         (b* (((vl-usertype x) member.type)
              ((mv events size)
               (vl-types->acl2-types-new-type x.name x.res pkg-sym))
              ((mv dims2 acc-size) (vl-coretype-collect-dims-aux x.pdims size))
              ((mv dims1 acc-size) (vl-coretype-collect-dims-aux x.udims acc-size))
              (collected-dims (append dims1 dims2))
              (fn-name (intern-in-package-of-symbol (str::cat x.name "-FN") pkg-sym))
              (case-statement
               `(,(intern-in-package-of-symbol member.name pkg-sym)
                 ,(if collected-dims
                      `(b* (,@(and offset 
                                   `((value (acl2::part-select value :low ,offset :width ,acc-size))))
                            (value (extracted-vl-type-array-accessor value
                                                         ',collected-dims
                                                         rest-args
                                                         ,member.name t))
                            (rest-args (nthcdr ,(len collected-dims) rest-args))
                            (value (if (equal rest-args nil)
                                       value
                                     (,fn-name value rest-args))))
                         value)
                    `(,fn-name ,(if offset
                                    `(acl2::part-select value :low ,offset :width ,acc-size)
                                  'value)
                               rest-args)))))
           (mv case-statement events acc-size)))
        (otherwise
         (progn$ (raise "Unexpected vl-structmember type: ~p0 ~%" member)
                 (mv nil nil 0))))))

  (define vl-types->acl2-types-new-type (name vl-datatype (pkg-sym symbolp))
    :returns (mv (events)
                 (size natp))
    (b* (((unless (stringp name))
          (mv (raise "(stringp name) is failed for: ~p0 ~%" name) 0))
         ((unless (vl-datatype-p vl-datatype))
          (mv (raise "(stringp name) is failed for: ~p0 ~%" name) 0)))
      (case (vl-datatype-kind vl-datatype)
        (:vl-coretype
         (b* (((mv collected-dims size) (vl-coretype-collect-dims vl-datatype))
              (fn-name (INTERN-IN-PACKAGE-OF-SYMBOL (str::cat name "-FN") pkg-sym))
              (macro-name (INTERN-IN-PACKAGE-OF-SYMBOL name pkg-sym))
              ;; accessor function expects indices only in a list such as '(1 2 3)
              (events
               `((define ,fn-name
                   ((value integerp) (args true-listp))
                   (b* ((value (acl2::loghead ,size value))
                        ((when (atom args)) (ifix value))
                        (dims ',collected-dims))
                     (extracted-vl-type-array-accessor value dims args
                                           ,name nil)))
                 (defmacro ,macro-name (value &optional (args '""))
                   (list ',fn-name value
                         (list 'quote
                               (vl-types->acl2-types-parse-args
                                args ',pkg-sym)))))))
           (mv events size)))
        (:vl-struct
         (b* (((vl-struct x) vl-datatype)
              ((unless (equal x.pdims nil))
               (mv (raise "(equal x.pdims nil) failed for: " x) 0))
              ((unless (equal x.udims nil))
               (mv (raise "(equal x.udims nil) failed for: " x) 0))
              ((mv member-cases member-events size)
               (vl-structmemberlist->acl2-types x.members t pkg-sym))
              (fn-name (INTERN-IN-PACKAGE-OF-SYMBOL (str::cat name "-FN") pkg-sym))
              (macro-name (INTERN-IN-PACKAGE-OF-SYMBOL name pkg-sym))
              (this-events
               `((define ,fn-name
                   ((value integerp) (args true-listp))
                   (b* ((value (acl2::loghead ,size value))
                        ((when (atom args))
                         (ifix value)
                         ;;(acl2::loghead ,size value)
                         )
                        
                        (cur-arg (car args))
                        (rest-args (cdr args)))
                     (case cur-arg
                       ,@member-cases
                       (otherwise
                        (raise "An invalid field (~p0) is given for vl-struct type ~s1 ~%" cur-arg ,name)))))
                 (defmacro ,macro-name (value &optional (args '""))
                   (list ',fn-name value
                         (list 'quote
                               (vl-types->acl2-types-parse-args
                                args ',pkg-sym)))))))
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
              ((mv member-cases member-events size)
               (vl-structmemberlist->acl2-types x.members nil pkg-sym))
              (fn-name (intern-in-package-of-symbol (str::cat name "-FN") pkg-sym))
              (macro-name (intern-in-package-of-symbol name pkg-sym))
              (this-events
               `((define ,fn-name
                   ((value integerp) (args true-listp))
                   (b* ((value (acl2::loghead ,size value))
                        ((when (atom args))
                         (ifix value)
                         ;;value
                         )
                        
                        (cur-arg (car args))
                        (rest-args (cdr args)))
                     (case cur-arg
                       ,@member-cases
                       (otherwise
                        (raise "An invalid field (~p0) is given for vl-struct type ~s1 ~%" cur-arg ,name)))))
                 (defmacro ,macro-name (value &optional (args '""))
                   (list ',fn-name value
                         (list 'quote
                               (vl-types->acl2-types-parse-args
                                args ',pkg-sym)))))))
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
              (cases (vl-enum-values->acl2-types-cases x.values x.items))
              ;;(cases (vl-enumitemlist->acl2-types-cases x.items))
              (fn-name (INTERN-IN-PACKAGE-OF-SYMBOL (str::cat name "-FN") pkg-sym))
              (macro-name (INTERN-IN-PACKAGE-OF-SYMBOL name pkg-sym))
              (this-events
               `((define ,fn-name
                   ((value integerp) &optional (args true-listp))
                   (declare (ignorable args))

                   (b* ((value (acl2::loghead ,size value))
                        ((when (not args))
                         value)
                        (- (or (and (not (cdr args))
                                    (symbolp (car args))
                                    (or (equal (symbol-name (car args)) "str")
                                        (equal (symbol-name (car args)) "string")))
                               (cw "An extra argument of ~p0 is passed to an accessor for an enum type (~s1). In case of such redundant arguments, we return the string equivalent of that enum type. To suppress this warning, set that extra argument to \"str\" or \"string\" instead of ~p0~%" args ,name))))
                     (case value
                       ,@cases
                       (otherwise :invalid-enumitem ;;value
                                  ))))
                 (defmacro ,macro-name (value &optional (args '""))
                   (list ',fn-name value
                         (list 'quote
                               (vl-types->acl2-types-parse-args
                                args ',pkg-sym)))))))
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

;; (make-event
;;  `(progn . ,(vl-typedef->acl2-types (@ test-type) 's)))

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
    (cons 'progn (extract-vl-types-fn ,design ,module ',vl-types ',design))))


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

<p> In case of enumarated types, if you pass an extra argument of \"str\" or \"string\", then the generated functions will return the string equivalant of the given value. For example, if the \"uop.size\" field is an enum type, then (|t_main| main \"uop.size\") will return an integer whereas (|t_main| main \"uop.size.str\") will return the string equivalent of that integer, e.g., \"ZMM\".
</p> 

"
  
  
  )

