; Copyright (C) Intel Corporation
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

; A tool to generate an SVA from ACL2 proof assumptions about SVTVs.

#||

Generating SVAs from ACL2 theorems
==================================

Generate a SystemVerilog sequence, where each entry in the sequence
 corresponds to an SVTV stage.  Each entry in the sequence will contain an
 expression that needs to be true at that point in time, as well a list of
 local variable assignments for signals at that stage. We will use these
 variables in the conclusion.

The ACL2 theorem to be converted to an SVA will be of the form

(implies LHS RHS)

LHS should be a conjunction of equalities, such as

(and (equal opcode <opcode>) (equal other_signal 1))

RHS should be an ACL2 term that manipulates SVTV variables.

Implementation:

1. Parse ACL2 thm for SVTV vars used in the LHS and RHS. All of the RHS SVTV
vars will need to be local variables in the SVA, which we will instantiate in
the appropriate stage in the SVA sequence.

2. Build SVA LHS by iterating over SVTV stimulus pattern. For each stage, for
each var in pipeline, check if corresponding var is in LHS and/or RHS.

3. Build SVA RHS by converting supported ACL2 function calls to verilog functions
calls.

||#

(in-package "SV")

(include-book "intel/svtv-to-sva/top" :dir :system)

(include-book "assume-to-sva-preprocess")

(define chars+-to-verilog ((x character-listp))
; Should functions in svtv-to-sva-types be changed to these?
  :returns (r character-listp :hyp :guard)
  (if (endp x)
      ()
    (b* ((c (first x))
         (cs (if (equal c #\+)
                 (coerce "_plus_" 'list)
               (list (char-to-verilog (first x))))))
      (append cs
              (chars+-to-verilog (rest x))))))

(define symb+-to-verilog ((x symbolp))
  "Convert an ACL2 symbol (may include +) to verilog"
  :returns (r stringp)
  (coerce (chars+-to-verilog (coerce (symbol-name x) 'list)) 'string))

(define part-select->verilog-inds ((x part-select-p))
  :guard-hints (("Goal" :in-theory (enable part-select-p)))
  "Convert only part-select indices to a verilog string"
  ; This function is used in the LHS of the SVA. Can we use the abbreviated +:
  ; for up_vect and down_vect, if we don't know which one the signal is?
  (b* ((args  (cdr x))
       (lsb   (unquote (first args)))
       (width (unquote (second args)))
       (msb   (+ lsb (1- width)))
       (lsb-s (str::int-to-dec-string lsb))
       (msb-s (str::int-to-dec-string msb)))
    (str::cat "[" msb-s ":" lsb-s "]")))

(fty::defprod svavar
 :short "Store information about variables in an assume term"
 ((name   symbolp)
  ;; part-select
  (ps     stringp :default "")
  (val    sv::maybe-4vec-p))
 :long  "<p>This structure holds information gathered while parsing a
 user-provided assumption term</p>"
 )

(fty::deflist svavar-list
              :elt-type svavar
              :short "A list of svavar-p"
              :true-listp t)

(defines
  assume-lhs-p
  :short "Recognizer for the theorem LHS to be converted to verilog"
  ;; The LHS can only consist of AND and EQUALITY terms. When macroexpanded,
  ;; (AND A B) = (IF A B 'NIL)
  (define assume-lhs-p (lhs)
    (b* (((unless (consp lhs))
          (raise "LHS expected to be a conjunction of equalities: ~x0" lhs))
         (fn (car lhs))
         (args (cdr lhs)))
      (cond
       ((quotep lhs)
        ;; no constraint
        (equal lhs (kwote t)))
       ((eq fn 'if)
        (b* (((unless (conspn args 3))
              (raise "~x0 expects three arguments" fn))
             (arg1 (first args))
             (arg2 (second args))
             (arg3 (third args))
             ((unless (equal arg3 (kwote nil)))
              (raise "LHS can only contain conjunction and equality terms:
                         ~x0. The final argument should be nil."
                     lhs)))
          (and (assume-lhs-p arg1) (assume-lhs-p arg2))))
       ((assoc fn *acl2-equal-fns-to-vl*)
         (b* (((unless (conspn args 2))
               (raise "~x0 expects two arguments" fn))
              (var (first args))
              (val (second args)))
           (and (or (symbolp var)
                    (part-select-p var))
                (conspn val 2)
                (quotep val)
                (sv::4vec-p (unquote val)))))
        (t (raise "LHS contains an unsupported function: ~x0" fn)))))

  (define assume-lhs-list-p (lhs)
    (if (atom lhs)
        (null lhs)
      (and (assume-lhs-p (car lhs))
           (assume-lhs-list-p (cdr lhs)))))
  ///

  (defthm cdr-assume-lhs-list-p
    (implies (assume-lhs-list-p x)
             (assume-lhs-list-p (cdr x)))))

(defines
  assume->svavar-lst
  :verify-guards nil
  (define assume->svavar-lst (x (lhs? booleanp) (lst svavar-list-p))
    :short "Extract the SVTV variable references in the LHS or RHS of an
    assumption theorem"
    :guard (if lhs? (assume-lhs-p x) t)
    ;; :verify-guards :after-returns ;; doesn't work
    :returns (r svavar-list-p :hyp (and (booleanp lhs?) (svavar-list-p lst)))

    (cond
     ((atom x)
      (cond ((symbolp x)    (cons (make-svavar :name x) lst))
            (t (raise "Unexpected atom: ~x0" x))))
     ((quotep x) lst)
     (t
      (b* ((fn (car x))
           (args (cdr x))
           ((when (hons-get fn *acl2-fn-to-vl*))
            (cond
             ;; LHS
             ((and lhs? (assoc fn *acl2-equal-fns-to-vl*))
              (b* ((var (first args))
                   (val (unquote (second args)))
                   ;; symbolp or part-select-p
                   ((when (symbolp var))
                    (cons (make-svavar :name var :val val) lst))
                   ;; clear this proof obligation
                   ((unless (part-select-p var))
                    (raise "expected a part-select: ~x0" x)))
                (cons (make-svavar
                       :name (fourth var)
                       :ps   (part-select->verilog-inds var)
                       :val val)
                      lst)
                ))

             ((and lhs? (eq fn 'if))
              (assume->svavar-lst (second args) lhs?
                                  (assume->svavar-lst (first args) lhs? lst)))
             ;; RHS
             (t (assume-lst->svavar-lst args lhs? lst)))))
        (raise "unrecognized function~%~x0 in ~%~x1" fn x)))))

  (define assume-lst->svavar-lst (xs (lhs? booleanp) (lst svavar-list-p))
    :guard (if lhs? (assume-lhs-list-p xs) t)
    :returns (r svavar-list-p :hyp (and (booleanp lhs?) (svavar-list-p lst)))
    (if (atom xs)
        lst
      (assume-lst->svavar-lst
       (cdr xs)
       lhs?
       (assume->svavar-lst (car xs) lhs? lst))))

  ///
  (verify-guards assume->svavar-lst
    :hints (("Goal" :in-theory (enable assume-lhs-p
                                       assume-lhs-list-p
                                       part-select-p)))
    )
  )

(define assoc-svavar (name (vars svavar-list-p))
  "Find an svavar, by name, in a list of svavars"
  :returns r
  (if (atom vars)
      nil
    (b* ((var (car vars))
         (svavar-name (svavar->name var)))
      (if (equal name svavar-name)
          (svavar-fix var)
        (assoc-svavar name (cdr vars)))))
  ///
  (defret svavar-p-<fn>
    (if r
        (svavar-p r)
      t))
  (defret svavar-p-<fn>-2
    (implies r
             (svavar-p r)))
  )

(define mk-sva-binds ((vl-var stringp)
                      (svavar svavar-p)
                      (w natp))
  "Create a Verilog expression to bind the value of a variable in the LHS of
                      the theorem"
  :returns (r string-listp)
  (b* (((when (not (svavar->val svavar)))
        (raise "All LHS vars must be assigned a value:
                     ~x0" vl-var))
       (ps (svavar->ps svavar)))
    (list
     (str::cat "(" vl-var ps " == "
               (4vec-to-verilog (svavar->val svavar) w)
               ")"))))

(define mk-sva-decls ((svavar svavar-p)
                      (w posp))
  "Create a verilog variable declaration."
  :returns (r string-listp)
  (b* ((name (symb+-to-verilog (svavar->name svavar)))
       (type "logic")
       (w-1 (1- w))
       (w-str (str::nat-to-dec-string w-1))
       (type-to-vl
        (if (posp w-1)
            (str::cat type " [" w-str ":0]")
          type))
       (initialize (if (equal type "logic")
                       ;; logic has default initialization of 'X since it is a
                       ;; 4-state data type (see SystemVerilog Manual, Section
                       ;; "Variable declarations" -- 6.8)
                       ";"
                     ;; User-defined types may not have a default
                     ;; initialization, so we must provide one. We supply 'X,
                     ;; which sets all bits to X (see SystemVerilog Manual,
                     ;; Section "Integer literal constants" -- 5.7.1)

                     ;; [VR]: Leaving this here in case we want to use other VL
                     ;; types later.
                     "='X;"))
       )
    (list (str::cat type-to-vl " " name initialize))))

(define mk-sva-assigns ((vl-var stringp)
                        (svavar svavar-p))
  :returns (r string-listp)
  "Create a verilog expression to assign a value to a variable"
  (b* ((name (symb+-to-verilog (svavar->name svavar))))
    (list (str::cat name " = "  vl-var))))

(define mk-sva-lhs-xmrs ((lhs-vars svavar-list-p)
                         (rhs-vars svavar-list-p)
                         (x true-listp)
                         (i natp)
                         (cfg svtv-sva-cfg-p)
                         (rhs-vars-seen symbol-listp))
  :returns (mv (b string-listp) (d string-listp) (a string-listp) (r symbol-listp))
  (b* (((svtv-sva-cfg c) cfg)
       (e (nth i (rest x)))
       (var (first x))
       ((unless (sv::svtv-entry-p e))
        (mv (raise "should be entry:~x0" e) nil nil nil))
       ((unless (stringp var))
        (mv (raise "should be string:~x0" var) nil nil nil))
       (look (assoc-equal var c.sizes))
       ((unless look)
        (mv (raise "should have found var in sizes:~x0" var) nil nil nil))
       (w (cdr look))
       ((unless (posp w))
        (mv (raise "internal error: should be positive:~x0" (list var w))
            nil nil nil))
       (var-xmr (if (member-equal var c.needs-xmr)
                (print-concat-mod (parse-concats var) c.target-mod)
              var))
       ((unless (and e
                     (not (sv::svtv-dontcare-p e))
                     (not (and (symbolp e) (member-eq e c.out-vars)))
                     (not (and (consp e) (symbolp (car e))
                               (member-eq (car e) c.out-vars)))))
        (mv nil nil nil (acl2::symbol-list-fix rhs-vars-seen)))
       (v (if (consp e) (car e) e))
       (v-lhs (or (assoc-svavar v lhs-vars)
                  (assoc-svavar (goto->var1 var i)
                                lhs-vars)))
       (v-rhs (assoc-svavar v rhs-vars))
       ;; What does it mean to translate an override mask var assumption to
       ;; verilog?
       (o (and (consp e) (consp (cdr e)) (cadr e)))
       (- (if (and o (or v-lhs v-rhs))
              (cw "not converting override mask ~x0 into an assumption" o) nil))

       (v-binds   (and v-lhs (mk-sva-binds var-xmr v-lhs w)))
       (v-decls   (and v-rhs (not (member-eq v rhs-vars-seen))
                       (mk-sva-decls v-rhs w)))
       (v-assigns (and v-rhs (mk-sva-assigns var-xmr v-rhs)))
       (rhs-vars-seen (if v-rhs (cons (svavar->name v-rhs)
                                      (acl2::symbol-list-fix rhs-vars-seen))
                        (acl2::symbol-list-fix rhs-vars-seen)))
       )
    (mv v-binds v-decls v-assigns rhs-vars-seen)))

(define mk-sva-lhs-step-xmrs ((lhs-vars svavar-list-p)
                              (rhs-vars svavar-list-p)
                              (x true-list-listp)
                              (i natp)
                              (cfg svtv-sva-cfg-p)
                              (rhs-vars-seen symbol-listp)
                              &optional
                              ((binds string-listp) 'nil)
                              ((decls string-listp) 'nil)
                              ((assigns string-listp) 'nil))
  :returns (mv b d a r)
  (if (endp x) (mv binds decls assigns rhs-vars-seen)
    (b* (((mv new-binds new-decls new-assigns new-rhs-vars-seen)
          (mk-sva-lhs-xmrs lhs-vars rhs-vars (first x) i cfg rhs-vars-seen)))
      (mk-sva-lhs-step-xmrs lhs-vars rhs-vars (rest x) i cfg
                            new-rhs-vars-seen
                            (append new-binds binds)
                            (append new-decls decls)
                            (append new-assigns assigns)
                            )))
  ///
  (defret string-listp-<fn>
    (implies (and (string-listp binds)
                  (string-listp decls)
                  (string-listp assigns))
             (and (string-listp b)
                  (string-listp d)
                  (string-listp a))))

  (defret symbol-listp-<fn>
    (implies (symbol-listp rhs-vars-seen)
             (symbol-listp r)))
  )

(fty::defprod
 sva-bda
 ((binds   string-listp)
  (decls   string-listp)
  (assigns string-listp)))

(fty::deflist sva-bda-list
              :elt-type sva-bda
              :short "A list of sva-bda-p"
              :true-listp t)

(define mk-sva-lhs-lst-xmrs ((lhs-vars svavar-list-p)
                             (rhs-vars svavar-list-p)
                             (x true-list-listp)
                             (n natp)
                             (cfg svtv-sva-cfg-p)
                             &key
                             ((i natp) '0)
                             ;; ensure no duplicate variable declaration in SVA
                             ((rhs-vars-seen symbol-listp) 'nil)
                             )
  :returns (r sva-bda-list-p)
  (if (zp n)
      ()
    (b* (((mv b d a new-rhs-vars-seen)
          (mk-sva-lhs-step-xmrs lhs-vars rhs-vars x i cfg rhs-vars-seen)))
      (append (and
               ;; when the SVTV uses both edges of the clock
               (or (not (svtv-sva-cfg->double-clock cfg))
                   (clk-is-high-xmr x i cfg))
               (list (make-sva-bda :binds b :decls d :assigns a)))
              (mk-sva-lhs-lst-xmrs lhs-vars rhs-vars x (1- n) cfg
                                   :i (1+ i)
                                   :rhs-vars-seen new-rhs-vars-seen)))))

(define sva-finish-lhs ((binds-lst string-list-list-p)
                        (assigns-lst string-list-list-p))
  :returns (r string-listp)
  (if (endp binds-lst)
      (if (endp assigns-lst)
          nil
        (raise "unexpected error: binds and assigns are unequal in length!"))
    (b* ((binds   (first binds-lst))
         (assigns (first assigns-lst)))
      (append (list "(")
              (indent
               (append
                (and (consp assigns)
                     (list "("))
                (indent (if (endp binds)
                            (list "1'b1")
                          (add-literals binds " &&")))
                (and (consp assigns)
                     (list "),"))
                (and (consp assigns)
                     (add-literals assigns ","))))
              (list ")")
              (and (consp (rest binds-lst))
                   (list "##1"))
              (sva-finish-lhs (rest binds-lst) (rest assigns-lst))))))

(define gather-sva-bdas ((sva-bdas sva-bda-list-p)
                         &optional
                         ((all-binds   string-list-list-p) 'nil)
                         ((all-decls   string-listp) 'nil)
                         ((all-assigns string-list-list-p) 'nil)
                         ;; true if all stages before this one had empty binds,
                         ;; decls, and assigns
                         ((can-prune? booleanp) 't)
                         )
  :returns (mv ab ad aa)
  (if (atom sva-bdas)
      (mv all-binds all-decls all-assigns)
    (b* ((bda     (first sva-bdas))
         (binds   (sva-bda->binds   bda))
         (decls   (sva-bda->decls   bda))
         (assigns (sva-bda->assigns bda))

         ((when (and can-prune? (not (or binds decls assigns))))
          (gather-sva-bdas (cdr sva-bdas) all-binds all-decls all-assigns can-prune?))

         (all-binds   (append all-binds (list binds)))
         (all-decls   (append all-decls decls)) ;; flatten decls
         (all-assigns (append all-assigns (list assigns))))
      (gather-sva-bdas (cdr sva-bdas) all-binds all-decls all-assigns nil)))
  ///
  (defret listps-<fn>
    :hyp :guard
    (and (string-list-list-p ab)
         (string-listp ad)
         (string-list-list-p aa))))

(define prune-sva-bdas ((sva-bdas sva-bda-list-p))
  "Remove all stages, starting from beginning, that are empty until the first
                       non-empty stage"
  :returns (r sva-bda-list-p)
  (if (atom sva-bdas)
      (sva-bda-list-fix sva-bdas)
    (b* ((sva-bda (car sva-bdas))
         (binds (sva-bda->binds sva-bda))
         (decls (sva-bda->decls sva-bda))
         (assigns (sva-bda->assigns sva-bda)))
      (if (not (or binds decls assigns))
          (prune-sva-bdas (cdr sva-bdas))
        (sva-bda-list-fix sva-bdas)))))

(define prune-sva-bdas-from-end ((sva-bdas sva-bda-list-p))
  "Remove all stages, starting from the end, that are empty until the first non-empty stage"
  :returns (r sva-bda-list-p)
  (reverse (prune-sva-bdas (reverse sva-bdas))))

(define str::cat-lst ((x string-listp))
  (str::fast-string-append-lst x))

; Some helper functions for converting assumption theorem RHS to SVA format

(define int->verilog ((x integerp))
  :returns (r string-listp)
  (cond ((natp x)
         (b* ((size (if (= x 0) 1 (integer-length x))))
           (list (str::cat
                  ;; size
                  (str::int-to-dec-string size)
                  ;; decimal
                  "'d"
                  ;; unsigned number
                  (str::int-to-dec-string x)))))
        (t ;; signed negative 32-bit integer
         (if (< x (- (expt 2 31)))
             (raise "Expected a 32-bit signed integer: ~x0" x)
           (list (str::int-to-dec-string x))))))

(define sva-rhs-to-sva-atom ((x atom))
  :returns (r string-listp)
  (cond ((symbolp x)   (list (symb+-to-verilog x)))
        (t (raise "Unsupported atom encountered: ~x0" x))))

(define sva-rhs-to-sva-const ((const quotep))
  :returns (r string-listp)
  (b* ((fn (car const))
       ((unless (and (conspn const 2)
                     (atom (unquote const))))
        (raise "~x0 expects one atom argument: ~x1" fn const))
       (x (unquote const)))
  (cond ((booleanp x)  (if x (list "1'h1") (list "1'h0")))
        ;; Verilog reference: integer literals can be used in
        ;; expressions. Integers can be unbased and unsized.
        ((integerp x)
         (int->verilog x))
        ;; Should we support converting 4vec to verilog for
        ;; assumptions?
        (t (raise "Unsupported constant encountered: ~x0" x)))))

; Convert RHS of assumption theorem to SVA format
(make-event
 `(defines
    sva-rhs-to-sva
    :verify-guards nil
    (define sva-rhs-to-sva (x)
      :parents (|Generating SVAs from Assumptions|)
      :short "Convert the RHS of an ACL2 theorem into SVA RHS"
      :hints (("Goal" :in-theory (disable acl2-count)))
      :returns (r string-listp)
      (if (atom x)
          (sva-rhs-to-sva-atom x)
        (b* ((fn (car x))
             (args (cdr x))
             ((unless (symbolp fn))
              (raise "Expected function to be a symbol: ~x0"
                     x))

             ((when (eq fn 'quote))
              (sva-rhs-to-sva-const x))

             (args-sva (sva-rhs-lst-to-sva args)))

          (make-subst fn args-sva))))

    (define sva-rhs-lst-to-sva (xs)
      :returns (r :hyp :guard string-listp)
      (if (atom xs)
          nil
        (b* ((result (sva-rhs-to-sva (car xs))))
            (cons (str::cat-lst result)
                  (sva-rhs-lst-to-sva (cdr xs))))))

    ///
    (verify-guards sva-rhs-to-sva)
    ))

(define sva-rhs-to-sva-members ((member-calls symbol-alistp))
  :returns (r :hyp :guard string-listp)
  (if (atom member-calls)
      nil
    (b* ((fn 'member-equal)
         (pair      (car member-calls))
         (var-name  (symb+-to-verilog (car pair)))
         (form      (cdr pair)))
      (case-match form
        (('member-equal arg1 array)
         (b* ((val (sva-rhs-to-sva arg1))
              ((unless (symbolp array))
               (raise "Expected the second argument to be a name of an
                  array: ~x1" form))
              (result (list (str::cat var-name " = 0,")
                            ;; `member(val,array,var) ;; assigns var the result
                            (str::cat
                             (str::cat-lst
                              (make-subst
                               fn
                               (list (str::cat-lst val)
                                     (symbol-name array)
                                     var-name)))
                             (if (consp (cdr member-calls))
                                 ","
                               "")))))
           (append result (sva-rhs-to-sva-members (cdr member-calls)))))
        (& (raise "Error: form expected to be a member call: ~x0" form))))))

(fty::defalist symbol-integer-list-alist
  :key-type symbol
  :val-type integer-listp
  :true-listp t)

(define mk-sva-array-decls ((array-decls symbol-integer-list-alist-p))
  :returns (res string-listp)
  (if (atom array-decls)
      nil
    (b* ((pair (car array-decls))
         (name (symbol-name (car pair)))
         (array (cdr pair)))
      (cons (str::cat "int " name
                      " [" (str::nat-to-dec-string (len array)) "];")
            (mk-sva-array-decls (cdr array-decls))))))

(define mk-sva-array-assigns ((array-decls symbol-integer-list-alist-p))
  :returns (res string-listp)
  (if (atom array-decls)
      nil
    (b* ((pair (car array-decls))
         (name (symbol-name (car pair)))
         (array (cdr pair)))
      (cons (str::cat name " = '"
                      (integer-list->vl-array array)
                      (if (atom (cdr array-decls)) "" ","))
            (mk-sva-array-assigns (cdr array-decls))))))

(define mk-sva-member-var-decls ((member-calls symbol-alistp))
  "Declarations for variables that will store the result of calling member in
   SVA"
  :returns (res string-listp)
  (if (atom member-calls)
      nil
    (b* ((pair (car member-calls))
         (name (car pair)))
      (cons (str::cat "logic "
                      (symb+-to-verilog name)
                      ";")
            (mk-sva-member-var-decls (cdr member-calls))))))

(local (defthm true-list-listp-of-append
         (implies (and (true-list-listp x)
                       (true-list-listp y))
                  (true-list-listp (append x y)))))

(define mk-sva-property
  ((name stringp               "name of the property to generate")
   (lhs-vars svavar-list-p     "list of SVTV vars in the thm LHS")
   (rhs-vars svavar-list-p     "list of SVTV vars in the thm RHS")
   (rhs                        "RHS of ACL2 thm")
   (arrays symbol-integer-list-alist-p
                               "alist of arrays in the thm")
   (member-calls symbol-alistp "alist of member forms in the thm")
   (orig-thm                   "original thm submitted to assume-to-sva")
   (svtv sv::svtv-p)
   (cfg svtv-sva-cfg-p))
  "Generate the SystemVerilog property for the SVA"
  :returns (r string-listp)
  (b* (((sv::svtv s) svtv)
       ((svtv-sva-cfg c) cfg)
       (- "1. Determine number of phases to include from SVTV")
       (nphases s.nphases)
       (- "2. Compute the assumptions (SVA LHS) in the generated property")
       ;; Abuse XMRs
       (sva-bdas (mk-sva-lhs-lst-xmrs lhs-vars rhs-vars
                                      (append s.orig-ins s.orig-overrides)
                                      nphases c))
       (- "3. Remove all stages, starting from the end, until the first non-empty bda")
       (sva-bdas (prune-sva-bdas-from-end sva-bdas))
       (- "4. Gather the predicate bindings and local variable declarations/assigns")
       ((mv binds decls assigns) (gather-sva-bdas sva-bdas))
       ;; Consider SystemVerilog statement -- int ar1 [3] = '{1, 2, 3}; This is
       ;; a valid declaration and initialization for a local variable in a
       ;; property. However, if ar1 is not assigned a value by the sequence in
       ;; the property , and thus does not "flow" out of it, then it will
       ;; become unassigned at the end of the subsequence. See SRM 11.10,
       ;; "Local Variables". We therefore declare arrays as local variables at
       ;; the property-level, and then assign them their constant-value at the
       ;; end of the sequence, so they do not become unassigned by the end of
       ;; the sequence. Note that this can also be achieved by declaring and
       ;; initializing the arrays at the module-level.
       (array-decls   (mk-sva-array-decls arrays))
       (array-assigns (mk-sva-array-assigns arrays))
       (array-assigns (if array-assigns
                          (cons "," array-assigns)
                        array-assigns))
       (member-call-decls   (mk-sva-member-var-decls member-calls))
       (member-call-assigns (sva-rhs-to-sva-members member-calls))
       (member-call-assigns (if member-call-assigns
                                (cons "," member-call-assigns)
                              member-call-assigns)))
    (append (list (str::cat " property " name ";"))
            (list "/*")
            (list
             (str::pretty orig-thm
                          :config
                          (str::change-printconfig
                           str::*default-printconfig*
                           :home-package 'pkg)))
            (list "*/")
            (indent
             (append decls
                     ;; declarations of local variables used for array lookups
                     array-decls
                     member-call-decls

                     (list (str::cat "@(posedge " c.clk ") disable iff (" c.rst
                                     ")"))
                     (list "(")
                     (indent (append (list "(")
                                     ;; LHS
                                     (sva-finish-lhs binds assigns)
                                     array-assigns
                                     member-call-assigns
                                     (list ")")
                                     (list "|->")
                                     ;; RHS
                                     (format-rhs
                                      (str::cat-lst (sva-rhs-to-sva rhs)))))
                     (list ");")))
            (list " endproperty")
            (list "")
            (list (str::cat name "_assert: assert property (" name ");"))
            ;; (list (str::cat name "_cover: cover property (" name ");"))
            )))

(define-stub assume-to-sva-package-imports
  ()
  :short "A list of SystemVerilog package imports statements."
  :returns
  (r string-listp))

(define assume-to-sva-package-imports-default
  ()
  :returns (r string-listp)
  nil)

(defattach assume-to-sva-package-imports
  assume-to-sva-package-imports-default)

(define assume-to-sva-mod ((cfg svtv-sva-cfg-p))
  "Generate preamble for SystemVerilog module definition"
  :returns (r string-listp)
  (b* (((svtv-sva-cfg c) cfg)
       ;; Import packages that contain typedefs we may need.
       (package-imports (assume-to-sva-package-imports)))
    (append (list (str::cat "module " c.prop-mod))
            package-imports
            (indent (list "();"))
            (indent
             (list
              (str::cat "logic " c.clk ";")
              (str::cat "assign " c.clk " = " c.target-mod "." c.clk ";")
              (str::cat "logic " c.rst ";")
              (str::cat "assign " c.rst " = " c.target-mod "." c.rst ";"))))))

(local
 (defthm car-symbolp-svtv-p
   (implies (sv::svtv-p x)
            (symbolp (car x)))
   :hints (("Goal" :in-theory (enable sv::svtv-p)))))

;; determining which directory to save into
(define-stub sva-run-assume-file
  ((run symbolp) (cfg svtv-sva-cfg-p)
   (filename acl2::maybe-stringp))
  :short "Given an input SVTV and CFG, return the full path name for the file
where the SVTV's SVAs will be saved. Filename is an optional override for the
generated filename."
  :returns (r stringp))

(define sva-run-assume-file-default
; A default function for sva-run-assume-file that can be overridden using a
; defattach event.
  ((run symbolp) (cfg svtv-sva-cfg-p)
   (filename acl2::maybe-stringp))
  :returns (r stringp)
  (b* ((mod-dir (sva-run-mod-dir run))
       ;; (dir (sva-run-sv-dir x))
       (dut (sva-run-dut-name run))
       (repo (svtv-sva-cfg->repo-path cfg))
       (suffix (svtv-sva-cfg->filename-suffix cfg))
       (filename (if filename
                     filename
                   (str::cat "acl2_assume_" suffix ".sv")))
       )
    (str::cat repo "assume-to-sva/svas/" dut "/"
              mod-dir "/" (symb+-to-verilog run) "/" filename)))

(defattach sva-run-assume-file sva-run-assume-file-default)

(define acl2_array-class ()
  :returns (r string-listp)
  "Define SystemVerilog function to search for an element in an array"
  (append
   (list "")
   (list "class acl2_array #(int size = 1);"
         "")
   (indent
    (append
     (list "// search for a value in an array")
     (list "static function logic find(int ar [size], int val);")
     (indent
      (append
       (list
        "find = 1'h0;"
        "for (int i = 0; i < $size(ar); ++i)")
       (indent
        (append
         (list "begin")
         (indent (list "if (ar[i] == val) find = 1'b1;"))
         (list "end")))))
     (list "endfunction")))
   (list "endclass")
   (list "")
   ;; Properties and sequences do not allow expressions "involving real,
   ;; realtime, string, event and dynamic SystemVerilog types" in local
   ;; variable assignments. But they do allow subroutine call statements in the
   ;; sequence_match_item. So, define a void function, which will assign the
   ;; local variable the value of membership test.
   (list "function void give(logic val, ref logic x);")
   (list "x = val;")
   (list "endfunction")
   (list "")
   (list "// macro for member in SystemVerilog")
   (list "`define member(val,array,var_name) give(acl2_array#($size(array))::find(array, val), var_name)")
   (list "")
   )
  )

(defstub write-cfg-file
  ;; A configurable function that can write out a config file for use with other tools.
  (* * * state) => state
  :formals (out-file instance-name filename state)
  :guard (and (stringp out-file)
              (stringp instance-name)
              (stringp filename)))

(define write-cfg-file-default
  (out-file instance-name filename state)
  (declare (ignore out-file instance-name filename))
  state)

; By default, write-cfg-file will do nothing.
(defattach write-cfg-file write-cfg-file-default)

(define sva-start-after-assertprop ((x string-listp))
  :returns (r string-listp :hyp :guard)
  (cond ((endp x) ())
        ((str::substrp "assert property" (first x))
         (rest x))
        (t (sva-start-after-assertprop (rest x))))
  ///
  (defthm len-of-sva-start-after-assertprop
    (<= (len (sva-start-after-assertprop x))
        (len x))
    :rule-classes (:rewrite :linear)))

(define sva-remove-prop-lines ((x string-listp) (prop stringp))
  :returns (r string-listp :hyp :guard)
  :measure (len x)
  (cond ((endp x) ())
        ((and (str::substrp "property" (first x))
              (b* ((toks (sva-std-verilog-toks (first x))))
                (and (member-equal "property" toks)
                     (member-equal prop toks))))
         (sva-remove-prop-lines (sva-start-after-assertprop (rest x)) prop))
        (t (cons (first x)
                 (sva-remove-prop-lines (rest x) prop)))))

(define assume-to-sva-fn
  ((lhs              "lhs of thm after preprocessing")
   (rhs              "rhs of thm after preprocessing")
   (orig-thm         "original thm submitted to assume-to-sva")
   (prop stringp     "base name of property module containing property")
   (member-calls symbol-alistp
                     "alist of variables in rhs that correspond to a member term")
   (svtv sv::svtv-p  "svtv used to generate the property along with env")
   (repo stringp     "path to the top of the FV repo")
   ;; mapping of array names to list of values
   (arrays symbol-integer-list-alist-p
                     "mapping of array names to list of values")
   (inst acl2::maybe-stringp
                     "name of the module instance to bind to. This will
  generate a custom bind statement.")
   (inst-cfg-prefix stringp
                     "prefix for the generated cfg file if the inst input argument was provided."
                      )
   (xmr-override acl2::maybe-stringp
                     "override the XMR references with a custom constant string")
   &key
   (state 'state))
  :parents (|Generating SVAs from Assumptions|)
  :short "Generate a SystemVerilog file with a module that contains an
  assertion for checking ACL2 proof assumptions"
  (b* ((- "0. Some preprocessing")
       (run  (car svtv))
       (- "1. Extract data from the assumption theorem")

       (prop (str::cat "acl2_" prop))

       ((unless (assume-lhs-p lhs))
        (prog2$ (raise "Expected LHS of input theorem to satisfy assume-lhs-p")
                state))

       (lhs-vars (assume->svavar-lst lhs t nil))
       (rhs-vars (assume->svavar-lst rhs nil nil))
       ;; the member forms are part of the RHS. Their references to svtv
       ;; variables must be determined.
       (rhs-vars (assume-lst->svavar-lst
                  (strip-cdrs member-calls) nil rhs-vars))

       (- "2. Extract data from the SVTV")

       ((sv::svtv s) svtv)
       (cfg (make-svtv-sva-cfg))
       (checker-mod (str::cat (symb+-to-verilog run) "_mod"))
       ;; [VR]: I don't think we will be dealing with out-vars ("variables
       ;; which should be treated as outputs if they are overrides")
       (out-vars nil)
       (cfg (change-svtv-sva-cfg cfg
                                 :prop-mod checker-mod
                                 :out-vars out-vars
                                 :filename-suffix checker-mod
                                 ))
       ((svtv-sva-cfg c)
        (svtv-fill-in-cfg run svtv repo cfg))
       (out-file (sva-run-assume-file run c nil))

       (c (if (and inst xmr-override)
              (change-svtv-sva-cfg c
                                   :target-mod xmr-override)
            c))
       (sva-property
        (mk-sva-property prop lhs-vars rhs-vars rhs arrays
                         member-calls orig-thm svtv c))
       (property-file
        (sva-run-assume-file run c
                             "properties.sv"))
       (new-lines
        (append (acl2_array-class)
                (list "")
                (assume-to-sva-mod c)
                (list "")
                (list
                 (str::cat "`include \"" property-file "\""))
                ;; sva-property
                (list "")
                (list "endmodule")
                (list "")
                (and (not inst)
                     (svtv-to-sva-bind c))
                (list "")))
       (state
        (if inst
            (write-cfg-file
             out-file inst
             (sva-run-assume-file run c
                                  (str::cat inst-cfg-prefix
                                            inst
                                            ".cfg"))
             state
             )
          state))
       ;; properties.sv file
       (read-text  (acl2::read-file-into-string property-file))
       (read-text  (if (stringp read-text) read-text ""))
       (read-lines (str::strtok! read-text (list #\Newline)))
       (read-lines (sva-remove-prop-lines read-lines prop))
       (state
        (write-out-strs property-file
                        (append sva-property read-lines)
                        state)))
       ;; module file
    (write-out-strs out-file new-lines state)))

(acl2::defmacro+ assume-to-sva (thm prop svtv
                                    &key
                                    (inst 'nil)
                                    (inst-cfg-prefix '"")
                                    (xmr-override 'nil)
                                    )
  :short "Top-level macro for converting a theorem, property name, and SVTV
  into an SVA file."
  :parents (|Generating SVAs from Assumptions|)
  (declare (xargs :guard (and (stringp prop)
                              (consp svtv)
                              (symbolp (car svtv))
                              (null (cdr svtv))
                              (acl2::maybe-stringp inst))))
  `(make-event (b* ((- "1. Preprocess the ACL2 thm to known fn->vl functions")
                    ((mv lhs rhs arrays member-calls state) (assume-to-sva-preprocess
                                    ,thm ,svtv))
                    (- "2. Determine the top-level fv repo path")
                    (alst (acl2::project-dir-alist (w state)))
                    ((unless (alistp alst))
                     (prog2$ (cw "project-dir-alist should be alist:~x0" alst)
                             (value '(value-triple nil))))
                    (repo (cdr (assoc-eq :FV alst)))
                    ((unless (stringp repo))
                     (prog2$
                      (cw "project-dir-alist FV entry should be string:~x0" alst)
                      (value '(value-triple nil))))
                    (- "3. Convert the ACL2 thm into an SVA and write to a file")
                    (state (assume-to-sva-fn lhs
                                             rhs
                                             ,thm
                                             (quote ,prop)
                                             member-calls
                                             ,svtv
                                             repo
                                             arrays
                                             ,inst
                                             ,inst-cfg-prefix
                                             ,xmr-override
                                             )))
                 (value '(value-triple t)))))

