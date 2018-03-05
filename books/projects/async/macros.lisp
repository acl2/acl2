;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "assoc-eq-value")
(include-book "hard-spec")

;; ======================================================================

(defun unstring (str1 str2)
  (declare (xargs :guard (and (stringp str1) (stringp str2))))
  (intern$ (string-append str1 str2) "ADE"))

(defun var-to-const (x)
  (declare (xargs :guard (symbolp x)))
  (intern$ (concatenate 'string "*" (symbol-name x) "*")
           "ADE"))

(defun state-accessors-gen (module sts idx)
  (declare (xargs :guard (and (symbolp module)
                              (symbol-listp sts)
                              (natp idx))))
  (if (atom sts)
      nil
    (b* ((st (car sts))
         (name (intern$ (concatenate 'string
                                     "*"
                                     (symbol-name module)
                                     "$"
                                     (symbol-name st)
                                     "*")
                        "ADE")))
      (cons `(defconst ,name ,idx)
            (state-accessors-gen module (cdr sts) (1+ idx))))))

(defmacro netlist-hyps (netlist &rest modules)
  (if (atom modules)
      nil
    (if (atom (cdr modules))
        `(equal (assoc ',(car modules) ,netlist)
                (car ,(var-to-const (car modules))))
      `(netlist-hyps (delete-to-eq ',(car modules) ,netlist)
                     ,@(cdr modules)))))

(defmacro not-primp-lemma (fn)
  (b* ((thm-name (unstring "NOT-PRIMP-" (symbol-name fn))))
    `(defthmd ,thm-name
       (not (primp (si ',fn n)))
       :hints (("Goal" :in-theory (enable primp))))))

;; ======================================================================

(defun b-to-f (body)
  (cond ((atom body) nil)
        ((consp (car body))
         (cons (b-to-f (car body))
               (b-to-f (cdr body))))
        ((symbolp (car body))
         (let ((sym-name (symbol-name (car body))))
           (cond ((and (<= 2 (length sym-name))
                       (equal (subseq sym-name 0 2)
                              "B-"))
                  (cons (unstring "F-"
                                  (subseq sym-name 2 (length sym-name)))
                        (b-to-f (cdr body))))
                 ((equal sym-name "AO2")
                  (cons (unstring "F$" sym-name)
                        (b-to-f (cdr body))))
                 (t
                  (cons (cond ((equal (car body) t) T)
                              ((equal (car body) nil) NIL)
                              (t (car body)))
                        (b-to-f (cdr body)))))))
        (t (cons (car body)
                 (b-to-f (cdr body))))))

(defun fn-to-module-outs (body)
  (cond ((atom body) nil)
        ((consp (car body))
         (append (fn-to-module-outs (car body))
                 (fn-to-module-outs (cdr body))))
        ((equal (car body) 'list)
         (cdr body))
        (t (fn-to-module-outs (cdr body)))))

(defun fn-to-module-body (i body)
  (cond ((atom body) nil)
        ((consp (car body))
         (cons (fn-to-module-body i (car body))
               (fn-to-module-body (1+ i) (cdr body))))
        ((equal (car body) 'list)
         nil)
        ((or (equal (car body) 'let)
             (equal (car body) 'let*)
             (equal (car body) 'b*))
         (append (fn-to-module-body i (cadr body))
                 (fn-to-module-body (+ i (len (cadr body)))
                                    (caddr body))))
        ((symbolp (car body))
         (cond
          ((not (cadr body))
           (list (unstring "G" (str::natstr i))
                 (list (car body))
                 'vss
                 ()))
          ((equal (cadr body) t)
           (list (unstring "G" (str::natstr i))
                 (list (car body))
                 'vdd
                 ()))
          ((symbolp (cadr body))
           (list (unstring "G" (str::natstr i))
                 (list (car body))
                 'id
                 (list (cadr body))))
          (t (list (unstring "G" (str::natstr i))
                   (list (car body))
                   (caadr body)
                   (cdadr body)))))
        (t nil)))

(defun flatten-expr (var i expr)
  (declare (xargs :guard (and (symbolp var)
                              (natp i))))
  (cond ((atom expr) nil)
        (t (cons (if (consp (car expr))
                     (si var i)
                   (car expr))
                 (flatten-expr var (1+ i) (cdr expr))))))

(defun flatten-binding (var i body outermost-p)
  (cond
   ((atom body) nil)
   ((equal (car body) 'list)
    body)
   ((consp (car body))
    (append (flatten-binding var i (car body) outermost-p)
            (flatten-binding var (1+ i) (cdr body) outermost-p)))
   ((or (equal (car body) 'let)
        (equal (car body) 'let*)
        (equal (car body) 'b*))
    (list (car body)
          (flatten-binding var 0 (cadr body) t)
          (flatten-binding var 0 (caddr body) t)))
   ((symbolp (car body))
    (b* ((var_i (si var i))
         (sym (car body))
         (sym-name (symbol-name sym)))
      (cond
       ((or (and (<= 2 (length sym-name))
                 (equal (subseq sym-name 0 2)
                        "B-"))
            (equal sym-name "AO2"))
        (append (flatten-binding (if outermost-p var var_i)
                                 0 (cdr body) nil)
                (list
                 (cons (if outermost-p var var_i)
                       `((,sym ,@(flatten-expr (if outermost-p var var_i)
                                               0
                                               (cdr body))))))))
       (outermost-p
        (if (symbolp (cadr body))
            (list body)
          (flatten-binding sym 0 (cdr body) outermost-p)))
       (t (flatten-binding var (1+ i) (cdr body) outermost-p)))))
   (t nil)))

(defmacro fn-to-module (name ins declare body)
  (b* ((f$name (unstring "F$" (symbol-name name)))
       (netlist-const (var-to-const name))
       (netlist-okp (unstring (symbol-name name) "-OKP"))
       (netlist-properp (unstring (symbol-name name)
                                  "&"))
       (value-lemma (unstring (symbol-name name) "$VALUE"))
       (boolp-value-lemma (intern$ (concatenate 'string
                                                (symbol-name f$name)
                                                "="
                                                (symbol-name name))
                                   "ADE"))
       (boolp-ins (pairlis$ (make-list (len ins)
                                       :initial-element 'booleanp)
                            (pairlis$ ins nil)))
       (outs (fn-to-module-outs body)))
    `(progn
       (defun ,name ,ins
         ,declare
         ,body)

       (defun ,f$name ,ins
         ,declare
         ,(b-to-f body))

       (defconst ,netlist-const
         '((,name
            ,ins
            ,(if (atom outs) (list 'x) outs)
            ()
            ,(fn-to-module-body 0 (flatten-binding 'x 0 body t)))))

       (defthmd ,netlist-okp
         (and (net-syntax-okp ,netlist-const)
              (net-arity-okp ,netlist-const)))

       (defund ,netlist-properp (netlist)
         (declare (xargs :guard (alistp netlist)))
         (netlist-hyps netlist ,name))

       (defthmd ,value-lemma
         (implies (,netlist-properp netlist)
                  (equal (se ',name (list ,@ins) sts netlist)
                         ,(if (atom outs)
                              `(list (,f$name ,@ins))
                            `(,f$name ,@ins))))
         :hints (("Goal"
                  :expand (se ',name (list ,@ins) sts netlist)
                  :in-theory (enable de-rules ,netlist-properp))))

       (defthm ,boolp-value-lemma
         (implies (and ,@boolp-ins)
                  (equal (,f$name ,@ins)
                         (,name ,@ins)))
         :hints (("Goal" :in-theory (disable b-gates))))

       (in-theory (disable ,f$name ,name))
       )))

;; ======================================================================

;; DESTRUCTURING-LEMMA generator

;; Because of quirks in equality reasoning, it "doesn't work" to simply let
;; module definitions open up.  Instead, we use a lemma that explicitly states
;; how to destructure a module definition.

(defmacro destructuring-lemma (fn args declare-form bindings
                                  name ins outs sts occs)
  (b* ((destructure (unstring (symbol-name fn) "$DESTRUCTURE"))
       (form `(,fn ,@args)))

    `(progn
       (defun ,fn ,args
         ,declare-form
         (let ,bindings
           (list ,name ,ins ,outs ,sts ,occs)))

       (defthmd ,destructure
         (let ,bindings
           (AND
            (EQUAL (CAR ,form) ,name)
            (EQUAL (CADR ,form) ,ins)
            (EQUAL (CADDR ,form) ,outs)
            (EQUAL (CADDDR ,form) ,sts)
            (EQUAL (CAR (CDDDDR ,form)) ,occs))))

       (in-theory (disable ,fn)))))

;; MODULE-GENERATOR generator args name inputs outputs body state.

(defmacro module-generator (generator args name inputs outputs sts body
                                      &key guard)
  (let ((destructuring-lemma (unstring (symbol-name generator)
                                       "$DESTRUCTURE"))
        (form `(,generator ,@args)))

    `(progn
       (defun ,generator ,args
         (declare (xargs :guard ,guard))
         (LIST ,name ,inputs ,outputs ,sts ,body))

       (defthmd ,destructuring-lemma
         (AND
          (EQUAL (CAR ,form) ,name)
          (EQUAL (CADR ,form) ,inputs)
          (EQUAL (CADDR ,form) ,outputs)
          (EQUAL (CADDDR ,form) ,sts)
          (EQUAL (CAR (CDDDDR ,form)) ,body)))

       (in-theory (disable ,generator)))))

;; Generating value or state lemmas for primitives

(defun primitives-lemmas-gen (eval primitives)
  ;; @eval is either 'se (for value lemmas) or 'de (for state lemmas)
  (if (atom primitives)
      nil
    (b* ((prim (car primitives))
         (fn (car prim))
         (expr (cadr prim))
         (thm-name (intern$ (concatenate 'string
                                         (symbol-name eval)
                                         "-"
                                         (symbol-name fn))
                            "ADE"))
         (eval-primp-apply (unstring (symbol-name eval) "-PRIMP-APPLY")))
      (cons `(defthm ,thm-name
               (equal (,eval ',fn ins sts netlist)
                      ,expr)
               :hints (("Goal" :in-theory (enable ,eval-primp-apply))))
            (primitives-lemmas-gen eval (cdr primitives))))))

;; ======================================================================

;; Define both vector (V_) and natural (N_) forms of the states.

(defun add-prefix-to-name (prefix name)
  (declare (xargs :guard (and (stringp prefix)
                              (symbolp name))))
  (intern$ (string-append prefix (symbol-name name))
           "ADE"))

(defun add-prefix-to-names (prefix names)
  (declare (xargs :guard (and (stringp prefix)
                              (symbol-listp names))))
  (if (atom names)
      nil
    (cons (add-prefix-to-name prefix (car names))
          (add-prefix-to-names prefix (cdr names)))))

(defun add-prefix-to-state-names (prefix control-states)
  (declare (xargs :guard (and (stringp prefix)
                              (symbol-alistp control-states))))
  (if (atom control-states)
      nil
    (cons (add-prefix-to-name prefix (caar control-states))
          (add-prefix-to-state-names prefix (cdr control-states)))))

(defun define-control-states (control-states)
  (declare (xargs :guard (symbol-alistp control-states)))
  (if (atom control-states)
      nil
    (b* ((name (caar control-states))
         (val  (cdar control-states))
         (vector-state-name (string-append "V_" (symbol-name name)))
         (natural-state-name (string-append "N_" (symbol-name name)))
         (vn (intern$ vector-state-name "ADE"))
         (nn (intern$ natural-state-name "ADE"))
         (bvp-vn-lemma (unstring "BVP-" vector-state-name))
         (len-vn-lemma (unstring "LEN-" vector-state-name)))
      (append `((defun ,vn ()
                  (declare (xargs :guard t))
                  ,val)

                (defthm ,bvp-vn-lemma
                  (bvp (,vn))
                  :rule-classes (:rewrite :type-prescription))

                (defthmd ,len-vn-lemma
                  (equal (len (,vn)) 5))

                (defun ,nn ()
                  (declare (xargs :guard t))
                  (v-to-nat ,val)))
              (define-control-states (cdr control-states))))))

;; Define an accessor for each entry in the control vector.

(defun define-control-vector-accessors (i control-template)
  (if (atom control-template)
      nil
    (b* ((field      (caar control-template))
         (type/size  (cadar control-template)))
      (if (equal type/size 'b)
          (cons `(defun ,field (cntl-vector)
                   (declare (xargs :guard (true-listp cntl-vector)))
                   (nth ,i cntl-vector))
                (define-control-vector-accessors
                  (1+ i)
                  (cdr control-template)))
        (cons `(defun ,field (cntl-vector)
                 (declare (xargs :guard (true-listp cntl-vector)))
                 (subseq-list cntl-vector ,i ,(+ i type/size)))
              (define-control-vector-accessors
                (+ i type/size)
                (cdr control-template)))))))

;; CONTROL-LET
;; A macro for a LET that extracts and computes necessary fields and flags.

(defun control-let (body)
  (declare (xargs :guard t))
  `(B* ((A-IMMEDIATE-P (A-IMMEDIATE-P I-REG))
        (MODE-A        (MODE-A        I-REG))
        (?RN-A          (RN-A          I-REG))
        (MODE-B        (MODE-B        I-REG))
        (?RN-B          (RN-B          I-REG))
        (SET-FLAGS     (SET-FLAGS     I-REG))
        (STORE-CC      (STORE-CC      I-REG))
        (OP-CODE       (OP-CODE       I-REG)))
     (B* ((A-IMMEDIATE-P-     (NOT* A-IMMEDIATE-P))
          (STORE              (STORE-RESULTP STORE-CC FLAGS))
          (?SET-SOME-FLAGS    (SET-SOME-FLAGS SET-FLAGS))
          (DIRECT-A           (OR* A-IMMEDIATE-P (REG-DIRECT-P MODE-A)))
          (DIRECT-B           (REG-DIRECT-P MODE-B))
          (UNARY              (UNARY-OP-CODE-P OP-CODE))
          (PRE-DEC-A          (PRE-DEC-P MODE-A))
          (POST-INC-A         (POST-INC-P MODE-A))
          (PRE-DEC-B          (PRE-DEC-P MODE-B))
          (POST-INC-B         (POST-INC-P MODE-B))
          (?C                 (C-FLAG FLAGS))
          (?ALL-T-REGS-ADDRESS (EQUAL REGS-ADDRESS *v1111*)))
       (B* ((?STORE-        (NOT* STORE))
            (?DIRECT-A-     (NOT* DIRECT-A))
            (?DIRECT-B-     (NOT* DIRECT-B))
            (?UNARY-        (NOT* UNARY))
            (?SIDE-EFFECT-A (AND* A-IMMEDIATE-P-
                                  (OR* PRE-DEC-A POST-INC-A)))
            (?SIDE-EFFECT-B (OR* PRE-DEC-B POST-INC-B)))
         ,body))))

;; Use the *STATE-TABLE* to build a CV_state function for each state.  This is
;; the function that creates the control-vector for each state.  Note that the
;; reset states RESET0 and RESET1 are constants, and in these cases we don't
;; include the hypothesis.

(defun build-st (template)
  (if (atom template)
      nil
    (if (natp (cadar template))
        `(append ,(caddar template) ,(build-st (cdr template)))
      `(cons ,(caddar template) ,(build-st (cdr template))))))

(defun cv-lemma-concl (cv-name template control-arglist)
  (if (atom template)
      nil
    (b* ((field-tuple (car template))
         (field-name  (car field-tuple))
         (field-val   (caddr field-tuple)))
      (cons `(equal (,field-name (,cv-name ,@control-arglist))
                    ,field-val)
            (cv-lemma-concl cv-name (cdr template) control-arglist)))))

(defun update-template (update-fields control-template)
  (if (atom update-fields)
      control-template
    (b* ((field (car update-fields))
         (field-name (if (atom field)
                         field
                       (car field)))
         (field-type/default (assoc-eq-value field-name control-template))
         (field-type/val (if (atom field)
                             (list (car field-type/default)
                                   (not (cadr field-type/default)))
                           (list (car field-type/default)
                                 (cadr field))))
         (new-template (update-alist field-name field-type/val
                                     control-template)))
      (update-template (cdr update-fields) new-template))))

(defun add-prefix-and-suffix-to-name (prefix suffix name)
  (declare (xargs :guard (and (stringp prefix)
                              (stringp suffix)
                              (symbolp name))))
  (intern$ (concatenate 'string prefix (symbol-name name) suffix)
          "ADE"))

(defun add-prefix-and-suffix-to-state-names (prefix suffix states)
  (declare (xargs :guard (and (stringp prefix)
                              (stringp suffix)
                              (symbol-alistp states))))
  (if (atom states)
      nil
    (cons (add-prefix-and-suffix-to-name prefix suffix (caar states))
          (add-prefix-and-suffix-to-state-names prefix suffix (cdr states)))))

(defun define-control-vector-functions (state-table
                                        control-template
                                        control-arglist)
  (if (atom state-table)
      nil
    (b* ((state-trans (car state-table))
         (state-name (car state-trans))
         (cv-name (add-prefix-to-name "CV_" state-name))
         (bvp-cv-name (add-prefix-to-name "BVP-" cv-name))
         (cv-lemma-name (add-prefix-and-suffix-to-name "CV_"
                                                       "$DESTRUCTURE"
                                                       state-name))
         (cntl-state-name 'major-state)
         (cntl-state-type/default
          (assoc-eq-value cntl-state-name control-template))
         (cntl-state-type/val
          (list (car cntl-state-type/default)
                (list (add-prefix-to-name "V_" state-name))))
         (new-template (update-alist cntl-state-name cntl-state-type/val
                                     control-template))
         (updated-template
          (update-template (cddr state-trans) ;; skip the next-state name
                           new-template)))
      (append `((defun ,cv-name ,control-arglist
                  (declare (xargs :guard (and (true-listp regs-address)
                                              (true-listp i-reg)
                                              (true-listp flags)
                                              (true-listp pc-reg)))
                           (ignorable ,@control-arglist))
                  ,(control-let (build-st updated-template)))

                (defthm ,bvp-cv-name
                  (implies (cv-hyps ,@control-arglist)
                           (bvp (,cv-name ,@control-arglist)))
                  :hints (("Goal" :in-theory (enable bvp binary-or*)))
                  :rule-classes (:rewrite :type-prescription))

                (defthmd ,cv-lemma-name
                  ,(control-let
                    `(implies ,(if (member state-name '(reset0 reset1))
                                   t
                                 `(cv-hyps ,@control-arglist))
                              (and ,@(cv-lemma-concl cv-name
                                                     updated-template
                                                     control-arglist))))
                  :hints (("Goal" :in-theory (enable control-vector-accessors)))))
              (define-control-vector-functions (cdr state-table)
                control-template
                control-arglist)))))

;; ======================================================================

;; The NEXT-STATE module, which takes the current decoded state
;; and creates a decoded version of the next state.

(defun bind-values (sts i l)
  (declare (xargs :guard (natp i)))
  (if (atom sts)
      nil
    (cons `(,(car sts) (nth ,i ,l))
          (bind-values (cdr sts) (1+ i) l))))

(defun id-occs (sts s i)
  (declare (xargs :guard (and (symbolp s)
                              (natp i))))
  (if (atom sts)
      nil
    (cons `(list ',(unstring "R" (str::natstr i))
                 ',(list (car sts))
                 'id
                 (list (si ',s ,i)))
          (id-occs (cdr sts) s (1+ i)))))

(defun b-and-expr (expr)
  (declare (xargs :guard (and (consp expr)
                              (<= (len expr) 5))))
  (case (len expr)
    (1 expr)
    (2 (list (cons 'B-AND expr)))
    (3 (list (cons 'B-AND3 expr)))
    (4 (list (cons 'B-AND4 expr)))
    (5 (list (list 'B-NOT (cons 'B-NAND5 expr))))
    (otherwise nil)))

(defun unwind (tree expr)
  (cond
   ((symbolp tree) (list (cons tree (b-and-expr expr))))
   ((equal (car tree) 'IF)
    (append
     (unwind (caddr tree) (cons (cadr tree) expr))
     (unwind (cadddr tree) (cons `(B-NOT ,(cadr tree)) expr))))
   (t (er hard 'unwind
          "Error when unwinding ~x0."
          tree))))

(defun unwind-next-sts (state-table)
  (if (atom state-table)
      nil
    (b* ((state-trans (car state-table))
         (st (car state-trans))
         (next-st (cadr state-trans)))
      (append (unwind next-st (list st))
              (unwind-next-sts (cdr state-table))))))

(defun collect-from-alist (x alist)
  (cond ((atom alist) nil)
        ((equal x (caar alist))
         (append (cdar alist)
                 (collect-from-alist x (cdr alist))))
        (t (collect-from-alist x (cdr alist)))))

(defun compute-next-sts (sts alist)
  (if (atom sts)
      nil
    (b* ((st (car sts))
         (collection (collect-from-alist st alist))
         (next-st (add-prefix-to-name "NEXT-" st)))
      (cons
       (case (len collection)
         (0 (cons next-st '(nil)))
         (1 (cons next-st collection))
         (2 (list next-st (cons 'B-OR collection)))
         (3 (list next-st (cons 'B-OR3 collection)))
         (4 (list next-st (cons 'B-OR4 collection)))
         (5 (list next-st (list 'B-NOT (cons 'B-NOR5 collection))))
         (6 (list next-st (list 'B-NOT (cons 'B-NOR6 collection))))
         (7 (list next-st (list 'B-NAND
                                (cons 'B-NOR4 (take 4 collection))
                                (cons 'B-NOR3 (nthcdr 4 collection)))))
         (otherwise (er hard 'compute-next-sts
                        "COMPUTE-NEXT-STS error")))
       (compute-next-sts (cdr sts) alist)))))

(defun define-next-state (state-table)
  (b* ((state-names (strip-cars state-table))
       (next-sts (add-prefix-to-names "NEXT-" state-names))
       (unwinded-next-sts (unwind-next-sts state-table))
       (spec (compute-next-sts state-names unwinded-next-sts)))
    `((defun next-state (decoded-state
                         store set-some-flags
                         unary direct-a direct-b
                         side-effect-a side-effect-b
                         all-t-regs-address
                         dtack- hold-)
        (declare (xargs :guard (true-listp decoded-state)))
        (b* ,(append (bind-values state-names 0 'decoded-state)
                     spec)
          (list ,@next-sts)))

      (defun f$next-state (decoded-state
                           store set-some-flags
                           unary direct-a direct-b
                           side-effect-a side-effect-b
                           all-t-regs-address
                           dtack- hold-)
        (declare (xargs :guard (true-listp decoded-state)))
        (b* ,(append (bind-values state-names 0 'decoded-state)
                     (b-to-f spec))
          (list ,@next-sts)))

      (defthm f$next-state=next-state
        (implies (and (bvp decoded-state)
                      (booleanp store) (booleanp set-some-flags)
                      (booleanp unary) (booleanp direct-a)
                      (booleanp direct-b)
                      (booleanp side-effect-a) (booleanp side-effect-b)
                      (booleanp all-t-regs-address)
                      (booleanp dtack-) (booleanp hold-))
                 (equal (f$next-state decoded-state
                                      store set-some-flags
                                      unary direct-a direct-b
                                      side-effect-a side-effect-b
                                      all-t-regs-address
                                      dtack- hold-)
                        (next-state decoded-state
                                    store set-some-flags
                                    unary direct-a direct-b
                                    side-effect-a side-effect-b
                                    all-t-regs-address
                                    dtack- hold-)))
        :hints (("Goal" :in-theory (disable b-gates))))

      (in-theory (disable f$next-state next-state))

      (defun next-state* ()
        (declare (xargs :guard t))
        (list
         'next-state
         (append (sis 's 0 32)
                 '(store set-some-flags
                         unary direct-a direct-b
                         side-effect-a side-effect-b
                         all-t-regs-address
                         dtack- hold-))
         ',next-sts
         ()
         (append (list ,@(id-occs state-names 's 0))
                 ',(fn-to-module-body 0 (flatten-binding 'x 0 spec t)))))

      (defund next-state& (netlist)
        (declare (xargs :guard (alistp netlist)))
        (equal (assoc 'next-state netlist)
               (next-state*)))

      (defun next-state$netlist ()
        (declare (xargs :guard t))
        (list (next-state*)))

      (defthmd next-state$netlist-okp
        (and (net-syntax-okp (next-state$netlist))
             (net-arity-okp (next-state$netlist))))

      )))

;; ======================================================================

(defun id-occs-from-decoded-state (sts i)
  (declare (xargs :guard (and (symbol-listp sts)
                              (natp i))))
  (if (atom sts)
      nil
    (cons `(list ',(unstring "G-" (symbol-name (car sts)))
                 ',(list (car sts))
                 'id
                 (list (si 'DECODED-STATE ,i)))
          (id-occs-from-decoded-state (cdr sts) (1+ i)))))

(defun translate-b-fns (form)
  (if (symbolp form)
      form
    (case (car form)
      (b-and (cons 'AND* (list (translate-b-fns (cadr form))
                               (translate-b-fns (caddr form)))))
      (b-or  (cons 'OR* (list (translate-b-fns (cadr form))
                              (translate-b-fns (caddr form)))))
      (b-not (cons 'NOT* (list (translate-b-fns (cadr form)))))
      (otherwise (er hard 'translate-b-fns
                     "Error in (translate-b-fns ~x0)."
                     form)))))

(defun make-if-tree (tree control-arglist)
  (cond ((symbolp tree) `(,(add-prefix-to-name "CV_" tree)
                          ,@control-arglist))
        ((and (consp tree) (equal (car tree) 'IF))
         `(IF* ,(translate-b-fns (cadr tree))
               ,(make-if-tree (caddr tree) control-arglist)
               ,(make-if-tree (cadddr tree) control-arglist)))
        (t (er hard 'make-if-tree
               "Error in (make-if-tree ~x0)."
               tree))))

;; Write a lemma for the next control-state for each state in terms of the CV
;; functions.

(defun next-cntl-state-lemmas (state-table control-arglist)
  (if (atom state-table)
      nil
    (b* ((state-trans (car state-table))
         (st (car state-trans))
         (v-st (add-prefix-to-name "V_" st))
         (next-st (cadr state-trans)))
      (cons
       `(DEFTHM ,(add-prefix-to-name "NEXT-CNTL-STATE$" st)
          (IMPLIES (AND (EQUAL RESET- T)
                        (CV-HYPS RW- REGS-ADDRESS I-REG FLAGS PC-REG))
                   (EQUAL (NEXT-CNTL-STATE RESET- DTACK- HOLD- RW- (,v-st)
                                           I-REG FLAGS PC-REG REGS-ADDRESS)
                          ,(control-let (make-if-tree next-st
                                                      control-arglist))))
          :HINTS (("GOAL"
                   :IN-THEORY (ENABLE NEXT-CNTL-STATE
                                       NEXT-STATE
                                       CV
                                       BINARY-AND* BINARY-OR*
                                       CV-STATES))))

       (next-cntl-state-lemmas (cdr state-table) control-arglist)))))

(defun generate-next-cntl-state-lemmas (state-table control-arglist)
  `(PROGN ,@(next-cntl-state-lemmas state-table control-arglist)))

;; ======================================================================

(defund bind-signals-to-val (signals val)
  (declare (xargs :guard t))
  (if (atom signals)
      nil
    (cons `(equal ,(car signals) ,val)
          (bind-signals-to-val (cdr signals) val))))

;; This function generates module's state lemmas for each set of values of (GO)
;; SIGNALS. The sets of SIGNALS' values are computed from two variables
;; HIGH-SIGNALS-SET and SIGNALS. Each element of HIGH-SIGNALS-SET is a set of
;; signals that have value T; the other signals not in that set but in SIGNALS
;; will have value NIL.

(define module$state-interleavings-gen (generator
                                        &key
                                        (suffix '"")
                                        (hyps 't)
                                        (signals 'nil)
                                        (high-signals-set 'nil)
                                        (enable 'nil)
                                        (disable 'nil))
  :mode :program
  (if (atom high-signals-set)
      '(progn)
    (b* ((suffix (if (natp suffix) (str::natstr suffix) suffix))
         (new-suffix (concatenate 'string
                                  suffix
                                  "-"
                                  (str::natstr (len high-signals-set))))
         (high-signals (car high-signals-set))
         (low-signals (remove-lst high-signals signals))
         (signals-hyps (append (bind-signals-to-val high-signals t)
                               (bind-signals-to-val low-signals nil)))
         (new-hyps (append hyps signals-hyps)))
      (append (module$state-interleavings-gen
               generator
               :suffix suffix
               :hyps hyps
               :signals signals
               :high-signals-set (cdr high-signals-set)
               :enable enable
               :disable disable)
              `((make-event
                 (,generator
                  state :suffix ,new-suffix
                  :hyps ',new-hyps
                  :enable ',enable :disable ',disable)))))))

;; This macro will call the above function to generate module's state lemmas
;; for all possible sets of values of (GO) SIGNALS (It might exclude the set of
;; all NIL values, depending on the value of variable POWERSETP).

(defmacro module$state-interleavings (generator
                                      powersetp
                                      &key
                                      (suffix '"")
                                      (hyps 't)
                                      (signals 'nil)
                                      (enable 'nil)
                                      (disable 'nil))
  (module$state-interleavings-gen
   generator
   :suffix suffix
   :hyps hyps
   :signals signals
   :high-signals-set (if powersetp
                         (powerset signals)
                       (no-empty-powerset signals))
   :enable enable
   :disable disable))

;; ======================================================================

(defmacro state-fn-n-gen (name &optional data-width)
  (declare (xargs :guard (symbolp name)))
  (b* ((state-fn (intern$ (concatenate 'string
                                       (symbol-name name)
                                       "$STATE-FN")
                          "ADE"))
       (state-fn-n (intern$ (concatenate 'string
                                         (symbol-name name)
                                         "$STATE-FN-N")
                            "ADE"))
       (len-of-state-fn-n (intern$ (concatenate 'string
                                                "LEN-OF-"
                                                (symbol-name name)
                                                "$STATE-FN-N")
                                   "ADE"))
       (st-len-const (intern$ (concatenate 'string
                                           "*"
                                           (symbol-name name)
                                           "$ST-LEN*")
                              "ADE"))
       (open-state-fn-n-zp (intern$ (concatenate 'string
                                                 "OPEN-"
                                                 (symbol-name name)
                                                 "$STATE-FN-N-ZP")
                                    "ADE"))
       (open-state-fn-n (intern$ (concatenate 'string
                                              "OPEN-"
                                              (symbol-name name)
                                              "$STATE-FN-N")
                                 "ADE"))
       (state-fn-m+n (intern$ (concatenate 'string
                                           (symbol-name name)
                                           "$STATE-FN-M+N")
                              "ADE"))
       (inputs-lst 'inputs-lst))
    (if data-width
        `(progn

           (defun ,state-fn-n (,inputs-lst st ,data-width n)
             (if (zp n)
                 st
               (,state-fn-n (cdr ,inputs-lst)
                            (,state-fn (car ,inputs-lst) st ,data-width)
                            ,data-width
                            (1- n))))

           (defthm ,len-of-state-fn-n
             (implies
              (equal (len st) ,st-len-const)
              (equal (len (,state-fn-n ,inputs-lst st ,data-width n))
                     ,st-len-const)))

           (defthm ,open-state-fn-n-zp
             (implies (zp n)
                      (equal (,state-fn-n ,inputs-lst st ,data-width n)
                             st)))

           (defthm ,open-state-fn-n
             (implies
              (not (zp n))
              (equal
               (,state-fn-n ,inputs-lst st ,data-width n)
               (,state-fn-n (cdr ,inputs-lst)
                            (,state-fn (car ,inputs-lst) st ,data-width)
                            ,data-width
                            (1- n)))))

           (defthm ,state-fn-m+n
             (implies
              (and (natp m)
                   (natp n))
              (equal (,state-fn-n ,inputs-lst st ,data-width (+ m n))
                     (,state-fn-n
                      (nthcdr m ,inputs-lst)
                      (,state-fn-n ,inputs-lst st ,data-width m)
                      ,data-width
                      n)))
             :hints (("Goal"
                      :induct (,state-fn-n ,inputs-lst st ,data-width m)))))

      `(progn

         (defun ,state-fn-n (,inputs-lst st n)
           (if (zp n)
               st
             (,state-fn-n (cdr ,inputs-lst)
                          (,state-fn (car ,inputs-lst) st)
                          (1- n))))

         (defthm ,len-of-state-fn-n
           (implies (equal (len st) ,st-len-const)
                    (equal (len (,state-fn-n ,inputs-lst st n))
                           ,st-len-const)))

         (defthm ,open-state-fn-n-zp
           (implies (zp n)
                    (equal (,state-fn-n ,inputs-lst st n)
                           st)))

         (defthm ,open-state-fn-n
           (implies
            (not (zp n))
            (equal (,state-fn-n ,inputs-lst st n)
                   (,state-fn-n (cdr ,inputs-lst)
                                (,state-fn (car ,inputs-lst) st)
                                (1- n)))))

         (defthm ,state-fn-m+n
           (implies (and (natp m)
                         (natp n))
                    (equal (,state-fn-n ,inputs-lst st (+ m n))
                           (,state-fn-n
                            (nthcdr m ,inputs-lst)
                            (,state-fn-n ,inputs-lst st m)
                            n)))
           :hints (("Goal"
                    :induct (,state-fn-n ,inputs-lst st m)))))
      )))

(defmacro input-format-n-gen (name &optional data-width)
  (declare (xargs :guard (symbolp name)))
  (b* ((input-format (intern$ (concatenate 'string
                                           (symbol-name name)
                                           "$INPUT-FORMAT")
                              "ADE"))
       (input-format-n (intern$ (concatenate 'string
                                             (symbol-name name)
                                             "$INPUT-FORMAT-N")
                                "ADE"))
       (open-input-format-n-zp (intern$ (concatenate 'string
                                                     "OPEN-"
                                                     (symbol-name name)
                                                     "$INPUT-FORMAT-N-ZP")
                                        "ADE"))
       (open-input-format-n (intern$ (concatenate 'string
                                                  "OPEN-"
                                                  (symbol-name name)
                                                  "$INPUT-FORMAT-N")
                                     "ADE"))
       (input-format-m+n (intern$ (concatenate 'string
                                               (symbol-name name)
                                               "$INPUT-FORMAT-M+N")
                                  "ADE"))
       (inputs-lst 'inputs-lst))
    (if data-width
        `(progn

           (defun ,input-format-n (,inputs-lst ,data-width n)
             (declare (xargs :guard (and (true-list-listp ,inputs-lst)
                                         (natp ,data-width)
                                         (natp n))
                             :measure (acl2-count n)))
             (if (zp n)
                 t
               (and (,input-format (car ,inputs-lst) ,data-width)
                    (,input-format-n (cdr ,inputs-lst)
                                     ,data-width
                                     (1- n)))))

           (defthm ,open-input-format-n-zp
             (implies (zp n)
                      (equal (,input-format-n ,inputs-lst ,data-width n)
                             t)))

           (defthm ,open-input-format-n
             (implies (not (zp n))
                      (equal (,input-format-n ,inputs-lst ,data-width n)
                             (and (,input-format (car ,inputs-lst)
                                                 ,data-width)
                                  (,input-format-n (cdr ,inputs-lst)
                                                   ,data-width
                                                   (1- n))))))

           (defthm ,input-format-m+n
             (implies
              (and (natp m)
                   (natp n))
              (equal (,input-format-n ,inputs-lst ,data-width (+ m n))
                     (and (,input-format-n ,inputs-lst ,data-width m)
                          (,input-format-n (nthcdr m ,inputs-lst)
                                           ,data-width
                                           n))))
             :hints (("Goal"
                      :induct (,input-format-n ,inputs-lst ,data-width m)))))

      `(progn

         (defun ,input-format-n (,inputs-lst n)
           (declare (xargs :guard (and (true-list-listp ,inputs-lst)
                                       (natp n))))
           (if (zp n)
               t
             (and (,input-format (car ,inputs-lst))
                  (,input-format-n (cdr ,inputs-lst) (1- n)))))

         (defthm ,open-input-format-n-zp
           (implies (zp n)
                    (equal (,input-format-n ,inputs-lst n)
                           t)))

         (defthm ,open-input-format-n
           (implies (not (zp n))
                    (equal (,input-format-n ,inputs-lst n)
                           (and (,input-format (car ,inputs-lst))
                                (,input-format-n (cdr ,inputs-lst)
                                                 (1- n))))))

         (defthm ,input-format-m+n
           (implies (and (natp m)
                         (natp n))
                    (equal (,input-format-n ,inputs-lst (+ m n))
                           (and (,input-format-n ,inputs-lst m)
                                (,input-format-n (nthcdr m ,inputs-lst) n))))))
      )))

(defmacro input-format-n-with-state-gen (name &optional data-width)
  (declare (xargs :guard (symbolp name)))
  (b* ((input-format (intern$ (concatenate 'string
                                           (symbol-name name)
                                           "$INPUT-FORMAT")
                              "ADE"))
       (input-format-n (intern$ (concatenate 'string
                                             (symbol-name name)
                                             "$INPUT-FORMAT-N")
                                "ADE"))
       (open-input-format-n-zp (intern$ (concatenate 'string
                                                     "OPEN-"
                                                     (symbol-name name)
                                                     "$INPUT-FORMAT-N-ZP")
                                        "ADE"))
       (open-input-format-n (intern$ (concatenate 'string
                                                  "OPEN-"
                                                  (symbol-name name)
                                                  "$INPUT-FORMAT-N")
                                     "ADE"))
       (input-format-m+n (intern$ (concatenate 'string
                                               (symbol-name name)
                                               "$INPUT-FORMAT-M+N")
                                  "ADE"))
       (state-fn (intern$ (concatenate 'string
                                       (symbol-name name)
                                       "$STATE-FN")
                          "ADE"))
       (state-fn-n (intern$ (concatenate 'string
                                         (symbol-name name)
                                         "$STATE-FN-N")
                            "ADE"))
       (inputs-lst 'inputs-lst))
    (if data-width
        `(progn

           (defun ,input-format-n (,inputs-lst st ,data-width n)
             (declare (xargs :measure (acl2-count n)))
             (if (zp n)
                 t
               (and (,input-format (car ,inputs-lst) st ,data-width)
                    (,input-format-n
                     (cdr ,inputs-lst)
                     (,state-fn (car ,inputs-lst) st ,data-width)
                     ,data-width
                     (1- n)))))

           (defthm ,open-input-format-n-zp
             (implies
              (zp n)
              (equal (,input-format-n ,inputs-lst st ,data-width n)
                     t)))

           (defthm ,open-input-format-n
             (implies
              (not (zp n))
              (equal (,input-format-n ,inputs-lst st ,data-width n)
                     (and (,input-format (car ,inputs-lst) st ,data-width)
                          (,input-format-n
                           (cdr ,inputs-lst)
                           (,state-fn (car ,inputs-lst) st ,data-width)
                           ,data-width
                           (1- n))))))

           (defthm ,input-format-m+n
             (implies
              (and (natp m)
                   (natp n))
              (equal (,input-format-n ,inputs-lst st ,data-width (+ m n))
                     (and (,input-format-n ,inputs-lst st ,data-width m)
                          (,input-format-n
                           (nthcdr m ,inputs-lst)
                           (,state-fn-n ,inputs-lst st ,data-width m)
                           ,data-width
                           n))))
             :hints
             (("Goal"
               :induct (,input-format-n ,inputs-lst st ,data-width m)))))

      `(progn

         (defun ,input-format-n (,inputs-lst st n)
           (declare (xargs :measure (acl2-count n)))
           (if (zp n)
               t
             (and (,input-format (car ,inputs-lst) st)
                  (,input-format-n (cdr ,inputs-lst)
                                   (,state-fn (car ,inputs-lst) st)
                                   (1- n)))))

         (defthm ,open-input-format-n-zp
           (implies (zp n)
                    (equal (,input-format-n ,inputs-lst st n)
                           t)))

         (defthm ,open-input-format-n
           (implies
            (not (zp n))
            (equal (,input-format-n ,inputs-lst st n)
                   (and (,input-format (car ,inputs-lst) st)
                        (,input-format-n (cdr ,inputs-lst)
                                         (,state-fn (car ,inputs-lst) st)
                                         (1- n))))))

         (defthm ,input-format-m+n
           (implies (and (natp m)
                         (natp n))
                    (equal (,input-format-n ,inputs-lst st (+ m n))
                           (and (,input-format-n ,inputs-lst st m)
                                (,input-format-n
                                 (nthcdr m ,inputs-lst)
                                 (,state-fn-n ,inputs-lst st m)
                                 n))))
           :hints (("Goal"
                    :induct (,input-format-n ,inputs-lst st m)))))
      )))

;; Proving the correspondence between simulating a DE module and its
;; "hardware" run function.

(defmacro simulate-lemma (name &key (complex-link 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (booleanp complex-link))))
  (b* ((recognizer (unstring (symbol-name name)
                             "&"))
       (state-fn (unstring (symbol-name name)
                           "$STATE-FN"))
       (state-fn-n (unstring (symbol-name name)
                             "$STATE-FN-N"))
       (state-lemma (unstring (symbol-name name)
                              "$STATE"))
       (input-format (unstring (symbol-name name)
                               "$INPUT-FORMAT"))
       (input-format-n (unstring (symbol-name name)
                                 "$INPUT-FORMAT-N"))
       (st-format (unstring (symbol-name name)
                            "$ST-FORMAT"))
       (st-format-preserved (unstring (symbol-name name)
                                      "$ST-FORMAT-PRESERVED"))
       (state-alt (unstring (symbol-name name)
                            "$STATE-ALT"))
       (simulate (unstring (symbol-name name)
                           "$DE-SIM-N")))
    `(progn
       (defthm ,st-format-preserved
         (implies (,st-format st data-width)
                  (,st-format (,state-fn inputs st data-width)
                              data-width))
         :hints (("Goal"
                  :in-theory (enable get-field
                                     ,state-fn
                                     ,st-format))))

       (defthmd ,state-alt
         (implies (and (,recognizer netlist data-width)
                       ,(if complex-link
                            `(,input-format inputs st data-width)
                          `(,input-format inputs data-width))
                       (,st-format st data-width))
                  (equal (de (si ',name data-width) inputs st netlist)
                         (,state-fn inputs st data-width)))
         :hints (("Goal"
                  :in-theory (enable ,input-format
                                     ,state-lemma))))

       (state-fn-n-gen ,name data-width)
       ,(if complex-link
           `(input-format-n-with-state-gen ,name data-width)
         `(input-format-n-gen ,name data-width))

       (defthmd ,simulate
         (implies (and (,recognizer netlist data-width)
                       ,(if complex-link
                            `(,input-format-n inputs-lst st data-width n)
                          `(,input-format-n inputs-lst data-width n))
                       (,st-format st data-width))
                  (equal (de-sim-n (si ',name data-width)
                                   inputs-lst st netlist
                                   n)
                         (,state-fn-n inputs-lst st data-width n)))
         :hints (("Goal" :in-theory (enable ,state-alt)))))))

;; Formalizing the relationship between input and output sequences

(defmacro in-out-stream-lemma (name &key
                                    (op 'nil)
                                    (inv 'nil)
                                    (complex-link 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (booleanp op)
                              (booleanp inv)
                              (booleanp complex-link))))
  (b* ((extract-state (unstring (symbol-name name)
                                "$EXTRACT-STATE"))
       (step-spec (unstring (symbol-name name)
                            "$STEP-SPEC"))
       (state-fn-n (unstring (symbol-name name)
                             "$STATE-FN-N"))
       (input-format-n (unstring (symbol-name name)
                                 "$INPUT-FORMAT-N"))
       (valid-st (unstring (symbol-name name)
                           "$VALID-ST"))
       (st-inv (unstring (symbol-name name)
                         "$INV"))
       (in-seq (unstring (symbol-name name)
                         "$IN-SEQ"))
       (out-seq (unstring (symbol-name name)
                          "$OUT-SEQ"))
       (op-seq (unstring (symbol-name name)
                         "$OP-SEQ"))
       (seq (if op
                `(,op-seq seq)
              `(,in-seq inputs-lst st data-width n)))
       (hyps (if inv
                 `(and ,(if complex-link
                            `(,input-format-n inputs-lst st data-width n)
                          `(,input-format-n inputs-lst data-width n))
                       (,valid-st st data-width)
                       (,st-inv st))
               `(and ,(if complex-link
                          `(,input-format-n inputs-lst st data-width n)
                        `(,input-format-n inputs-lst data-width n))
                     (,valid-st st data-width))))
       (concl (if op
                  `(equal (append final-extracted-st
                                  (,out-seq inputs-lst st data-width n))
                          (append (,op-seq
                                   (,in-seq inputs-lst st data-width n))
                                  extracted-st))
                `(equal (append final-extracted-st
                                (,out-seq inputs-lst st data-width n))
                        (append (,in-seq inputs-lst st data-width n)
                                extracted-st))))
       (dataflow-correct-aux (unstring (symbol-name name)
                                       "$DATAFLOW-CORRECT-AUX"))
       (dataflow-correct (unstring (symbol-name name)
                                   "$DATAFLOW-CORRECT")))
    `(encapsulate
       ()

       (local
        (defthm ,dataflow-correct-aux
          (implies (equal (append x y1)
                          (append ,seq y2))
                   (equal (append x y1 z)
                          (append ,seq y2 z)))
          :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                          (acl2::associativity-of-append))))))

       (defthmd ,dataflow-correct
         (b* ((extracted-st (,extract-state st))
              (final-st (,state-fn-n inputs-lst st data-width n))
              (final-extracted-st (,extract-state final-st)))
           (implies ,hyps ,concl))
         :hints (("Goal" :in-theory (enable ,step-spec)))))))

;; ST-TRANS-FN generates (1) condition functions on GO signals' values based on
;; their interleavings, and (2) functions that counts the number of DE steps to
;; be executed corresponding to each interleaving of GO signals.

(defun idx->car-cdr (n l)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      `(car ,l)
    (idx->car-cdr (1- n) `(cdr ,l))))

(defun go-gen1 (signals x flag)
  (declare (xargs :guard t))
  (cond ((not signals) nil)
        ((atom signals)
         `((equal (,signals ,x) ,flag)))
        (t (cons `(equal (,(car signals) ,x) ,flag)
                 (go-gen1 (cdr signals) x flag)))))

(defun remove-lst-lst (x y)
  (declare (xargs :guard (true-list-listp y)))
  (if (atom y)
      nil
    (cons (remove-lst x (car y))
          (remove-lst-lst x (cdr y)))))

(defun remove-len-<-2 (l)
  (declare (xargs :guard t))
  (if (atom l)
      nil
    (if (< (len (car l)) 2)
        (remove-len-<-2 (cdr l))
      (cons (car l) (remove-len-<-2 (cdr l))))))

(defun go-gen (n x l independ-lst)
  (declare (xargs :guard (and (natp n)
                              (true-list-listp independ-lst))))
  (if (atom l)
      nil
    (b* ((removed-lst (if (atom (car l))
                          (list (car l))
                        (car l)))
         (independs (remove-lst removed-lst (car independ-lst)))
         (new-independ-lst
          (remove-len-<-2 (remove-lst-lst removed-lst independ-lst))))
      (append (go-gen1 (car l) (idx->car-cdr n x) t)
              (if (and (consp independs)
                       (< (len independs) (len (car independ-lst))))
                  (go-gen1 independs (idx->car-cdr n x) nil)
                nil)
              (go-gen (1+ n) x (cdr l) new-independ-lst)))))

(defun st-trans-gen (name st-trans-rules n x l independ-lst)
  (declare (xargs :guard (and (symbolp name)
                              (natp n)
                              (true-list-listp independ-lst))))
  (if (atom l)
      nil
    (b* ((st-trans (intern$ (concatenate 'string
                                         (symbol-name name)
                                         "$ST-TRANS-"
                                         (str::natstr n))
                            "ADE"))
         (st-trans->numsteps (intern$ (concatenate 'string
                                                   "*"
                                                   (symbol-name name)
                                                   "$ST-TRANS-"
                                                   (str::natstr n)
                                                   "->NUMSTEPS*")
                                      "ADE")))
      (append
       `((defund ,st-trans (,x)
           (declare (xargs :guard (true-list-listp ,x)))
           (and ,@(go-gen 0 x (car l) independ-lst)))

         (add-to-ruleset ,st-trans-rules '(,st-trans))

         (defconst ,st-trans->numsteps ,(len (car l))))

       (st-trans-gen name st-trans-rules (1+ n) x (cdr l) independ-lst)))))

(defun st-trans-lst (name n x)
  (declare (xargs :guard (and (symbolp name)
                              (natp n))))
  (if (zp n)
      nil
    (b* ((st-trans (intern$ (concatenate 'string
                                         (symbol-name name)
                                         "$ST-TRANS-"
                                         (str::natstr (1- n)))
                            "ADE")))
      (cons `(,st-trans ,x)
            (st-trans-lst name (1- n) x)))))

(defun st-trans->numsteps-lst (name n x)
  (declare (xargs :guard (and (symbolp name)
                              (natp n))))
  (if (zp n)
      nil
    (b* ((st-trans (intern$ (concatenate 'string
                                         (symbol-name name)
                                         "$ST-TRANS-"
                                         (str::natstr (1- n)))
                            "ADE"))
         (st-trans->numsteps (intern$ (concatenate 'string
                                                   "*"
                                                   (symbol-name name)
                                                   "$ST-TRANS-"
                                                   (str::natstr (1- n))
                                                   "->NUMSTEPS*")
                                      "ADE")))
      (cons `((,st-trans ,x) ,st-trans->numsteps)
            (st-trans->numsteps-lst name (1- n) x)))))

(defun st-trans-fn (name interleavings independ-lst)
  (declare (xargs :guard (and (symbolp name)
                              (true-list-listp independ-lst))))
  (b* ((st-trans (intern$ (concatenate 'string
                                       (symbol-name name)
                                       "$ST-TRANS")
                          "ADE"))
       (st-trans-n (intern$ (concatenate 'string
                                         (symbol-name name)
                                         "$ST-TRANS-N")
                            "ADE"))
       (open-st-trans-n-zp (intern$ (concatenate 'string
                                                 "OPEN-"
                                                 (symbol-name name)
                                                 "$ST-TRANS-N-ZP")
                                    "ADE"))
       (open-st-trans-n (intern$ (concatenate 'string
                                              "OPEN-"
                                              (symbol-name name)
                                              "$ST-TRANS-N")
                                 "ADE"))
       (st-trans-m+n (intern$ (concatenate 'string
                                           (symbol-name name)
                                           "$ST-TRANS-M+N")
                              "ADE"))
       (st-trans->numsteps (intern$ (concatenate 'string
                                                 (symbol-name name)
                                                 "$ST-TRANS->NUMSTEPS")
                                    "ADE"))
       (st-trans-n->numsteps (intern$ (concatenate 'string
                                                   (symbol-name name)
                                                   "$ST-TRANS-N->NUMSTEPS")
                                      "ADE"))
       (open-st-trans-n->numsteps-zp
        (intern$ (concatenate 'string
                              "OPEN-"
                              (symbol-name name)
                              "$ST-TRANS-N->NUMSTEPS-ZP")
                 "ADE"))
       (open-st-trans-n->numsteps
        (intern$ (concatenate 'string
                              "OPEN-"
                              (symbol-name name)
                              "$ST-TRANS-N->NUMSTEPS")
                 "ADE"))
       (st-trans-n->numsteps-plus
        (intern$ (concatenate 'string
                              (symbol-name name)
                              "$ST-TRANS-N->NUMSTEPS-PLUS")
                 "ADE"))
       (st-trans-rules (intern$ (concatenate 'string
                                             (symbol-name name)
                                             "$ST-TRANS-RULES")
                                "ADE"))
       (inputs-lst 'inputs-lst))
    `(progn

       (def-ruleset ,st-trans-rules
         '())

       ,@(st-trans-gen name st-trans-rules
                       0 inputs-lst interleavings independ-lst)

       (defund ,st-trans (,inputs-lst)
         (declare (xargs :guard (true-list-listp ,inputs-lst)))
         (or ,@(rev
                (st-trans-lst name (len interleavings) inputs-lst))))

       (defund ,st-trans->numsteps (,inputs-lst)
         (declare (xargs :guard (true-list-listp ,inputs-lst)))
         (cond
          ,@(rev
             (st-trans->numsteps-lst name (len interleavings)
                                     inputs-lst))
          (t 0)))

       (add-to-ruleset ,st-trans-rules '(,st-trans
                                         ,st-trans->numsteps))

       (defun ,st-trans-n (,inputs-lst n)
         (declare (xargs :measure (acl2-count n)
                         :guard (and (true-list-listp ,inputs-lst)
                                     (natp n))))
         (if (zp n)
             t
           (and (,st-trans ,inputs-lst)
                (,st-trans-n
                 (nthcdr (,st-trans->numsteps ,inputs-lst) ,inputs-lst)
                 (1- n)))))

       (defthm ,open-st-trans-n-zp
         (implies (zp n)
                  (equal (,st-trans-n ,inputs-lst n) t)))

       (defthm ,open-st-trans-n
         (implies (not (zp n))
                  (equal (,st-trans-n ,inputs-lst n)
                         (and (,st-trans ,inputs-lst)
                              (,st-trans-n
                               (nthcdr (,st-trans->numsteps ,inputs-lst)
                                       ,inputs-lst)
                               (1- n))))))

       (defun ,st-trans-n->numsteps (,inputs-lst n)
         (declare (xargs :guard (and (true-list-listp ,inputs-lst)
                                     (natp n))))
         (if (zp n)
             0
           (b* ((numsteps (,st-trans->numsteps ,inputs-lst)))
             (+ numsteps
                (,st-trans-n->numsteps (nthcdr numsteps ,inputs-lst)
                                       (1- n))))))

       (defthm ,open-st-trans-n->numsteps-zp
         (implies (zp n)
                  (equal (,st-trans-n->numsteps ,inputs-lst n) 0)))

       (defthm ,open-st-trans-n->numsteps
         (implies (not (zp n))
                  (equal (,st-trans-n->numsteps ,inputs-lst n)
                         (b* ((numsteps (,st-trans->numsteps ,inputs-lst)))
                           (+ numsteps
                              (,st-trans-n->numsteps
                               (nthcdr numsteps ,inputs-lst)
                               (1- n)))))))

       (defthm ,st-trans-m+n
         (implies (and (natp m)
                       (natp n))
                  (equal (,st-trans-n ,inputs-lst (+ m n))
                         (and (,st-trans-n ,inputs-lst m)
                              (,st-trans-n
                               (nthcdr (,st-trans-n->numsteps ,inputs-lst m)
                                       ,inputs-lst)
                               n)))))

       (defthm ,st-trans-n->numsteps-plus
         (implies (and (natp m)
                       (natp n))
                  (equal (,st-trans-n->numsteps ,inputs-lst (+ m n))
                         (+ (,st-trans-n->numsteps ,inputs-lst m)
                            (,st-trans-n->numsteps
                             (nthcdr (,st-trans-n->numsteps ,inputs-lst m)
                                     ,inputs-lst)
                             n)))))

       (in-theory (disable ,st-trans-n
                           ,st-trans-n->numsteps))
       )))
