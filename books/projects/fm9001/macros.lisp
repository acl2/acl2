;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "assoc-eq-value")
(include-book "hard-spec")

;; ======================================================================

(defun unstring (str1 str2)
  (declare (xargs :guard (and (stringp str1) (stringp str2))))
  (intern$ (string-append str1 str2) "FM9001"))

(defun var-to-const (x)
  (declare (xargs :guard (symbolp x)))
  (intern$ (concatenate 'string "*" (symbol-name x) "*")
           "FM9001"))

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
                                   "FM9001"))
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
         :hints (("Goal" :in-theory (enable se-rules ,netlist-properp))))

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

;; ======================================================================

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

;; ======================================================================

;; Define both vector (V_) and natural (N_) forms of the states.

(defun add-prefix-to-name (prefix name)
  (declare (xargs :guard (and (stringp prefix)
                              (symbolp name))))
  (intern$ (string-append prefix (symbol-name name))
           "FM9001"))

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
         (vn (intern$ vector-state-name "FM9001"))
         (nn (intern$ natural-state-name "FM9001"))
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
          "FM9001"))

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


