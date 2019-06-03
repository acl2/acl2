;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "misc/defopener" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; ======================================================================

(defmacro strings-to-symbol (&rest strs)
  `(intern$ (concatenate 'string ,@strs)
            "ADE"))

(defun var-to-const (x)
  (declare (xargs :guard (symbolp x)))
  (intern$ (concatenate 'string "*" (symbol-name x) "*")
           "ADE"))

(defun state-accessors-gen (module st idx)
  (declare (xargs :guard (and (symbolp module)
                              (symbol-listp st)
                              (natp idx))))
  (if (atom st)
      nil
    (b* ((sub-st (car st))
         (name (strings-to-symbol "*"
                                  (symbol-name module)
                                  "$"
                                  (symbol-name sub-st)
                                  "*")))
      (cons `(defconst ,name ,idx)
            (state-accessors-gen module (cdr st) (1+ idx))))))

(defmacro not-primp-lemma (fn)
  (b* ((thm-name (strings-to-symbol "NOT-PRIMP-" (symbol-name fn))))
    `(local
      (defthm ,thm-name
        (not (primp (si ',fn n)))
        :hints (("Goal" :in-theory (enable primp)))))))

;; ======================================================================

;; DESTRUCTURING-LEMMA generator

;; Because of quirks in equality reasoning, it "doesn't work" to simply let
;; module definitions open up.  Instead, we use a lemma that explicitly states
;; how to destructure a module definition.

(defmacro destructuring-lemma (fn args declare-form bindings
                                  name ins outs st occs)
  (b* ((destructure (strings-to-symbol (symbol-name fn) "$DESTRUCTURE"))
       (prefix-name (strings-to-symbol
                     (coerce (butlast (coerce (symbol-name fn) 'list)
                                      1)
                             'string)))
       (form `(,fn ,@args)))

    `(progn
       (defun ,fn ,args
         ,declare-form
         (let ,bindings
           (list ,name ,ins ,outs ,st ,occs)))

       (defthmd ,destructure
         (let ,bindings
           (AND
            (EQUAL (CAR ,form) ,name)
            (EQUAL (CADR ,form) ,ins)
            (EQUAL (CADDR ,form) ,outs)
            (EQUAL (CADDDR ,form) ,st)
            (EQUAL (CAR (CDDDDR ,form)) ,occs))))

       ;; Prove that this module is not a DE primitive.

       (not-primp-lemma ,prefix-name)

       (in-theory (disable ,fn)))))

;; MODULE-GENERATOR generator args name inputs outputs body state.

(defmacro module-generator (generator args name inputs outputs st body
                                      &optional declare-form)
  (let ((destructuring-lemma (strings-to-symbol (symbol-name generator)
                                                "$DESTRUCTURE"))
        (prefix-name (strings-to-symbol
                      (coerce (butlast (coerce (symbol-name generator) 'list)
                                       1)
                              'string)))
        (form `(,generator ,@args)))

    `(progn
       (defun ,generator ,args
         ,declare-form
         (LIST ,name ,inputs ,outputs ,st ,body))

       (defthmd ,destructuring-lemma
         (AND
          (EQUAL (CAR ,form) ,name)
          (EQUAL (CADR ,form) ,inputs)
          (EQUAL (CADDR ,form) ,outputs)
          (EQUAL (CADDDR ,form) ,st)
          (EQUAL (CAR (CDDDDR ,form)) ,body)))

       ;; Prove that this module is not a DE primitive.

       (not-primp-lemma ,prefix-name)

       (in-theory (disable ,generator)))))

;; Generating value or state lemmas for primitives

(defun primitives-lemmas-gen (eval primitives)
  ;; @eval is either 'se (for value lemmas) or 'de (for state lemmas)
  (if (atom primitives)
      nil
    (b* ((prim (car primitives))
         (fn (car prim))
         (expr (cadr prim))
         (value/state (if (equal eval 'se) "$VALUE" "$STATE"))
         (thm-name (strings-to-symbol (symbol-name fn) value/state))
         (eval-primp-apply (strings-to-symbol (symbol-name eval)
                                              "-PRIMP-APPLY")))
      (cons `(defthm ,thm-name
               (equal (,eval ',fn ins st netlist)
                      ,expr)
               :hints (("Goal" :in-theory (enable ,eval-primp-apply))))
            (primitives-lemmas-gen eval (cdr primitives))))))

;; ======================================================================

(define outputs/step-gen (state name
                                &key
                                (type ''outputs)
                                (inputs '())
                                (input-signals '())
                                (hyps 't)
                                (enable 'nil)
                                (disable 'nil))
  :mode :program
  (b* ((fn-name (strings-to-symbol (symbol-name name)
                                   (if (equal type 'outputs)
                                       "$OUTPUTS-GEN"
                                     "$STEP")))
       ;; (lemma-name (strings-to-symbol (symbol-name name)
       ;;                                (if (equal type 'value)
       ;;                                    "$VALUE"
       ;;                                  "$STATE")))
       (recognizer (strings-to-symbol (symbol-name name)
                                      "&"))
       (destructure (strings-to-symbol (symbol-name name)
                                       "*$DESTRUCTURE"))
       (eval (if (equal type 'outputs) 'se 'de))
       (hints
        `(("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (,eval (si ',name data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            ,recognizer
                            ,destructure
                            ,@enable)
                           (de-module-disabled-rules
                            ,@disable)))))
       ((mv & lemma state)
        (bash-fn `(b* ((inputs ,inputs))
                    (implies ,hyps
                             (equal (,eval (si ',name data-size)
                                           inputs st netlist)
                                    ?)))
                 hints nil 'bash state))
       (fn-body (cadr (caddar lemma))))
    (mv nil
        `(defun ,fn-name (inputs st data-size)
             (b* ,input-signals
               ,fn-body))
        ;; `(progn
        ;;    (defun ,fn-name (inputs st data-size)
        ;;      (b* ,input-signals
        ;;        ,fn-body))

        ;;    (defthm ,lemma-name
        ;;      (b* ((inputs ,inputs))
        ;;        (implies ,hyps
        ;;                 (equal (,eval (si ',name data-size)
        ;;                               inputs st netlist)
        ;;                        (,fn-name inputs st data-size))))
        ;;      :hints ,hints)

        ;;    (in-theory (disable ,fn-name))
        ;;    )
        state)))

(defmacro run-gen (name &rest sizes)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp sizes))))
  (b* ((step (strings-to-symbol (symbol-name name)
                                "$STEP"))
       (run (strings-to-symbol (symbol-name name)
                               "$RUN"))
       (open-run-zp (strings-to-symbol "OPEN-"
                                       (symbol-name name)
                                       "$RUN-ZP"))
       (open-run (strings-to-symbol "OPEN-"
                                    (symbol-name name)
                                    "$RUN"))
       (run-plus (strings-to-symbol (symbol-name name)
                                   "$RUN-PLUS"))
       (inputs-seq 'inputs-seq))
    (if sizes
        `(progn

           (defun ,run (,inputs-seq st ,@sizes n)
             (if (zp n)
                 st
               (,run (cdr ,inputs-seq)
                     (,step (car ,inputs-seq) st ,@sizes)
                     ,@sizes
                     (1- n))))

           (defopener ,open-run-zp
             (,run ,inputs-seq st ,@sizes n)
             :hyp (zp n)
             :hints (("Goal"
                      :in-theory (theory 'minimal-theory)
                      :expand (,run ,inputs-seq st ,@sizes n))))

           (defopener ,open-run
             (,run ,inputs-seq st ,@sizes n)
             :hyp (not (zp n))
             :hints (("Goal"
                      :in-theory (theory 'minimal-theory)
                      :expand (,run ,inputs-seq st ,@sizes n))))

           (defthm ,run-plus
             (implies
              (and (natp m)
                   (natp n))
              (equal (,run ,inputs-seq st ,@sizes (+ m n))
                     (,run
                      (nthcdr m ,inputs-seq)
                      (,run ,inputs-seq st ,@sizes m)
                      ,@sizes
                      n)))
             :hints (("Goal"
                      :induct (,run ,inputs-seq st ,@sizes m))))

           (in-theory (disable ,run)))

      `(progn

         (defun ,run (,inputs-seq st n)
           (if (zp n)
               st
             (,run (cdr ,inputs-seq)
                   (,step (car ,inputs-seq) st)
                   (1- n))))

         (defopener ,open-run-zp
           (,run ,inputs-seq st n)
           :hyp (zp n)
           :hints (("Goal"
                    :in-theory (theory 'minimal-theory)
                    :expand (,run ,inputs-seq st n))))

         (defopener ,open-run
           (,run ,inputs-seq st n)
           :hyp (not (zp n))
           :hints (("Goal"
                    :in-theory (theory 'minimal-theory)
                    :expand (,run ,inputs-seq st n))))

         (defthm ,run-plus
           (implies (and (natp m)
                         (natp n))
                    (equal (,run ,inputs-seq st (+ m n))
                           (,run
                            (nthcdr m ,inputs-seq)
                            (,run ,inputs-seq st m)
                            n)))
           :hints (("Goal"
                    :induct (,run ,inputs-seq st m))))

         (in-theory (disable ,run)))
      )))

(defmacro input-format-n-gen (name &optional data-size)
  (declare (xargs :guard (symbolp name)))
  (b* ((input-format (strings-to-symbol (symbol-name name)
                                        "$INPUT-FORMAT"))
       (input-format-n (strings-to-symbol (symbol-name name)
                                          "$INPUT-FORMAT-N"))
       (open-input-format-n-zp (strings-to-symbol "OPEN-"
                                                  (symbol-name name)
                                                  "$INPUT-FORMAT-N-ZP"))
       (open-input-format-n (strings-to-symbol "OPEN-"
                                               (symbol-name name)
                                               "$INPUT-FORMAT-N"))
       (input-format-plus (strings-to-symbol (symbol-name name)
                                            "$INPUT-FORMAT-PLUS"))
       (inputs-seq 'inputs-seq))
    (if data-size
        `(progn

           (defun ,input-format-n (,inputs-seq ,data-size n)
             (declare (xargs :guard (and (true-list-listp ,inputs-seq)
                                         (natp ,data-size)
                                         (natp n))
                             :measure (acl2-count n)))
             (if (zp n)
                 t
               (and (,input-format (car ,inputs-seq) ,data-size)
                    (,input-format-n (cdr ,inputs-seq)
                                     ,data-size
                                     (1- n)))))

           (defopener ,open-input-format-n-zp
             (,input-format-n ,inputs-seq ,data-size n)
             :hyp (zp n)
             :hints (("Goal"
                      :in-theory (theory 'minimal-theory)
                      :expand (,input-format-n ,inputs-seq ,data-size n))))

           (defopener ,open-input-format-n
             (,input-format-n ,inputs-seq ,data-size n)
             :hyp (not (zp n))
             :hints (("Goal"
                      :in-theory (theory 'minimal-theory)
                      :expand (,input-format-n ,inputs-seq ,data-size n))))

           (defthm ,input-format-plus
             (implies
              (and (natp m)
                   (natp n))
              (equal (,input-format-n ,inputs-seq ,data-size (+ m n))
                     (and (,input-format-n ,inputs-seq ,data-size m)
                          (,input-format-n (nthcdr m ,inputs-seq)
                                           ,data-size
                                           n))))
             :hints (("Goal"
                      :induct (,input-format-n ,inputs-seq ,data-size m))))

           (in-theory (disable ,input-format-n)))

      `(progn

         (defun ,input-format-n (,inputs-seq n)
           (declare (xargs :guard (and (true-list-listp ,inputs-seq)
                                       (natp n))))
           (if (zp n)
               t
             (and (,input-format (car ,inputs-seq))
                  (,input-format-n (cdr ,inputs-seq) (1- n)))))

         (defopener ,open-input-format-n-zp
           (,input-format-n ,inputs-seq n)
           :hyp (zp n)
           :hints (("Goal"
                    :in-theory (theory 'minimal-theory)
                    :expand (,input-format-n ,inputs-seq n))))

         (defopener ,open-input-format-n
           (,input-format-n ,inputs-seq n)
           :hyp (not (zp n))
           :hints (("Goal"
                    :in-theory (theory 'minimal-theory)
                    :expand (,input-format-n ,inputs-seq n))))

         (defthm ,input-format-plus
           (implies (and (natp m)
                         (natp n))
                    (equal (,input-format-n ,inputs-seq (+ m n))
                           (and (,input-format-n ,inputs-seq m)
                                (,input-format-n (nthcdr m ,inputs-seq) n)))))

         (in-theory (disable ,input-format-n)))
      )))

(defmacro input-format-n-with-state-gen (name &optional data-size)
  (declare (xargs :guard (symbolp name)))
  (b* ((input-format (strings-to-symbol (symbol-name name)
                                            "$INPUT-FORMAT"))
       (input-format-n (strings-to-symbol (symbol-name name)
                                              "$INPUT-FORMAT-N"))
       (open-input-format-n-zp (strings-to-symbol "OPEN-"
                                                      (symbol-name name)
                                                      "$INPUT-FORMAT-N-ZP"))
       (open-input-format-n (strings-to-symbol "OPEN-"
                                                   (symbol-name name)
                                                   "$INPUT-FORMAT-N"))
       (input-format-plus (strings-to-symbol (symbol-name name)
                                                 "$INPUT-FORMAT-PLUS"))
       (step (strings-to-symbol (symbol-name name)
                                "$STEP"))
       (run (strings-to-symbol (symbol-name name)
                               "$RUN"))
       (inputs-seq 'inputs-seq))
    (if data-size
        `(progn

           (defun ,input-format-n (,inputs-seq st ,data-size n)
             (declare (xargs :measure (acl2-count n)))
             (if (zp n)
                 t
               (and (,input-format (car ,inputs-seq) st ,data-size)
                    (,input-format-n
                     (cdr ,inputs-seq)
                     (,step (car ,inputs-seq) st ,data-size)
                     ,data-size
                     (1- n)))))

           (defopener ,open-input-format-n-zp
             (,input-format-n ,inputs-seq st ,data-size n)
             :hyp (zp n)
             :hints (("Goal"
                      :in-theory (theory 'minimal-theory)
                      :expand (,input-format-n ,inputs-seq st ,data-size n))))

           (defopener ,open-input-format-n
             (,input-format-n ,inputs-seq st ,data-size n)
             :hyp (not (zp n))
             :hints (("Goal"
                      :in-theory (theory 'minimal-theory)
                      :expand (,input-format-n ,inputs-seq st ,data-size n))))

           (defthm ,input-format-plus
             (implies
              (and (natp m)
                   (natp n))
              (equal (,input-format-n ,inputs-seq st ,data-size (+ m n))
                     (and (,input-format-n ,inputs-seq st ,data-size m)
                          (,input-format-n
                           (nthcdr m ,inputs-seq)
                           (,run ,inputs-seq st ,data-size m)
                           ,data-size
                           n))))
             :hints
             (("Goal"
               :induct (,input-format-n ,inputs-seq st ,data-size m))))

           (in-theory (disable ,input-format-n)))

      `(progn

         (defun ,input-format-n (,inputs-seq st n)
           (declare (xargs :measure (acl2-count n)))
           (if (zp n)
               t
             (and (,input-format (car ,inputs-seq) st)
                  (,input-format-n (cdr ,inputs-seq)
                                       (,step (car ,inputs-seq) st)
                                       (1- n)))))

         (defopener ,open-input-format-n-zp
           (,input-format-n ,inputs-seq st n)
           :hyp (zp n)
           :hints (("Goal"
                    :in-theory (theory 'minimal-theory)
                    :expand (,input-format-n ,inputs-seq st n))))

         (defopener ,open-input-format-n
           (,input-format-n ,inputs-seq st n)
           :hyp (not (zp n))
           :hints (("Goal"
                    :in-theory (theory 'minimal-theory)
                    :expand (,input-format-n ,inputs-seq st n))))

         (defthm ,input-format-plus
           (implies (and (natp m)
                         (natp n))
                    (equal (,input-format-n ,inputs-seq st (+ m n))
                           (and (,input-format-n ,inputs-seq st m)
                                (,input-format-n
                                 (nthcdr m ,inputs-seq)
                                 (,run ,inputs-seq st m)
                                 n))))
           :hints (("Goal"
                    :induct (,input-format-n ,inputs-seq st m))))

         (in-theory (disable ,input-format-n)))
      )))

;; Proving the correspondence between simulating a DE module and its
;; "hardware" run function.

(defmacro simulate-lemma (name  &key
                               (sizes '(data-size))
                               (clink 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp sizes)
                              (booleanp clink))))
  (b* ((recognizer (strings-to-symbol (symbol-name name)
                                      "&"))
       (outputs (strings-to-symbol (symbol-name name)
                                "$OUTPUTS"))
       (step (strings-to-symbol (symbol-name name)
                                "$STEP"))
       (run (strings-to-symbol (symbol-name name)
                               "$RUN"))
       (input-format (strings-to-symbol (symbol-name name)
                                        "$INPUT-FORMAT"))
       (input-format-n (strings-to-symbol (symbol-name name)
                                          "$INPUT-FORMAT-N"))
       (st-format (strings-to-symbol (symbol-name name)
                                     "$ST-FORMAT"))
       (st-format-preserved (strings-to-symbol (symbol-name name)
                                               "$ST-FORMAT-PRESERVED"))
       (value-alt (strings-to-symbol (symbol-name name)
                                     "$VALUE-ALT"))
       (state-alt (strings-to-symbol (symbol-name name)
                                     "$STATE-ALT"))
       (simulate (strings-to-symbol (symbol-name name)
                                    "$DE-N")))
    `(progn
       (defthm ,st-format-preserved
         (implies (,st-format st ,@sizes)
                  (,st-format (,step inputs st ,@sizes)
                              ,@sizes))
         :hints (("Goal"
                  :in-theory (enable ,step
                                     ,st-format))))

       (defthmd ,value-alt
         (implies (and (,recognizer netlist ,@sizes)
                       ,(if clink
                            `(,input-format inputs st ,(car sizes))
                          `(,input-format inputs ,(car sizes)))
                       (,st-format st ,@sizes))
                  (equal (se (si ',name ,(car sizes)) inputs st netlist)
                         (,outputs inputs st ,(car sizes))))
         :hints (("Goal"
                  :in-theory (enable ,input-format))))

       (defthmd ,state-alt
         (implies (and (,recognizer netlist ,@sizes)
                       ,(if clink
                            `(,input-format inputs st ,(car sizes))
                          `(,input-format inputs ,(car sizes)))
                       (,st-format st ,@sizes))
                  (equal (de (si ',name ,(car sizes)) inputs st netlist)
                         (,step inputs st ,@sizes)))
         :hints (("Goal"
                  :in-theory (enable ,input-format))))

       (run-gen ,name ,@sizes)
       ,(if clink
            `(input-format-n-with-state-gen ,name ,(car sizes))
          `(input-format-n-gen ,name ,(car sizes)))

       (defthmd ,simulate
         (implies (and (,recognizer netlist ,@sizes)
                       ,(if clink
                            `(,input-format-n inputs-seq st ,(car sizes) n)
                          `(,input-format-n inputs-seq ,(car sizes) n))
                       (,st-format st ,@sizes))
                  (equal (de-n (si ',name ,(car sizes))
                               inputs-seq st netlist
                               n)
                         (,run inputs-seq st ,@sizes n)))
         :hints (("Goal" :in-theory (enable ,run ,state-alt)))))))

;; Data sequence generator

(defmacro seq-gen (name in-out act-name act-idx data
                        &key
                        (sizes '(data-size))
                        (netlist-data 'nil)
                        (clink 'nil)
                        (partial-clink 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp in-out)
                              (symbolp act-name)
                              (integerp act-idx)
                              (symbol-listp sizes)
                              (booleanp clink)
                              (booleanp partial-clink))))
  (b* ((recognizer (strings-to-symbol (symbol-name name)
                                      "&"))
       (input-format-n (strings-to-symbol (symbol-name name)
                                          "$INPUT-FORMAT-N"))
       (st-format (strings-to-symbol (symbol-name name)
                                     "$ST-FORMAT"))
       (act-fn (strings-to-symbol (symbol-name name)
                                  "$"
                                  (symbol-name act-name)))
       (act (if clink
                `(,act-fn inputs)
              `(,act-fn inputs st ,(car sizes))))
       (step (strings-to-symbol (symbol-name name)
                                "$STEP"))
       (seq (strings-to-symbol (symbol-name name)
                               "$"
                               (symbol-name in-out)
                               "-SEQ"))
       (seq-netlist (strings-to-symbol (symbol-name name)
                                       "$"
                                       (symbol-name in-out)
                                       "-SEQ-NETLIST"))
       (seq-lemma (strings-to-symbol (symbol-name name)
                                     "$"
                                     (symbol-name in-out)
                                     "-SEQ-LEMMA"))
       (value-alt (strings-to-symbol (symbol-name name)
                                     "$VALUE-ALT"))
       (state-alt (strings-to-symbol (symbol-name name)
                                     "$STATE-ALT")))
    `(progn
       (defun ,seq (inputs-seq st ,@sizes n)
         (declare (ignorable st)
                  (xargs :measure (acl2-count n)))
         (if (zp n)
             nil
           (b* ((inputs (car inputs-seq))
                (,act-name ,act)
                (data ,data)
                (seq (,seq (cdr inputs-seq)
                           (,step inputs st ,@sizes)
                           ,@sizes
                           (1- n))))
             (if (equal ,act-name t)
                 (append seq (list data))
               seq))))

       (defun ,seq-netlist (inputs-seq st netlist ,(car sizes) n)
         (declare (ignorable st netlist)
                  (xargs :measure (acl2-count n)))
         (if (zp n)
             nil
           (b* ((inputs (car inputs-seq))
                (?outputs (se (si ',name ,(car sizes))
                              inputs st netlist))
                (,act-name ,(if (natp act-idx)
                                `(nth ,act-idx outputs)
                              act))
                (data ,(if netlist-data netlist-data data))
                (seq (,seq-netlist (cdr inputs-seq)
                                   (de (si ',name ,(car sizes))
                                       inputs st netlist)
                                   netlist
                                   ,(car sizes)
                                   (1- n))))
             (if (equal ,act-name t)
                 (append seq (list data))
               seq))))

       (defthm ,seq-lemma
         (implies (and (,recognizer netlist ,@sizes)
                       ,(if (or clink partial-clink)
                            `(,input-format-n inputs-seq st ,(car sizes) n)
                          `(,input-format-n inputs-seq ,(car sizes) n))
                       (,st-format st ,@sizes))
                  (equal (,seq-netlist inputs-seq st netlist ,(car sizes) n)
                         (,seq inputs-seq st ,@sizes n)))
         :hints (("Goal" :in-theory (enable ,value-alt
                                            ,state-alt
                                            ,act-fn))))
       )
    ))

;; Formalizing the relationship between input and output sequences

(defmacro in-out-stream-lemma (name &key
                                    (op 'nil)
                                    (inv 'nil)
                                    (clink 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp op)
                              (booleanp inv)
                              (booleanp clink))))
  (b* ((recognizer (strings-to-symbol (symbol-name name)
                                      "&"))
       (extract (strings-to-symbol (symbol-name name)
                                   "$EXTRACT"))
       (extracted-step (strings-to-symbol (symbol-name name)
                                          "$EXTRACTED-STEP"))
       (run (strings-to-symbol (symbol-name name)
                               "$RUN"))
       (de-n-lemma (strings-to-symbol (symbol-name name)
                                      "$DE-N"))
       (input-format-n (strings-to-symbol (symbol-name name)
                                              "$INPUT-FORMAT-N"))
       (valid-st (strings-to-symbol (symbol-name name)
                                    "$VALID-ST"))
       (valid-st=>st-format (strings-to-symbol (symbol-name name)
                                               "$VALID-ST=>ST-FORMAT"))
       (st-inv (strings-to-symbol (symbol-name name)
                                  "$INV"))
       (in-seq (strings-to-symbol (symbol-name name)
                                  "$IN-SEQ"))
       (in-seq-netlist (strings-to-symbol (symbol-name name)
                                          "$IN-SEQ-NETLIST"))
       (out-seq (strings-to-symbol (symbol-name name)
                                   "$OUT-SEQ"))
       (out-seq-netlist (strings-to-symbol (symbol-name name)
                                           "$OUT-SEQ-NETLIST"))
       (op-map (strings-to-symbol (symbol-name op) "-MAP"))
       (seq (if op
                `(,op-map seq)
              `(,in-seq inputs-seq st data-size n)))
       (hyps (if inv
                 `(and ,(if clink
                            `(,input-format-n inputs-seq st data-size n)
                          `(,input-format-n inputs-seq data-size n))
                       (,valid-st st data-size)
                       (,st-inv st))
               `(and ,(if clink
                          `(,input-format-n inputs-seq st data-size n)
                        `(,input-format-n inputs-seq data-size n))
                     (,valid-st st data-size))))
       (netlist-hyps
        (if inv
            `(and (,recognizer netlist data-size)
                  ,(if clink
                       `(,input-format-n inputs-seq st data-size n)
                     `(,input-format-n inputs-seq data-size n))
                  (,valid-st st data-size)
                  (,st-inv st))
          `(and (,recognizer netlist data-size)
                ,(if clink
                     `(,input-format-n inputs-seq st data-size n)
                   `(,input-format-n inputs-seq data-size n))
                (,valid-st st data-size))))
       (concl (if op
                  `(equal (append final-extracted-st
                                  (,out-seq inputs-seq st data-size n))
                          (append (,op-map
                                   (,in-seq inputs-seq st data-size n))
                                  extracted-st))
                `(equal (append final-extracted-st
                                (,out-seq inputs-seq st data-size n))
                        (append (,in-seq inputs-seq st data-size n)
                                extracted-st))))
       (netlist-concl
        (if op
            `(equal (append final-extracted-st
                            (,out-seq-netlist
                             inputs-seq st netlist data-size n))
                    (append (,op-map
                             (,in-seq-netlist
                              inputs-seq st netlist data-size n))
                            extracted-st))
          `(equal (append final-extracted-st
                          (,out-seq-netlist
                           inputs-seq st netlist data-size n))
                  (append (,in-seq-netlist
                           inputs-seq st netlist data-size n)
                          extracted-st))))
       (dataflow-correct-aux (strings-to-symbol (symbol-name name)
                                                "$DATAFLOW-CORRECT-AUX"))
       (dataflow-correct (strings-to-symbol (symbol-name name)
                                            "$DATAFLOW-CORRECT"))
       (functionally-correct (strings-to-symbol (symbol-name name)
                                                "$FUNCTIONALLY-CORRECT")))
    `(encapsulate
       ()

       (local
        (defthm ,dataflow-correct-aux
          (implies (equal (append x y1)
                          (append ,seq y2))
                   (equal (append x y1 z)
                          (append ,seq y2 z)))
          :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                          (associativity-of-append))))))

       (defthmd ,dataflow-correct
         (b* ((extracted-st (,extract st))
              (final-st (,run inputs-seq st data-size n))
              (final-extracted-st (,extract final-st)))
           (implies ,hyps ,concl))
         :hints (("Goal" :in-theory (enable ,extracted-step))))

       (defthmd ,functionally-correct
         (b* ((extracted-st (,extract st))
              (final-st (de-n (si ',name data-size)
                              inputs-seq st netlist n))
              (final-extracted-st (,extract final-st)))
           (implies ,netlist-hyps ,netlist-concl))
         :hints (("Goal"
                  :use ,dataflow-correct
                  :in-theory (enable ,valid-st=>st-format
                                     ,de-n-lemma))))
       )))

