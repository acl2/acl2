;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

;; VECTOR-MODULE name (occ-name outputs type inputs) specs &key enable

(in-package "ADE")

(include-book "macros")

;; ======================================================================

;; VECTOR-MODULE creates simple, linear, n-bit module generators.

;; Arguments:

;; * name -- The generator will be (<name>* n)

;; * (occ-name outputs type inputs) --  A schematic representation of the
;; occurrences.  The body of the generator will contain occurrences of the
;; form:
;;       (<occ-name>_n
;;        (<output_0>_n ... <output_k>_n)
;;        type
;;        (<input_0>_n ... <input_k>_n))

;; * specs -- A list of specifications for the output vectors, written in
;; terms of the inputs.

;; * enable -- A list of events to be enabled.

;; Example: (vector-module v-pullup (g (y) pullup (a)) ((v-pullup a))
;;                         :enable (v-pullup)) 

;; More examples in "vector-module.lisp".

(defun mapAPPEND (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (cdr x))
          `(APPEND ,(car x) ,(mapAPPEND (cdr x)))
        (car x))
    nil))

(defun mapAND (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (cdr x))
          `(AND ,(car x) ,(mapAND (cdr x)))
        (car x))
    nil))

(defun map-si (x m)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(si ',(car x) ,m)
          (map-si (cdr x) m))))

(defun map-sis (x m n)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(sis ',(car x) ,m ,n)
          (map-sis (cdr x) m n))))

(defun map-unbound-in-body (x body l m n)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(unbound-in-body (si ',(car x) ,l)
                            (,body ,m ,n))
          (map-unbound-in-body (cdr x) body l m n))))

(defun map-assoc-eq-values (x m n)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(assoc-eq-values (sis ',(car x) ,m ,n)
                            bindings)
          (map-assoc-eq-values (cdr x) m n))))

(defun map-equal-assoc-eq-values (x y m n)
  (declare (xargs :guard (true-list-listp y)))
  (if (or (atom x) (atom y))
      nil
    (cons `(equal (assoc-eq-values (sis ',(car x) ,m ,n)
                                   (se-occ body
                                           bindings
                                           state-bindings
                                           netlist))
                  ,(let* ((spec (car y))
                          (fn (car spec))
                          (args (cdr spec)))
                     `(,fn ,@(map-assoc-eq-values args m n))))
          (map-equal-assoc-eq-values (cdr x) (cdr y) m n))))

(defun map-value-lemma-hyp (x n)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(and (true-listp ,(car x))
                (equal (len ,(car x)) ,n))
          (map-value-lemma-hyp (cdr x) n))))

(defun map-value-lemma-concl (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (atom x)
      nil
    (cons (let* ((fn (caar x))
                 (args (cdar x)))
            `(,fn ,@args))
          (map-value-lemma-concl (cdr x)))))

(defmacro vector-module (name occ specs &key enable)
  (let* ((occ-name (car occ))
         (outputs (cadr occ))
         (type (caddr occ))
         (inputs (cadddr occ))
         (name-str (symbol-name name))
         (body-defun (unstring name-str "$BODY"))
         (generator (unstring name-str "*"))
         (destructor (unstring (symbol-name generator) "$DESTRUCTURE"))
         (module-name `(SI ',name N))
         (predicate (unstring name-str "&"))
         (unbound-in-body-lemma (unstring name-str "$UNBOUND-IN-BODY"))
         (body-value-lemma (unstring name-str "$BODY-VALUE"))
         (not-primp-lemma-name (unstring "NOT-PRIMP-" name-str))
         (value-lemma (unstring name-str "$VALUE"))
         (netlist (unstring name-str "$NETLIST")))

    `(PROGN

      (DEFUN ,body-defun (M N)
        (DECLARE (XARGS :GUARD (AND (NATP M) (NATP N))))
        (IF (ZP N)
            NIL
            (CONS
             (LIST (SI ',occ-name M)
                   (LIST ,@(map-si outputs 'M))
                   ',type
                   (LIST ,@(map-si inputs 'M)))
             (,body-defun (1+ M) (1- N)))))

      (MODULE-GENERATOR
       ,generator (N)
       ,module-name
       ,(mapAPPEND
         (map-sis inputs 0 'N))
       ,(mapAPPEND
         (map-sis outputs 0 'N))
       NIL
       (,body-defun 0 N)
       :guard (natp n))

      (DEFUN ,predicate (NETLIST N)
        (DECLARE (XARGS :GUARD (AND (ALISTP NETLIST)
                                    (NATP N))))
        (EQUAL (ASSOC ,module-name NETLIST)
               (,generator N)))

      (DEFUN ,netlist (N)
        (DECLARE (XARGS :GUARD (NATP N)))
        (LIST (,generator N)))

      (DEFTHM ,unbound-in-body-lemma
        (IMPLIES (and (NATP L)
                      (NATP M)
                      (< L M))
                 ,(mapAND (map-unbound-in-body outputs body-defun 'L 'M 'N)))
        :HINTS (("GOAL"
                 :IN-THEORY (ENABLE OCC-OUTS))))

      (DEFTHM ,body-value-lemma
        (IMPLIES (AND (NATP M)
                      (EQUAL BODY (,body-defun M N)))
                 ,(mapAND
                   (map-equal-assoc-eq-values outputs specs 'M 'N)))
        :hints (("Goal"
                 :INDUCT (VECTOR-MODULE-INDUCTION BODY
                                                  M N
                                                  BINDINGS
                                                  STATE-BINDINGS
                                                  NETLIST)
                 :in-theory (ENABLE de-rules sis ,@enable))))

      (NOT-PRIMP-LEMMA ,name)

      (DEFTHM ,value-lemma
        (IMPLIES (AND (,predicate NETLIST N)
                      ,(mapAND
                        (map-value-lemma-hyp inputs 'N)))
                 (EQUAL
                  (SE ,module-name ,(mapAPPEND inputs)
                      STS NETLIST)
                  ,(mapAPPEND
                    (map-value-lemma-concl specs))))
        :hints (("Goal"
                 :do-not '(preprocess)
                 :expand (SE ,module-name ,(mapAPPEND inputs)
                             STS NETLIST)
                 :in-theory (ENABLE de-rules
                                    ,destructor
                                    ,not-primp-lemma-name))))

      (IN-THEORY (DISABLE ,body-defun
                          ,predicate
                          ,unbound-in-body-lemma
                          ,body-value-lemma
                          ,value-lemma))
      )))
