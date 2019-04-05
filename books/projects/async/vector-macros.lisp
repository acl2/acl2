;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

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
                            wire-alist)
          (map-assoc-eq-values (cdr x) m n))))

(defun map-equal-assoc-eq-values (x y m n)
  (declare (xargs :guard (true-list-listp y)))
  (if (or (atom x) (atom y))
      nil
    (cons `(equal (assoc-eq-values (sis ',(car x) ,m ,n)
                                   (se-occ body
                                           wire-alist
                                           st-alist
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
         (body-defun (strings-to-symbol name-str "-BODY"))
         (generator (strings-to-symbol name-str "*"))
         (destructor (strings-to-symbol (symbol-name generator)
                                        "$DESTRUCTURE"))
         (module-name `(SI ',name N))
         (predicate (strings-to-symbol name-str "&"))
         (unbound-in-body-lemma (strings-to-symbol name-str
                                                   "$UNBOUND-IN-BODY"))
         (body-value-lemma (strings-to-symbol name-str "-BODY$VALUE"))
         (value-lemma (strings-to-symbol name-str "$VALUE"))
         (netlist (strings-to-symbol name-str "$NETLIST")))

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
       (declare (xargs :guard (natp N))))

      (DEFUND ,predicate (NETLIST N)
        (DECLARE (XARGS :GUARD (AND (ALISTP NETLIST)
                                    (NATP N))))
        (EQUAL (ASSOC ,module-name NETLIST)
               (,generator N)))

      (DEFUND ,netlist (N)
        (DECLARE (XARGS :GUARD (NATP N)))
        (LIST (,generator N)))

      (LOCAL
       (DEFTHM ,unbound-in-body-lemma
         (IMPLIES (and (NATP L)
                       (NATP M)
                       (< L M))
                  ,(mapAND (map-unbound-in-body outputs body-defun 'L 'M 'N)))
         :HINTS (("GOAL"
                  :IN-THEORY (ENABLE OCC-OUTS)))))

      (LOCAL
       (DEFTHM ,body-value-lemma
         (IMPLIES (AND (NATP M)
                       (EQUAL BODY (,body-defun M N)))
                  ,(mapAND
                    (map-equal-assoc-eq-values outputs specs 'M 'N)))
         :hints (("Goal"
                  :INDUCT (VECTOR-MODULE-INDUCTION BODY
                                                   M N
                                                   WIRE-ALIST
                                                   ST-ALIST
                                                   NETLIST)
                  :in-theory (ENABLE de-rules sis ,@enable)))))

      (DEFTHM ,value-lemma
        (IMPLIES (AND (,predicate NETLIST N)
                      ,(mapAND
                        (map-value-lemma-hyp inputs 'N)))
                 (EQUAL
                  (SE ,module-name ,(mapAPPEND inputs)
                      ST NETLIST)
                  ,(mapAPPEND
                    (map-value-lemma-concl specs))))
        :hints (("Goal"
                 :expand (:free (inputs N)
                                (SE ,module-name ,(mapAPPEND inputs)
                                    ST NETLIST))
                 :in-theory (ENABLE de-rules ,predicate ,destructor))))
      )))
