;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "macros")

;; ======================================================================

;;;;;    MONOTONICITY LEMMAS FOR BOOLEAN FUNCTIONS     ;;;;;

;; e.g.:

;;   >(macroexpand-1 '(monotonicity-lemma f-and3))
;;   (PROVE-LEMMA F-AND3-MONOTONE (REWRITE)
;;       (IMPLIES (AND (B-APPROX A1 A2) (B-APPROX B1 B2) (B-APPROX C1 C2))
;;                (B-APPROX (F-AND3 A1 B1 C1) (F-AND3 A2 B2 C2))))
;;   T
;;
;;   >

(defun b-approx-args (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons `(b-approx ,(si 'a n) ,(si 'b n))
          (b-approx-args (1- n)))))

(defun monotonicity-lemma-fn (name arity hints)
  (declare (xargs :guard (and (symbolp name)
                              (natp arity))))
  (b* ((lemma-name (unstring (symbol-name name) "-MONOTONE")))

    `(defthm ,lemma-name
       (implies (and ,@(rev (b-approx-args arity)))
                (b-approx (,name ,@(sis 'a 1 arity))
                          (,name ,@(sis 'b 1 arity))))
       :hints ,hints)))

(defun monotonicity-lemmas-fn (names arities hints)
  (declare (xargs :guard (and (symbol-listp names)
                              (nat-listp arities)
                              (equal (len names) (len arities)))))
  (if (atom names)
      nil
    (cons (monotonicity-lemma-fn (car names) (car arities) hints)
          (monotonicity-lemmas-fn (cdr names) (cdr arities) hints))))

(defmacro monotonicity-lemmas (names arities &optional hints)
  `(progn ,@(monotonicity-lemmas-fn names arities hints)))

;; ======================================================================

;;;;;           PROVE-PRIMITIVE-MONOTONICITY           ;;;;;

;; >(macroexpand-1 '(prove-primitive-monotonicity (AO2 AO4)))
;; (DO-EVENTS-RECURSIVE
;;     '((PROVE-LEMMA DUAL-EVAL-AO2-VALUE (REWRITE)
;;           (EQUAL (DUAL-EVAL 0 'AO2 ARGS STATE NETLIST)
;;                  (LET ((A (CAR ARGS)) (B (CAR (CDR ARGS)))
;;                        (C (CAR (CDR (CDR ARGS))))
;;                        (D (CAR (CDR (CDR (CDR ARGS))))))
;;                    (CONS (F-NOR (F-AND A B) (F-AND C D)) 'NIL)))
;;           ((ENABLE DUAL-EVAL DUAL-APPLY-VALUE)))
;;       (PROVE-LEMMA DUAL-EVAL-AO2-STATE (REWRITE)
;;           (EQUAL (DUAL-EVAL 2 'AO2 ARGS STATE NETLIST) 0)
;;           ((ENABLE DUAL-EVAL DUAL-APPLY-STATE)))
;;       (PROVE-LEMMA AO2-MONOTONE (REWRITE)
;;           (AND (MONOTONICITY-PROPERTY 0 'AO2 NETLIST A1 A2 S1 S2)
;;                (MONOTONICITY-PROPERTY 2 'AO2 NETLIST A1 A2 S1 S2))
;;           ((DISABLE-THEORY T)
;;            (ENABLE-THEORY GROUND-ZERO MONOTONICITY-LEMMAS)
;;            (ENABLE *1*B-APPROX *1*V-APPROX *1*S-APPROX V-APPROX
;;                    MONOTONICITY-PROPERTY-OPENER-0
;;                    MONOTONICITY-PROPERTY-OPENER-2 DUAL-EVAL-AO2-VALUE
;;                    DUAL-EVAL-AO2-STATE S-APPROX-IMPLIES-B-APPROX
;;                    FOURP-IMPLIES-S-APPROX-IS-B-APPROX FOURP-F-BUF
;;                    FOURP-F-IF)
;;            (EXPAND (V-APPROX A1 A2) (V-APPROX (CDR A1) (CDR A2))
;;                    (V-APPROX (CDR (CDR A1)) (CDR (CDR A2)))
;;                    (V-APPROX (CDR (CDR (CDR A1))) (CDR (CDR (CDR A2)))))))
;;       (PROVE-LEMMA DUAL-EVAL-AO4-VALUE (REWRITE)
;;           (EQUAL (DUAL-EVAL 0 'AO4 ARGS STATE NETLIST)
;;                  (LET ((A (CAR ARGS)) (B (CAR (CDR ARGS)))
;;                        (C (CAR (CDR (CDR ARGS))))
;;                        (D (CAR (CDR (CDR (CDR ARGS))))))
;;                    (CONS (F-NAND (F-OR A B) (F-OR C D)) 'NIL)))
;;           ((ENABLE DUAL-EVAL DUAL-APPLY-VALUE)))
;;       (PROVE-LEMMA DUAL-EVAL-AO4-STATE (REWRITE)
;;           (EQUAL (DUAL-EVAL 2 'AO4 ARGS STATE NETLIST) 0)
;;           ((ENABLE DUAL-EVAL DUAL-APPLY-STATE)))
;;       (PROVE-LEMMA AO4-MONOTONE (REWRITE)
;;           (AND (MONOTONICITY-PROPERTY 0 'AO4 NETLIST A1 A2 S1 S2)
;;                (MONOTONICITY-PROPERTY 2 'AO4 NETLIST A1 A2 S1 S2))
;;           ((DISABLE-THEORY T)
;;            (ENABLE-THEORY GROUND-ZERO MONOTONICITY-LEMMAS)
;;            (ENABLE *1*B-APPROX *1*V-APPROX *1*S-APPROX V-APPROX
;;                    MONOTONICITY-PROPERTY-OPENER-0
;;                    MONOTONICITY-PROPERTY-OPENER-2 DUAL-EVAL-AO4-VALUE
;;                    DUAL-EVAL-AO4-STATE S-APPROX-IMPLIES-B-APPROX
;;                    FOURP-IMPLIES-S-APPROX-IS-B-APPROX FOURP-F-BUF
;;                    FOURP-F-IF)
;;            (EXPAND (V-APPROX A1 A2) (V-APPROX (CDR A1) (CDR A2))
;;                    (V-APPROX (CDR (CDR A1)) (CDR (CDR A2)))
;;                    (V-APPROX (CDR (CDR (CDR A1)))
;;                              (CDR (CDR (CDR A2)))))))))
;; T
;;
;; >

(defun device-monotonicity-lemma (name)
  (declare (xargs :guard (symbolp name)))
  (b* ((lemma-name (unstring (symbol-name name) "-MONOTONE")))

    `(defthm ,lemma-name
       (and (monotonicity-property 0 ',name netlist a1 a2 s1 s2)
            (monotonicity-property 2 ',name netlist a1 a2 s1 s2))
       :hints (("Goal"
                :in-theory (enable de-rules
                                   mem-theory
                                   monotonicity-property-opener-0
                                   monotonicity-property-opener-2))))))

(defun device-monotonicity-lemmas (names)
  (declare (xargs :guard (symbol-listp names)))
  (if (atom names)
      nil
    (cons (device-monotonicity-lemma (car names))
          (device-monotonicity-lemmas (cdr names)))))

(defmacro prove-primitive-monotonicity (names)
  `(progn ,@(device-monotonicity-lemmas names)))


