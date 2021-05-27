;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; Vector modules of I/O pads.

;; It greatly simplifies the proofs at the CHIP level to package the pads into
;; the modules defined in this file.  However, LSI logic requires every module
;; to contain at least 1 "interior gate", i.e., a gate that is not a pad.
;; Therefore, in some places we introduce redundant buffers.

(in-package "FM9001")

(include-book "de")
(include-book "macros")
(include-book "primitives")
(include-book "unbound")

;; ======================================================================

;; TTL-INPUT-PADS

(defund ttl-input-pads-body (m n pin)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'g m)             ; Occurrence name
           (list (si 'out m)     ; Outputs
                 (si 'po m))
           'TTL-INPUT            ; Type TTL-INPUT
           (list (si 'in m) pin)) ; Inputs
     (cons
      (list (si 'b m)            ; Useless buffers for LSI's "lpace".
            (list (si 'b-out m))
            'B-BUF
            (list (si 'out m)))
      (ttl-input-pads-body (1+ m) (1- n) (si 'po m))))))

(defun ttl-input-pads-body$induction
    (m n pin bindings state-bindings netlist)
  (if (zp n)
      (list m pin bindings state-bindings netlist)
    (ttl-input-pads-body$induction
     (1+ m)
     (1- n)
     (si 'po m)
     (se-occ-bindings 2
                      (ttl-input-pads-body m
                                           n
                                           pin)
                      bindings
                      state-bindings
                      netlist)
     state-bindings netlist)))

(destructuring-lemma
 ttl-input-pads* (n)
 (declare (xargs :guard (posp n)))
 nil
 (si 'ttl-input-pads n)
 (cons 'pin (sis 'in 0 n))
 (cons (si 'po (1- n)) (sis 'b-out 0 n))
 nil
 (ttl-input-pads-body 0 n 'pin))

(defund ttl-input-pads& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (posp n))))
  (equal (assoc (si 'ttl-input-pads n) netlist)
         (ttl-input-pads* n)))

(defun ttl-input-pads$netlist (n)
  (declare (xargs :guard (posp n)))
  (list (ttl-input-pads* n)))

(defthm ttl-input-pads-body$unbound-in-body
  (implies (and (natp l)
                (natp m)
                (< l m))
           (unbound-in-body (si 'b-out l)
                            (ttl-input-pads-body m n pin)))
  :hints (("Goal"
           :in-theory (enable ttl-input-pads-body occ-outs))))

(defthmd ttl-input-pads-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'b-out m n)
                   (se-occ (ttl-input-pads-body m n pin)
                           bindings state-bindings netlist))
                  (v-threefix (assoc-eq-values (sis 'in m n) bindings))))
  :hints (("Goal"
           :induct (ttl-input-pads-body$induction m n pin bindings
                                                  state-bindings netlist)
           :in-theory (enable se-rules
                               ttl-input-pads-body
                               sis))))

(in-theory (disable ttl-input-pads-body$unbound-in-body))

(not-primp-lemma ttl-input-pads)

(defthmd ttl-input-pads$value
  (implies (and (ttl-input-pads& netlist n)
                (equal (len inputs) n)
                (true-listp inputs))
           (equal (cdr (se (si 'ttl-input-pads n)
                           (cons pin inputs)
                           sts
                           netlist))
                  (v-threefix inputs)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             ttl-input-pads&
                             ttl-input-pads*$destructure
                             not-primp-ttl-input-pads
                             ttl-input-pads-body$value)
                            ()))))

;; ======================================================================

;; TTL-OUTPUT-PADS

(defund ttl-output-pads-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'b m)             ; Useless buffers for LSI's "lpace".
           (list (si 'b-in m))
           'B-BUF
           (list (si 'in m)))
     (cons
      (list (si 'g m)            ; Occurrence name
            (list (si 'out m))   ; Outputs
            'TTL-OUTPUT          ; Type TTL-OUTUT
            (list (si 'b-in m))) ; Inputs
      (ttl-output-pads-body (1+ m) (1- n))))))

(defun ttl-output-pads-body$induction
    (m n bindings state-bindings netlist)
  (if (zp n)
      (list m bindings state-bindings netlist)
    (ttl-output-pads-body$induction
     (1+ m)
     (1- n)
     (se-occ-bindings 2
                      (ttl-output-pads-body m n)
                      bindings
                      state-bindings
                      netlist)
     state-bindings netlist)))

(destructuring-lemma
 ttl-output-pads* (n)
 (declare (xargs :guard (natp n)))
 nil
 (si 'ttl-output-pads n)
 (sis 'in 0 n)
 (sis 'out 0 n)
 nil
 (ttl-output-pads-body 0 n))

(defund ttl-output-pads& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (equal (assoc (si 'ttl-output-pads n) netlist)
         (ttl-output-pads* n)))

(defun ttl-output-pads$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (ttl-output-pads* n)))

(defthm ttl-output-pads-body$unbound-in-body
  (implies (and (natp l)
                (natp m)
                (< l m))
           (unbound-in-body (si 'out l)
                            (ttl-output-pads-body m n)))
  :hints (("Goal"
           :in-theory (enable ttl-output-pads-body occ-outs))))

(defthmd ttl-output-pads-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'out m n)
                   (se-occ (ttl-output-pads-body m n)
                           bindings state-bindings netlist))
                  (v-threefix (assoc-eq-values (sis 'in m n) bindings))))
  :hints (("Goal"
           :induct (ttl-output-pads-body$induction m n bindings
                                                   state-bindings netlist)
           :in-theory (enable se-rules
                               ttl-output-pads-body
                               sis))))

(in-theory (disable ttl-output-pads-body$unbound-in-body))

(not-primp-lemma ttl-output-pads)

(defthmd ttl-output-pads$value
  (implies (and (ttl-output-pads& netlist n)
                (equal (len inputs) n)
                (true-listp inputs))
           (equal (se (si 'ttl-output-pads n)
                      inputs sts netlist)
                  (v-threefix inputs)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             ttl-output-pads&
                             ttl-output-pads*$destructure
                             not-primp-ttl-output-pads
                             ttl-output-pads-body$value)
                            ()))))

;; ======================================================================

;; TTL-TRI-OUTPUT-PADS

(defund ttl-tri-output-pads-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'g m)                      ; Occurrence name
           (list (si 'out m))             ; Outputs
           'TTL-TRI-OUTPUT                ; Type TTL-TRI-OUTPUT
           (list (si 'in m) 'enable-buf)) ; Inputs
     (ttl-tri-output-pads-body (1+ m) (1- n)))))

(defun ttl-tri-output-pads-body$induction
    (m n bindings state-bindings netlist)
  (if (zp n)
      (list m bindings state-bindings netlist)
    (ttl-tri-output-pads-body$induction
     (1+ m)
     (1- n)
     (se-occ-bindings 1
                      (ttl-tri-output-pads-body m n)
                      bindings
                      state-bindings
                      netlist)
     state-bindings netlist)))

(destructuring-lemma
 ttl-tri-output-pads* (n)
 (declare (xargs :guard (natp n)))
 nil
 (si 'ttl-tri-output-pads n)
 (cons 'enable (sis 'in 0 n))
 (sis 'out 0 n)
 nil
 (cons (list 'enable-buffer '(enable-buf)
             (if (< n 8) 'B-BUF 'B-BUF-PWR)
             '(enable))
       (ttl-tri-output-pads-body 0 n)))

(defund ttl-tri-output-pads& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'ttl-tri-output-pads n) netlist)
              (ttl-tri-output-pads* n))
       (let ((netlist (delete-to-eq (si 'ttl-tri-output-pads n) netlist)))
         (if (< n 8)
             t
           (b-buf-pwr& netlist)))))

(defun ttl-tri-output-pads$netlist (n)
  (declare (xargs :guard (natp n)))
  (if (< n 8)
      (list (ttl-tri-output-pads* n))
    (cons (ttl-tri-output-pads* n) *b-buf-pwr*)))

(defthm ttl-tri-output-pads-body$unbound-in-body
  (implies (and (natp l)
                (natp m)
                (< l m))
           (unbound-in-body (si 'out l)
                            (ttl-tri-output-pads-body m n)))
  :hints (("Goal"
           :in-theory (enable ttl-tri-output-pads-body occ-outs))))

(defthmd ttl-tri-output-pads-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'out m n)
                   (se-occ (ttl-tri-output-pads-body m n)
                           bindings state-bindings netlist))
                  (vft-buf (f-not (assoc-eq-value 'enable-buf bindings))
                           (assoc-eq-values (sis 'in m n) bindings))))
  :hints (("Goal"
           :induct (ttl-tri-output-pads-body$induction m n bindings
                                                       state-bindings
                                                       netlist)
           :in-theory (enable se-rules
                               ttl-tri-output-pads-body
                               vft-buf-rewrite
                               repeat
                               sis))))

(in-theory (disable ttl-tri-output-pads-body$unbound-in-body))

(not-primp-lemma ttl-tri-output-pads)

(defthmd ttl-tri-output-pads$value
  (implies (and (ttl-tri-output-pads& netlist n)
                (equal (len inputs) n)
                (true-listp inputs))
           (equal (se (si 'ttl-tri-output-pads n)
                      (cons enable inputs)
                      sts netlist)
                  (vft-buf (f-not enable) inputs)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             ttl-tri-output-pads&
                             ttl-tri-output-pads*$destructure
                             not-primp-ttl-tri-output-pads
                             b-buf-pwr$value
                             ttl-tri-output-pads-body$value
                             f-not-f-buf=f-not)
                            ()))))

;; ======================================================================

;; TTL-BIDIRECT-PADS

(defund ttl-bidirect-pads-body (m n pin)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'g m)          ; Occurrence name
           (list (si 'data m) ; Outputs
                 (si 'out m)
                 (si 'po m))
           'TTL-BIDIRECT      ; Type TTL-OUTUT
           (list (si 'data m) ; Inputs
                 (si 'in m)
                 'buf-enable pin))
     (ttl-bidirect-pads-body (1+ m) (1- n) (si 'po m)))))

(defun ttl-bidirect-pads-body$induction
    (m n pin bindings state-bindings netlist)
  (if (zp n)
      (list m pin bindings state-bindings netlist)
    (ttl-bidirect-pads-body$induction
     (1+ m)
     (1- n)
     (si 'po m)
     (se-occ-bindings 1
                      (ttl-bidirect-pads-body m
                                              n
                                              pin)
                      bindings
                      state-bindings
                      netlist)
     state-bindings netlist)))

(destructuring-lemma
 ttl-bidirect-pads* (n)
 (declare (xargs :guard (posp n)))
 nil
 (si 'ttl-bidirect-pads n)
 (list* 'enable 'pin (append (sis 'data 0 n) (sis 'in 0 n)))
 (list* (si 'po (1- n)) (append (sis 'data 0 n) (sis 'out 0 n)))
 nil
 (cons (list 'enable-buf '(buf-enable)
             (if (< n 8) 'B-BUF 'B-BUF-PWR)
             '(enable))
       (ttl-bidirect-pads-body 0 n 'pin)))

(defund ttl-bidirect-pads& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (posp n))))
  (and (equal (assoc (si 'ttl-bidirect-pads n) netlist)
              (ttl-bidirect-pads* n))
       (let ((netlist (delete-to-eq (si 'ttl-bidirect-pads n) netlist)))
         (if (< n 8)
             t
           (b-buf-pwr& netlist)))))

(defun ttl-bidirect-pads$netlist (n)
  (declare (xargs :guard (posp n)))
  (if (< n 8)
      (list (ttl-bidirect-pads* n))
    (cons (ttl-bidirect-pads* n) *b-buf-pwr*)))

(defthm ttl-bidirect-pads-body$unbound-in-body
  (implies (and (natp l)
                (natp m)
                (< l m))
           (and
            (unbound-in-body (si 'data l) (ttl-bidirect-pads-body m n pin))
            (unbound-in-body (si 'out l) (ttl-bidirect-pads-body m n pin))
            (unbound-in-body (si 'po l) (ttl-bidirect-pads-body m n pin))
            (unbound-in-body (si 'in l) (ttl-bidirect-pads-body m n pin))))
  :hints (("Goal"
           :in-theory (enable ttl-bidirect-pads-body occ-outs))))

(local
 (defthm 3vp=>4vp
   (implies (3vp x)
            (4vp x))
   :hints (("Goal" :in-theory (enable 3vp 4vp)))
   :rule-classes (:rewrite :type-prescription)))

(defthmd ttl-bidirect-pads-body$value
  (implies (natp m)
           (and
            (equal (assoc-eq-values
                    (sis 'data m n)
                    (se-occ (ttl-bidirect-pads-body m n pin)
                            bindings state-bindings netlist))
                   (if (not (assoc-eq-value 'buf-enable bindings))
                       (v-threefix (assoc-eq-values (sis 'in m n) bindings))
                     (if (equal (assoc-eq-value 'buf-enable bindings) t)
                         (make-list n :initial-element *z*)
                       (make-list n :initial-element *x*))))

            (equal (assoc-eq-values
                    (sis 'out m n)
                    (se-occ (ttl-bidirect-pads-body m n pin)
                            bindings state-bindings netlist))
                   (if (not (assoc-eq-value 'buf-enable bindings))
                       (v-threefix
                        (v-wire (assoc-eq-values (sis 'data m n) bindings)
                                (v-threefix (assoc-eq-values (sis 'in m n)
                                                             bindings))))
                     (if (equal (assoc-eq-value 'buf-enable bindings) t)
                         (v-threefix (assoc-eq-values (sis 'data m n) bindings))
                       (make-list n :initial-element *x*))))))
  :hints (("Goal"
           :induct (ttl-bidirect-pads-body$induction m n pin bindings
                                                     state-bindings netlist)
           :in-theory (enable se-rules
                               ttl-bidirect-pads-body
                               v-threefix
                               v-wire
                               f-not
                               ft-buf-rewrite
                               ft-wire-rewrite
                               repeat
                               sis))))

(in-theory (disable ttl-bidirect-pads-body$unbound-in-body))

(not-primp-lemma ttl-bidirect-pads)

(defthmd ttl-bidirect-pads$value
  (implies (and (ttl-bidirect-pads& netlist n)
                (equal (len data) n)
                (true-listp data)
                (equal (len inputs) n)
                (true-listp inputs))
           (equal
            (cdr (se (si 'ttl-bidirect-pads n)
                     (list* enable pin (append data inputs))
                     state-bindings netlist))
            (append
             (vft-buf (f-not enable) inputs)
             (v-threefix (v-wire data (vft-buf (f-not enable) inputs))))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             ttl-bidirect-pads&
                             ttl-bidirect-pads*$destructure
                             not-primp-ttl-bidirect-pads
                             b-buf-pwr$value
                             ttl-bidirect-pads-body$value
                             f-not
                             vft-buf-rewrite)
                            (append-v-threefix
                             make-list-ac
                             make-list-ac-removal)))))
