;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2018

(in-package "ADE")

(include-book "link-joint")
(include-book "store-n")
(include-book "vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

(defconst *netlist*
  '((flip-flop
     (en bit-in)
     (bit-out)
     (L0 L1)
     ((L0 (L0-out L0-out~) latch (en bit-in))
      (G (en~) b-not (en))
      (L1 (bit-out bit-out~) latch (en~ L0-out))))))

(defund flip-flop& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc 'flip-flop netlist)
         (car *netlist*)))

(local
 (defthmd check-flip-flop
   (and (net-syntax-okp *netlist*)
        (net-arity-okp *netlist*)
        (flip-flop& *netlist*))))

(defthmd flip-flop$value
  (implies (flip-flop& netlist)
           (equal (se 'flip-flop input st netlist)
                  (list (f-if (f-not (first input))
                            (f-if (first input)
                                (second input)
                              (first (first st)))
                          (first (second st))))))
  :hints (("Goal"
           :expand (se 'flip-flop input st netlist)
           :in-theory (enable de-rules flip-flop&))))

(defthmd flip-flop$state
  (implies (flip-flop& netlist)
           (equal (de 'flip-flop input st netlist)
                  (list (list (f-if (first input)
                                    (second input)
                                    (first (first st))))
                        (list (f-if (f-not (first input))
                                    (f-if (first input)
                                          (second input)
                                          (first (first st)))
                                    (first (second st)))))))
  :hints (("Goal"
           :expand (de 'flip-flop input st netlist)
           :in-theory (enable de-rules flip-flop&))))

(assert-event
 (equal (se 'flip-flop '(nil nil) '((t) (nil)) *netlist*)
        '(t)))

(assert-event
 (equal (de 'flip-flop '(nil nil) '((t) (nil)) *netlist*)
        '((t) (t))))


