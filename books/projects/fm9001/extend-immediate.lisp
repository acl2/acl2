;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "primitives")
(include-book "tv-if")

;; ======================================================================

;; This module selects either a 32-bit value, or a 32-bit value produced by
;; sign-extending a 9-bit value into 32 bits.

(module-generator
 extend-immediate* ()
 'extend-immediate
 (cons 'select-immediate (append (sis 'immediate 0 9) (sis 'reg-data 0 32)))
 (sis 'z 0 32)
 nil
 (list
  (list 'buffer
        '(sign-bit)
        'b-buf-pwr
        (list (si 'immediate 8)))
  (list 'mux
        (sis 'z 0 32)
        (si 'tv-if (tree-number (make-tree 32)))
        (cons 'select-immediate
              (append (append (sis 'immediate 0 9)
                              (make-list 23 :initial-element 'sign-bit))
                      (sis 'reg-data 0 32)))))
 :guard t)

(defund extend-immediate& (netlist)
  (and (equal (assoc 'extend-immediate netlist)
              (extend-immediate*))
       (let ((netlist (delete-to-eq 'extend-immediate netlist)))
         (and (b-buf-pwr& netlist)
              (tv-if& netlist (make-tree 32))))))

(defun extend-immediate$netlist ()
  (cons (extend-immediate*)
        (union$ *b-buf-pwr*
                (tv-if$netlist (make-tree 32))
                :test 'equal)))

(defthm check-extend-immediate$netlist
  (extend-immediate& (extend-immediate$netlist)))

(defun f$extend-immediate (select-immediate immediate reg-data)
  (declare (xargs :guard (and (true-listp immediate)
                              (true-listp reg-data))))
  (fv-if select-immediate
         (append immediate
                 (if (booleanp (nth 8 immediate))
                     (make-list 23 :initial-element (nth 8 immediate))
                   (make-list 23 :initial-element *x*)))
         reg-data))

;; (defthm true-listp-f$extend-immediate
;;   (true-listp (f$extend-immediate select-immediate immediate reg-bus))
;;   :rule-classes :type-prescription)

(defthm len-f$extend-immediate
  (implies (equal (len immediate) 9)
           (equal (len (f$extend-immediate select-immediate immediate reg-bus))
                  32)))

(defthm f$extend-immediate=extend-immediate
  (implies (and (bvp immediate) (equal (len immediate) 9)
                (bvp reg-data) (equal (len reg-data) 32)
                (booleanp select-immediate))
           (equal (f$extend-immediate select-immediate immediate reg-data)
                  (if* select-immediate
                       (sign-extend immediate 32)
                       reg-data)))
  :hints (("Goal" :in-theory (enable sign-extend-as-append))))

(defthmd extend-immediate$value
  (implies (and (extend-immediate& netlist)
                (true-listp immediate) (equal (len immediate) 9)
                (true-listp reg-data) (equal (len reg-data) 32))
           (equal (se 'extend-immediate
                      (cons select-immediate (append immediate reg-data))
                      sts netlist)
                  (f$extend-immediate select-immediate immediate reg-data)))
  :hints (("Goal"
           :use ((:instance tv-if$value
                            (c select-immediate)
                            (a (append immediate
                                       (make-list 23
                                                  :initial-element
                                                  *x*)))
                            (b reg-data)
                            (tree (make-tree 32))
                            (sts nil)
                            (netlist (delete-to-eq 'extend-immediate
                                                   netlist)))
                 (:instance tv-if$value
                            (c select-immediate)
                            (a (append immediate
                                       (make-list 23
                                                  :initial-element
                                                  (nth 8 immediate))))
                            (b reg-data)
                            (tree (make-tree 32))
                            (sts nil)
                            (netlist (delete-to-eq 'extend-immediate
                                                   netlist))))
           :in-theory (e/d (se-rules
                            extend-immediate&
                            extend-immediate*$destructure
                            b-buf-pwr$value)
                           ((extend-immediate*)
                            (si)
                            (sis)
                            (make-tree)
                            (make-list-ac)
                            make-list-ac-removal
                            tv-disabled-rules)))))

(in-theory (disable f$extend-immediate))
