;; Copyright (C) 2021, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2021

;; An example of simulating FM9001

(in-package "FM9001")

(include-book "fm9001-spec")

;; ======================================================================

(defund init-state ()
  (declare (xargs :guard t))
  (list
   ;; Processor state
   (list
    ;; Register file
    (cons (cons (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32))))
                (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32)))))
          (cons (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32))))
                (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            ;; PC
                            (ram (make-list 32))))))
    ;; Flags
    '(nil nil nil nil))
   ;; Memory state
   (alloc-mem 1 ;; Address 1
              'ram
              (ash #b1110 24) ;; Value
              (alloc-mem 0 ;; Address 0
                         'ram
                         (ash #b1 24) ;; Value
                         nil))))

(set-print-base-radix 16 state)

(fm9001-state-pprint (init-state)) ;; Note that PC = reg[15] = 0 at the initial
                                   ;; state
(fm9001-state-pprint (fm9001 (init-state) 1)) ;; Perform INC because of the
                                              ;; value at memory address 0
(fm9001-state-pprint (fm9001 (init-state) 2)) ;; Perform NOT because of the
                                              ;; value at memory address 1
(fm9001-state-pprint (fm9001 (init-state) 3)) ;; Just increment PC
