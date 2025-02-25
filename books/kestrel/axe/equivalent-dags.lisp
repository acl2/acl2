; Recognizing equivalent DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "dags")
(include-book "make-equality-dag")

;equivalent dags represent the same mathematical function but have their nodes numbered differently
;requires that the dags be dag-lsts, not quoteps
(defund equivalent-dagsp (dag1 dag2)
  (declare (xargs :guard (and (pseudo-dagp dag1)
                              (pseudo-dagp dag2)
                              (<= (+ (len dag1) (len dag2))
                                  *max-1d-array-length*))
                  :guard-hints (("Goal" :use (:instance true-listp-of-car-of-mv-nth-1-of-make-equality-dag)
                                 :in-theory (disable true-listp-of-car-of-mv-nth-1-of-make-equality-dag quotep)))))
  (if (equal dag1 dag2) ;slow? how often is this the case?
      t
    (if (not (eql (len dag1) (len dag2))) ;different lengths means not equivalent (todo: what if constants got inlined?)
        nil
      ;;faster way to do this check? stop as soon as a difference is found!
      (b* (((mv erp equality-dag) (make-equality-dag dag1 dag2)) ;BOZO change to stop as soon as it finds a node that doesn't have an analogue in the other dag?
           ((when erp) nil) ;todo: consider passing back the error
           )
        (if (quotep equality-dag)
            (if (unquote equality-dag)
                t
              nil)
          (let* ((equality-node (car equality-dag))
                 (equality-expr (cdr equality-node))
                 )
            ;;the dags are equal if they merge into an equality dag whose top expr is (equal <foo> <foo>)
            (equal (farg1 equality-expr)
                   (farg2 equality-expr))))))))

;fixme what if one is a constant and the other is a dag with one node that is that constant?
(defund equivalent-dags-or-quoteps (dag1 dag2)
  (declare (xargs :guard (and (or (myquotep dag1)
                                  (pseudo-dagp dag1))
                              (or (myquotep dag2)
                                  (pseudo-dagp dag2))
                              (<= (+ (len dag1) (len dag2))
                                  *max-1d-array-length*))))
  (if (or (quotep dag1)
          (quotep dag2))
      (equal dag1 dag2)
    (equivalent-dagsp dag1 dag2)))

;; This one can return an error if the dags are too big.
;; Returns (mv erp equivalentp).
(defund equivalent-dagsp2 (dag1 dag2)
  (declare (xargs :guard (and (pseudo-dagp dag1)
                              (pseudo-dagp dag2))))
  (if (<= (+ (len dag1) (len dag2))
          *max-1d-array-length*)
      (mv nil (equivalent-dagsp dag1 dag2))
    (mv :dags-too-big nil)))
