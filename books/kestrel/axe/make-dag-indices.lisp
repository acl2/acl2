; Making the 3 indices of a DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A DAG has 3 kinds of indices, the parent-array, constant-alist, and variable-alist.  The file contains utilities to make all 3.

;; TODO: Consider making versions of these that assume the dag-array-name and
;; dag-parent-array-name are the standard names (and rename the existing
;; functions).

(include-book "dag-parent-array")
(include-book "dag-parent-array-with-name")
(include-book "make-dag-constant-alist")
(include-book "make-dag-variable-alist")

;;;
;;; make-dag-indices-aux
;;;

;returns (mv dag-parent-array dag-constant-alist dag-variable-alist)
;if we have the dag-lst in hand, consider calling add-nodes-to-dag-array to save the array refs into dag-array? no?
(defun make-dag-indices-aux (n ;counts up
                             dag-len dag-array-name dag-array
                             dag-parent-array-name
                             ;;these get populated:
                             dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :measure (nfix (+ 1 (- dag-len n)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dag-parent-arrayp dag-parent-array-name dag-parent-array) ;; nodes not yet assigned have the default value of nil
                              (natp n)
                              (<= n dag-len)
                              (<= dag-len (alen1 dag-parent-array-name dag-parent-array))
                              (alistp dag-constant-alist)
                              (alistp dag-variable-alist))))
  (if (or (>= n dag-len)
          (not (mbt (natp n)))
          (not (mbt (natp dag-len))))
      (mv dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((expr (aref1 dag-array-name dag-array n)))
      (if (atom expr) ;tests for variable
          (make-dag-indices-aux (+ 1 n) dag-len dag-array-name dag-array
                                dag-parent-array-name dag-parent-array
                                dag-constant-alist
                                (acons-fast expr n dag-variable-alist))
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn)
              (make-dag-indices-aux (+ 1 n) dag-len dag-array-name dag-array
                                    dag-parent-array-name dag-parent-array
                                    (acons-fast expr n dag-constant-alist)
                                    dag-variable-alist)
            ;;function call:
            (let* ((args (dargs expr)))
              (if (no-atoms args) ;check if there are any args that are nodenums
                  ;;if all args are quoteps, it counts as a "constant"
                  (make-dag-indices-aux (+ 1 n)
                                        dag-len dag-array-name dag-array
                                        dag-parent-array-name dag-parent-array
                                        (acons-fast expr n dag-constant-alist)
                                        dag-variable-alist)
                (make-dag-indices-aux (+ 1 n)
                                      dag-len dag-array-name dag-array
                                      dag-parent-array-name
                                      (add-to-parents-of-atoms-with-name args n dag-parent-array-name dag-parent-array)
                                      dag-constant-alist
                                      dag-variable-alist)))))))))

;consider enabling?
(defthmd mv-nth-0-of-make-dag-indices-aux
  (equal (mv-nth 0 (make-dag-indices-aux n dag-len dag-array-name dag-array dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
         (make-dag-parent-array-with-name-aux n dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len))
  :hints (("Goal" :expand (make-dag-parent-array-with-name-aux n dag-array-name
                                   dag-array dag-parent-array-name
                                   dag-parent-array dag-len)
           :in-theory (enable make-dag-indices-aux make-dag-parent-array-with-name-aux))))

;; We reason about make-dag-constant-alist-aux instead of make-dag-indices-aux, which is more complicated.
(defthm mv-nth-1-of-make-dag-indices-aux
  (equal (mv-nth 1 (make-dag-indices-aux n dag-len dag-array-name dag-array dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
         (make-dag-constant-alist-aux n dag-array-name dag-array dag-len dag-constant-alist))
  :hints (("Goal" :in-theory (enable make-dag-indices-aux make-dag-constant-alist-aux))))

;; We reason about make-dag-variable-alist-aux instead of make-dag-indices-aux, which is more complicated.
(defthm mv-nth-2-of-make-dag-indices-aux
  (equal (mv-nth 2 (make-dag-indices-aux n dag-len dag-array-name dag-array dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
         (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist))
  :hints (("Goal" :in-theory (enable make-dag-indices-aux make-dag-variable-alist-aux))))

(defthm dag-parent-arrayp-of-mv-nth-0-of-make-dag-indices-aux
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array)))
           (dag-parent-arrayp dag-parent-array-name
                              (mv-nth 0 (make-dag-indices-aux n dag-len dag-array-name dag-array dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))))

(defthm alen1-of-mv-nth-0-of-make-dag-indices-aux
  (implies (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))
           (equal (alen1 dag-parent-array-name (mv-nth 0 (make-dag-indices-aux n dag-len dag-array-name dag-array dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :in-theory (enable make-dag-indices-aux))))

(defthm bounded-dag-parent-entriesp-of-mv-nth-0-of-make-dag-indices-aux
  (implies (and (bounded-dag-parent-entriesp m ;(+ -1 dag-len)
                                             dag-parent-array-name
                                             dag-parent-array
                                             dag-len)
                (< m (alen1 dag-parent-array-name dag-parent-array))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array))
                (natp limit)
                (<= dag-len limit))
           (bounded-dag-parent-entriesp m ;(+ -1 dag-len)
                                        dag-parent-array-name
                                        (mv-nth 0 (make-dag-indices-aux n dag-len dag-array-name dag-array dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
                                        limit)))
;;;
;;; make-dag-indices
;;;

;returns (mv dag-parent-array dag-constant-alist dag-variable-alist)
;handles the bottommost DAG-LEN nodes in DAG-ARRAY.
(defund make-dag-indices (dag-array-name dag-array dag-parent-array-name dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (symbolp dag-parent-array-name))))
  (let* ((parent-array-len (max 1 dag-len)) ;arrays must have size at least 1  ;TODO: Consider using alen1 of the dag-array here, since wf-dagp requires that
         (dag-parent-array (make-empty-array dag-parent-array-name parent-array-len)))
    (make-dag-indices-aux 0
                          dag-len
                          dag-array-name dag-array
                          dag-parent-array-name dag-parent-array
                          nil         ;;empty dag-constant-alist
                          nil         ;;empty dag-variable-alist
                          )))

;; We reason about make-dag-parent-array-with-name instead of make-dag-indices, which is more complicated.
(defthm mv-nth-0-of-make-dag-indices
  (equal (mv-nth 0 (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len))
         (make-dag-parent-array-with-name dag-len dag-array-name dag-array dag-parent-array-name))
  :hints (("Goal" :in-theory (enable make-dag-indices make-dag-parent-array-with-name mv-nth-0-of-make-dag-indices-aux))))

;; We reason about make-dag-constant-alist instead of make-dag-indices, which is more complicated.
(defthm mv-nth-1-of-make-dag-indices
  (equal (mv-nth 1 (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len))
         (make-dag-constant-alist dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable make-dag-indices make-dag-constant-alist))))

;; We reason about make-dag-variable-alist instead of make-dag-indices, which is more complicated.
(defthm mv-nth-2-of-make-dag-indices
  (equal (mv-nth 2 (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len))
         (make-dag-variable-alist dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable make-dag-indices make-dag-variable-alist))))

;;;
;;; make-dag-indices-with-len
;;;

;returns (mv dag-parent-array dag-constant-alist dag-variable-alist)
;parent-array-len may be (should be for efficiency?) larger than dag-len?
(defund make-dag-indices-with-len (dag-array-name dag-array dag-parent-array-name dag-len parent-array-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (symbolp dag-parent-array-name)
                              (integerp parent-array-len)
                              (<= dag-len parent-array-len)
                              (<= parent-array-len 2147483646))))
  (let* ((parent-array-len (max 1 parent-array-len)) ;arrays must have size at least 1
         (dag-parent-array (make-empty-array dag-parent-array-name parent-array-len)))
    (make-dag-indices-aux 0 dag-len dag-array-name dag-array
                          dag-parent-array-name dag-parent-array
                          nil         ;;empty dag-constant-alist
                          nil         ;;empty dag-variable-alist
                          )))

;;note that here we pass the dag-len as the parent-array-len
(defthm mv-nth-0-of-make-dag-indices-with-len
  (equal (mv-nth 0 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len dag-len))
         (make-dag-parent-array-with-name dag-len dag-array-name dag-array dag-parent-array-name))
  :hints (("Goal" :in-theory (enable make-dag-indices-with-len make-dag-parent-array-with-name
                                     MV-NTH-0-OF-MAKE-DAG-INDICES-AUX))))

;; We reason about make-dag-constant-alist instead of make-dag-indices-with-len, which is more complicated.
(defthm mv-nth-1-of-make-dag-indices-with-len
  (equal (mv-nth 1 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len parent-array-len))
         (make-dag-constant-alist dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable make-dag-indices-with-len make-dag-constant-alist))))

;; We reason about make-dag-variable-alist instead of make-dag-indices-with-len, which is more complicated.
(defthm mv-nth-2-of-make-dag-indices-with-len
  (equal (mv-nth 2 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len parent-array-len))
         (make-dag-variable-alist dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable make-dag-indices-with-len make-dag-variable-alist))))

(defthm alen1-of-mv-nth-0-of-make-dag-indices-with-len
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
 ;               (posp dag-len)
                (symbolp dag-parent-array-name)
                (posp parent-array-len)
                (<= parent-array-len 2147483646))
           (equal (alen1 dag-parent-array-name (mv-nth 0 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len parent-array-len)))
                  parent-array-len))
  :hints (("Goal" :in-theory (enable make-dag-indices-with-len pseudo-dag-arrayp))))

(defthm dag-parent-arrayp-of-mv-nth-0-of-make-dag-indices-with-len
  (implies (and (natp dag-len)
                (<= dag-len parent-array-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name)
                (posp parent-array-len)
                (<= parent-array-len 2147483646))
           (dag-parent-arrayp dag-parent-array-name
                              (mv-nth 0 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len parent-array-len))))
  :hints (("Goal" :in-theory (enable make-dag-indices-with-len pseudo-dag-arrayp))))

(defthm bounded-dag-parent-entriesp-of-mv-nth-0-of-make-dag-indices-with-len
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name)
                (natp dag-len)
                (natp limit)
                (<= dag-len limit)
                (<= dag-len parent-array-len)
                (posp parent-array-len)
                (< parent-array-len 2147483647)
                (natp m)
                (< m parent-array-len)
                )
           (bounded-dag-parent-entriesp m ;(+ -1 dag-len)
                                        dag-parent-array-name
                                        (mv-nth 0 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len parent-array-len))
                                        limit))
  :hints (("Goal" :in-theory (enable make-dag-indices-with-len))))

(defthm bounded-dag-parent-arrayp-of-mv-nth-0-of-make-dag-indices-with-len
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name)
                ;; (posp dag-len)
                (<= dag-len parent-array-len)
                (posp parent-array-len)
                (<= parent-array-len 2147483646))
           (bounded-dag-parent-arrayp dag-parent-array-name
                               (mv-nth 0 (make-dag-indices-with-len dag-array-name dag-array dag-parent-array-name dag-len parent-array-len))
                               dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))
