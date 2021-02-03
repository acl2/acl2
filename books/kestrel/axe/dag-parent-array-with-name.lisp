; More general variant of parent-arrray.lisp
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

(include-book "dag-parent-array") ;todo

;;;
;;; find-shortest-parent-lst-with-name
;;;

;todo: put the name param earlier
(defund find-shortest-parent-lst-with-name (current-shortest-lst items dag-parent-array dag-parent-array-name)
  (declare (xargs :guard (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                              (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array))
                              (true-listp items)
                              (true-listp current-shortest-lst))
                  :guard-hints (("Goal" :in-theory (enable dag-parent-arrayp)))))
  (if (endp items)
      current-shortest-lst
    (let ((item (car items)))
      (if (not (atom item)) ;skip quoteps
          (find-shortest-parent-lst-with-name current-shortest-lst (cdr items) dag-parent-array dag-parent-array-name)
        ;; it's a nodenum
        (let* ((new-lst (aref1 dag-parent-array-name dag-parent-array item)))
          (find-shortest-parent-lst-with-name (shorter-lst current-shortest-lst
                                                           new-lst
                                                           current-shortest-lst
                                                           new-lst)
                                              (cdr items)
                                              dag-parent-array
                                              dag-parent-array-name))))))

(defthm true-listp-of-find-shortest-parent-lst-with-name
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (true-listp current-shortest-lst)
                (all-dargp items))
           (true-listp (find-shortest-parent-lst-with-name current-shortest-lst items dag-parent-array dag-parent-array-name)))
  :hints (("Goal" :in-theory (enable find-shortest-parent-lst-with-name))))

(defthm nat-listp-of-find-shortest-parent-lst-with-name
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (nat-listp current-shortest-lst)
                (all-dargp items))
           (nat-listp (find-shortest-parent-lst-with-name current-shortest-lst items dag-parent-array dag-parent-array-name)))
  :hints (("Goal" :in-theory (enable find-shortest-parent-lst-with-name))))

(defthm all-<-of-find-shortest-parent-lst-with-name
  (implies (and (all-< current-shortest-lst limit)
                (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit)
                (all-dargp-less-than items (+ 1 n))
                (integerp n))
           (all-< (find-shortest-parent-lst-with-name current-shortest-lst items dag-parent-array dag-parent-array-name)
                  limit))
  :hints (("Goal" :in-theory (enable find-shortest-parent-lst-with-name))))

;;;
;;; find-matching-node-with-name
;;;

;; todo: make this more similar to find-matching-node?
;; returns the nodenum from NODENUMS at which (cons fn args) exists (if any), otherwise nil
(defund find-matching-node-with-name (fn args nodenums dag-array dag-array-name dag-len)
  (declare (xargs :guard (and (symbolp fn)
                              (not (equal 'quote fn))
                              ;(array1p dag-array-name dag-array)
                              (nat-listp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums dag-len))))
  (if (endp nodenums)
      nil
    (let* ((nodenum (first nodenums))
           (expr (aref1 dag-array-name dag-array nodenum)))
      (if (and (consp expr) ;; TODO: Drop this check (maybe add a type decl) since the expr is always a cons?
               (eq fn (ffn-symb expr))
               (equal args (dargs expr)))
          nodenum
        (find-matching-node-with-name fn args (rest nodenums) dag-array dag-array-name dag-len)))))

(defthm integerp-of-find-matching-node-with-name
  (implies (nat-listp nodenums)
           (iff (integerp (find-matching-node-with-name fn args nodenums dag-array dag-array-name dag-len))
                (find-matching-node-with-name fn args nodenums dag-array dag-array-name dag-len)))
  :hints (("Goal" :in-theory (enable find-matching-node-with-name))))

(defthm nonneg-of-find-matching-node-with-name
  (implies (nat-listp nodenums)
           (<= 0 (find-matching-node-with-name fn args nodenums dag-array dag-array-name dag-len)))
  :hints (("Goal" :in-theory (enable find-matching-node-with-name))))

(defthm <-of-find-matching-node-with-name
  (implies (and (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (natp dag-len)
       ;         (array1p dag-array-name dag-array)
                (nat-listp nodenums)
                (true-listp nodenums)
                (all-< nodenums dag-len ;(alen1 'dag-array dag-array)
                       )
                (find-matching-node-with-name fn args nodenums dag-array dag-array-name dag-len))
           (< (find-matching-node-with-name fn args nodenums dag-array dag-array-name dag-len)
              dag-len))
  :hints (("Goal" :in-theory (enable find-matching-node-with-name))))

;;;
;;; find-expr-using-parents-with-name
;;;

(defund find-expr-using-parents-with-name (fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              (not (no-atoms args))
                              (symbolp fn)
                              (not (equal 'quote fn))
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (symbolp dag-parent-array-name)
                              (symbolp dag-array-name)
                              (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                              (all-dargp-less-than args dag-len)
                              (equal (alen1 dag-array-name dag-array)
                                     (alen1 dag-parent-array-name dag-parent-array))
                              (<= dag-len (alen1 dag-array-name dag-array)))
                  :guard-hints (("Goal" :use (:instance all-<-of-find-shortest-parent-lst-with-name
                                                        (limit dag-len)
                                                        (dag-parent-array dag-parent-array)
                                                        (items (mv-nth 1 (first-atom args)))
                                                        (current-shortest-lst
                                                         (aref1 dag-parent-array-name
                                                                dag-parent-array
                                                                (mv-nth 0 (first-atom args))))
                                                        (n (+ -1 (alen1 dag-array-name dag-array))))
                                 :in-theory (e/d (<-of-+-of-minus1-arith-hack bounded-dag-parent-arrayp)
                                                 (all-<-of-find-shortest-parent-lst-with-name))))))
  (mv-let (first-node-child rest)
    (first-atom args)
    (let ((parents (find-shortest-parent-lst-with-name
                    (aref1 dag-parent-array-name dag-parent-array first-node-child)
                    rest
                    dag-parent-array
                    dag-parent-array-name
                    )))
      (find-matching-node-with-name fn args parents dag-array dag-array-name dag-len))))

(defthm integerp-of-find-expr-using-parents-with-name
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (all-dargp args)
                (not (no-atoms args)))
           (iff (integerp (find-expr-using-parents-with-name fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len))
                (find-expr-using-parents-with-name fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len)))
  :hints (("Goal" :in-theory (enable find-expr-using-parents-with-name))))

(defthm nonneg-of-find-expr-using-parents-with-name
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (not (no-atoms args)))
           (<= 0 (find-expr-using-parents-with-name fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len)))
  :hints (("Goal" :in-theory (enable find-expr-using-parents-with-name))))

(defthm <-of-find-expr-using-parents-with-name
  (implies (and (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (not (no-atoms args))
                (all-dargp-less-than args (alen1 dag-array-name dag-array))
                (natp dag-len)
                (equal (alen1 dag-array-name dag-array)
                       (alen1 dag-parent-array-name dag-parent-array))
                (find-expr-using-parents-with-name fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len))
           (< (find-expr-using-parents-with-name fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len) dag-len))
  :hints (("Goal"
           :use ((:instance all-<-of-aref1-when-bounded-dag-parent-entriesp
                            (limit2 dag-len)
                            (limit dag-len)
                            (n (mv-nth 0 (first-atom args)))
                            (dag-parent-array dag-parent-array)
                            (dag-parent-array-name dag-parent-array-name))
                 (:instance all-<-of-find-shortest-parent-lst-with-name
                            (n (+ -1 (alen1 dag-array-name dag-array)))
                            (limit dag-len)
                            (dag-parent-array dag-parent-array)
                            (items (mv-nth 1 (first-atom args)))
                            (current-shortest-lst
                             (aref1 dag-parent-array-name
                                    dag-parent-array
                                    (mv-nth 0 (first-atom args)))))
                 (:instance <-of-find-matching-node-with-name
                            (dag-len dag-len)
                            (dag-array dag-array)
                            (nodenums (find-shortest-parent-lst-with-name
                                       (aref1 dag-parent-array-name
                                              dag-parent-array
                                              (mv-nth 0 (first-atom args)))
                                       (mv-nth 1 (first-atom args))
                                       dag-parent-array
                                       dag-parent-array-name))
                            (dag-parent-array-name dag-parent-array-name)
                            ))
           :in-theory (e/d (bounded-dag-parent-arrayp
                            find-expr-using-parents-with-name)
                           (all-<-of-find-shortest-parent-lst-with-name
                            <-of-find-matching-node-with-name)))))

;;;
;;; add-to-parents-of-atoms-with-name
;;;

;;add NODENUM to the parents lists for those ITEMS which are not quoteps
(defund add-to-parents-of-atoms-with-name (items nodenum dag-parent-array-name dag-parent-array)
  (declare (xargs :guard (and (true-listp items)
                              (natp nodenum)
                              (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                              (all-dargp-less-than items nodenum)
                              (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array)))))
  (if (endp items)
      dag-parent-array
    (let ((item (first items)))
      (if (atom item) ;it's a nodenum, not a quotep:
          (let* ((old-parents (aref1 dag-parent-array-name dag-parent-array item))
                 (new-parents (cons ;add-to-set-eql ;i think it's okay to just use cons here, since the nodenum being added is a new node in the dag (so it shouldn't already be among the parents) ;ffixme think...
                               nodenum old-parents)))
            (add-to-parents-of-atoms-with-name (rest items)
                                               nodenum
                                               dag-parent-array-name
                                               (aset1 dag-parent-array-name dag-parent-array item new-parents)))
        ;;it's a quotep:
        (add-to-parents-of-atoms-with-name (rest items) nodenum dag-parent-array-name dag-parent-array)))))

(defthm add-to-parents-of-atoms-with-name-when-no-atoms
  (implies (no-atoms items)
           (equal (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array)
                  dag-parent-array))
  :hints (("Goal" :in-theory (enable no-atoms add-to-parents-of-atoms-with-name))))

(defthm array1p-of-add-to-parents-of-atoms-with-name
  (implies (and (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array))
                ;;(all-dargp items)
                (natp nodenum)
                ;;(<= nodenum top-nodenum-to-check)
                (array1p dag-parent-array-name dag-parent-array))
           (array1p dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp add-to-parents-of-atoms-with-name integer-listp))))

(defthm default-of-add-to-parents-of-atoms-with-name
  (implies (and (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array))
                ;(all-dargp items)
                (natp nodenum)
                ;(<= nodenum top-nodenum-to-check)
                (array1p dag-parent-array-name dag-parent-array))
           (equal (default dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array))
                  (default dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp add-to-parents-of-atoms-with-name integer-listp))))

(defthm alen1-of-add-to-parents-of-atoms-with-name
  (implies (all-dargp items) ;(natp nodenum)
           (equal (alen1 dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array))
                  (alen1 dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :in-theory (enable add-to-parents-of-atoms-with-name integer-listp))))

(defthm all-dag-parent-entriesp-of-add-to-parents-of-atoms-with-name
  (implies (and (all-dargp-less-than items nodenum)
                (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array))
                (natp nodenum)
                (integerp n)
                (array1p dag-parent-array-name dag-parent-array)
                ;(< nodenum (alen1 dag-parent-array-name dag-parent-array))
                (< n (alen1 dag-parent-array-name dag-parent-array))
                (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array))
           (all-dag-parent-entriesp n dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array)))
  :hints (("Subgoal *1/6" :cases ((< n (car items))))
          ("Goal" :in-theory (enable add-to-parents-of-atoms-with-name integer-listp
                                     <-of-car-when-all-dargp-less-than
                                     not-<-of-car-when-all-dargp-less-than))))

(defthm dag-parent-arrayp-of-add-to-parents-of-atoms-with-name
  (implies (and (all-dargp-less-than items nodenum)
                (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array))
                ;(all-dargp items)
                (natp nodenum)
                ;;(<= nodenum top-nodenum-to-check)
                ;(< nodenum (alen1 dag-parent-array-name dag-parent-array))
                (dag-parent-arrayp dag-parent-array-name dag-parent-array))
           (dag-parent-arrayp dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp add-to-parents-of-atoms-with-name integer-listp))))

(defthm all-<-of-aref1-of-add-to-parents-of-atoms-with-name
  (implies (and (natp n)
                (natp nodenum)
                (array1p dag-parent-array-name dag-parent-array)
                (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array))
                (< n (alen1 dag-parent-array-name dag-parent-array))
                (< nodenum limit)
                (all-< (aref1 dag-parent-array-name dag-parent-array n) limit))
           (all-< (aref1 dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array) n) limit))
  :hints (("Goal" :in-theory (enable add-to-parents-of-atoms-with-name))))

(defthm bounded-dag-parent-entriesp-of-add-to-parents-of-atoms-with-name
  (implies (and (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit)
                (natp nodenum)
                (< nodenum limit)
                (natp limit)
                (array1p dag-parent-array-name dag-parent-array)
                (< n (alen1 dag-parent-array-name dag-parent-array))
                (all-dargp-less-than items (alen1 dag-parent-array-name dag-parent-array)))
           (bounded-dag-parent-entriesp n dag-parent-array-name (add-to-parents-of-atoms-with-name items nodenum dag-parent-array-name dag-parent-array) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-entriesp))))

;;;
;;; make-dag-parent-array-with-name-aux
;;;

;the parent array pairs each nodenum with a list of the nodenums of its parents
;fixme use this more when we call make-dag-indices but then only use the parent array!
;todo: add -with-name to the name and make a simpler version
(defund make-dag-parent-array-with-name-aux (n dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len)
  (declare (xargs :measure (nfix (+ 1 (- dag-len n)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp n)
                              (<= n dag-len)
                              (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                              (<= dag-len (alen1 dag-parent-array-name dag-parent-array)))))
  (if (or (>= n dag-len)
          (not (mbt (natp n)))
          (not (mbt (natp dag-len))))
      dag-parent-array
    (let ((expr (aref1 dag-array-name dag-array n)))
      (if (or (variablep expr)
              (fquotep expr))
          (make-dag-parent-array-with-name-aux (+ 1 n) dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len)
        ;;function call (add this node to the parent lists of all its children):
        (make-dag-parent-array-with-name-aux (+ 1 n) dag-array-name
                               dag-array
                               dag-parent-array-name
                               (add-to-parents-of-atoms-with-name (dargs expr) n dag-parent-array-name dag-parent-array)
                               dag-len)))))

(defthm alen1-of-make-dag-parent-array-with-name-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array)))
           (equal (alen1 dag-parent-array-name (make-dag-parent-array-with-name-aux n dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len))
                  (alen1 dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :in-theory (enable make-dag-parent-array-with-name-aux))))

(defthm dag-parent-arrayp-of-make-dag-parent-array-with-name-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array)))
           (dag-parent-arrayp dag-parent-array-name (make-dag-parent-array-with-name-aux n dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len)))
  :hints (("Goal" :in-theory (enable make-dag-parent-array-with-name-aux)
           :expand (make-dag-parent-array-with-name-aux 0 dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len))))

(defthm bounded-dag-parent-entriesp-of-make-dag-parent-array-with-name-aux
  (implies (and (bounded-dag-parent-entriesp m ;(+ -1 dag-len)
                                             dag-parent-array-name
                                             dag-parent-array
                                             dag-len)
                (< m (alen1 dag-parent-array-name dag-parent-array))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array))
                (natp m)
                (<= dag-len limit))
           (bounded-dag-parent-entriesp m ;(+ -1 dag-len)
                                        dag-parent-array-name
                                        (make-dag-parent-array-with-name-aux n dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len)
                                        limit))
  :hints (("Goal" :in-theory (enable make-dag-parent-array-with-name-aux))))

;;;
;;; make-dag-parent-array-with-name
;;;

;; This makes the shortest possible parent-array for dag-array, but its alen1 may not match the alen1 of the dag-array.
;rename to make-minimal-dag-parent-array?
(defund make-dag-parent-array-with-name (dag-len dag-array-name dag-array dag-parent-array-name)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (symbolp dag-parent-array-name))))
  (let* ((parent-array-len (max 1 dag-len)) ;arrays must have size at least 1
         ;; The :default value is nil:
         (dag-parent-array (make-empty-array dag-parent-array-name parent-array-len)))
    (make-dag-parent-array-with-name-aux 0 dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len)))

(defthm dag-parent-arrayp-of-make-dag-parent-array-with-name
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name))
           (dag-parent-arrayp dag-parent-array-name (make-dag-parent-array-with-name dag-len dag-array-name dag-array dag-parent-array-name)))
  :hints (("Goal" :cases (< dag-len 1)
           :in-theory (enable make-dag-parent-array-with-name))))

(defthm alen1-of-make-dag-parent-array-with-name
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name))
           (equal (alen1 dag-parent-array-name (make-dag-parent-array-with-name dag-len dag-array-name dag-array dag-parent-array-name))
                  (max 1 dag-len)))
  :hints (("Goal" :in-theory (enable make-dag-parent-array-with-name))))

(defthm bounded-dag-parent-entriesp-of-make-dag-parent-array-with-name
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name)
                (natp limit)
                (<= dag-len limit)
                (natp m)
                (< m dag-len))
           (bounded-dag-parent-entriesp m
                                        dag-parent-array-name
                                        (make-dag-parent-array-with-name dag-len dag-array-name dag-array dag-parent-array-name)
                                        limit))
  :hints (("Goal" :cases ((equal dag-len 0))
           :in-theory (enable make-dag-parent-array-with-name))))

(defthm bounded-dag-parent-arrayp-of-make-dag-parent-array-with-name
  (implies (and (< 0 dag-len) ;why?
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name))
           (bounded-dag-parent-arrayp dag-parent-array-name
                               (make-dag-parent-array-with-name dag-len dag-array-name dag-array dag-parent-array-name)
                               dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))

;;;
;;; make-dag-parent-array-with-name2
;;;

;; This causes the alen1 of the result to match the alen1 of dag-array, which is often required.
(defund make-dag-parent-array-with-name2 (dag-len dag-array-name dag-array dag-parent-array-name)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (symbolp dag-parent-array-name))))
  (let* (;; The :default value is nil:
         (dag-parent-array (make-empty-array dag-parent-array-name (alen1 dag-array-name dag-array))))
    (make-dag-parent-array-with-name-aux 0 dag-array-name dag-array dag-parent-array-name dag-parent-array dag-len)))

(defthm dag-parent-arrayp-of-make-dag-parent-array-with-name2
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name))
           (dag-parent-arrayp dag-parent-array-name (make-dag-parent-array-with-name2 dag-len dag-array-name dag-array dag-parent-array-name)))
  :hints (("Goal" :cases (< dag-len 1)
           :in-theory (enable make-dag-parent-array-with-name2))))

(defthm alen1-of-make-dag-parent-array-with-name2
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name))
           (equal (alen1 dag-parent-array-name (make-dag-parent-array-with-name2 dag-len dag-array-name dag-array dag-parent-array-name))
                  (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable make-dag-parent-array-with-name2))))

(defthm bounded-dag-parent-entriesp-of-make-dag-parent-array-with-name2
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name)
                (natp limit)
                (<= dag-len limit)
                (natp m)
                (< m (alen1 dag-array-name dag-array)))
           (bounded-dag-parent-entriesp m
                                        dag-parent-array-name
                                        (make-dag-parent-array-with-name2 dag-len dag-array-name dag-array dag-parent-array-name)
                                        limit))
  :hints (("Goal" :cases ((equal dag-len 0))
           :in-theory (enable make-dag-parent-array-with-name2))))

;move
(defthm pseudo-dag-arrayp-forward-chaining-another-2
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (integerp (alen1 dag-array-name dag-array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm bounded-dag-parent-arrayp-of-make-dag-parent-array-with-name2
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (symbolp dag-parent-array-name))
           (bounded-dag-parent-arrayp dag-parent-array-name
                                      (make-dag-parent-array-with-name2 dag-len dag-array-name dag-array dag-parent-array-name)
                                      dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))
