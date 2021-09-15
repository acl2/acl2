; Replacing a node in a DAG
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

(include-book "kestrel/axe/dag-arrays" :dir :system)

;; ;ffffixme if this makes the parent into a ground term, it should be added to the dag-constant-alist?!
;; (defun change-mentions-of-nodenum2 (nodenum new-nodenum-or-quotep parent-nodenums miter-array-name miter-array)
;;   (if (endp parent-nodenums)
;;       miter-array
;;     (let* ((parent-nodenum (first parent-nodenums))
;;            (expr (aref1 miter-array-name miter-array parent-nodenum)) ;we know this is a function call, because this node is a parent of nodenum?
;;            )
;;       (if (or (atom expr)
;;               (fquotep expr))
;;           (hard-error 'change-mentions-of-nodenum2 "bad expr." nil)
;;         (change-mentions-of-nodenum2 nodenum new-nodenum-or-quotep (rest parent-nodenums) miter-array-name
;;                                      (aset1-safe miter-array-name miter-array parent-nodenum (cons (ffn-symb expr)
;;                                                                                               (fixup-args3 nodenum new-nodenum-or-quotep (dargs expr)))))))))

;; (skip- proofs (verify-guards change-mentions-of-nodenum2))

;is this just a replace function (replace-eql?)?
(defund fixup-args3  (target      ;should be an integer (a nodenum)
                     replacement ;can be a nodenum or quotep
                     lst)
  (declare (xargs :guard (and (true-listp lst)
                              (EQLABLEP TARGET))))
  (if (endp lst)
      nil
    (let ((item (car lst)))
      (if (eql item target)
          (cons replacement (fixup-args3 target replacement (cdr lst)))
        (cons item (fixup-args3 target replacement (cdr lst)))))))

(defthm all-dargp-less-than-of-fixup-args3
  (implies (and (all-dargp-less-than dargs n)
                (natp new-nodenum)
                (force (implies (member-equal old-nodenum dargs)
                                (< new-nodenum n))))
           (all-dargp-less-than (fixup-args3 old-nodenum new-nodenum dargs) n))
  :hints (("Goal" :in-theory (enable  fixup-args3))))

(local (in-theory (enable pseudo-dag-arrayp))) ;todo

;(local (in-theory (enable MEMBER-EQUAL-BECOMES-MEMBERP)))

;ffixme this could be slow? see the version using parent pointers (but got weird, non-deterministic crashes)
;counts up from n
(defun change-mentions-of-nodenum (n dag-len old-nodenum new-nodenum dag-array-name dag-array)
  (declare (xargs :measure (+ 1 (nfix (- dag-len n)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp old-nodenum)
                              (natp new-nodenum)
                              (natp n)
                              (<= n dag-len)
                              (NOT (< '2147483645 N))
                              (<= dag-len 2147483645)
                              (<= new-nodenum old-nodenum))
                  :guard-hints (("Goal" :use (:instance <-when-member-equal-of-dargs-of-aref1
                                                        (darg OLD-NODENUM)
                                                        (nodenum n))))))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp dag-len)))
          (>= n dag-len))
      dag-array
    (let ((expr (aref1 dag-array-name dag-array n)))
      (if (or (variablep expr)
              (fquotep expr))
          (change-mentions-of-nodenum (+ 1 n) dag-len old-nodenum new-nodenum dag-array-name dag-array)
        (let ((args (dargs expr)))
          (if (member old-nodenum args)
              (change-mentions-of-nodenum (+ 1 n) dag-len old-nodenum new-nodenum
                                          dag-array-name
                                          (aset1 dag-array-name
                                                 dag-array
                                                 n
                                                 (cons (ffn-symb expr)
                                                       (fixup-args3 old-nodenum
                                                                    new-nodenum
                                                                    args))))
            (change-mentions-of-nodenum (+ 1 n) dag-len old-nodenum new-nodenum dag-array-name dag-array)))))))

;; ;ffffffixme if we are replacing a node with a child (did i mean, "with a constant"?), perhaps its parent will become a ground term!
;; ;; Returns (mv dag-array parent-array)
;; ;new-nodenum must be less than old-nodenum, to preserve node ordering..
;; (defun replace-node (old-nodenum new-nodenum dag-array-name dag-array parent-array-name parent-array)
;;   (let* ((old-nodenum-expr (aref1 dag-array-name dag-array old-nodenum)) ;pass in if available?
;;          ;;putting in the special constant :removed (so the old-nodenum no longer has children, so we can remove it from the parent lists of its former children):
;;          (dag-array (aset1-safe dag-array-name dag-array old-nodenum (enquote :removed))) ;fffixme add to dag-constant-alist?
;;          ;;remove old-nodenum from the parent lists of its former children (if any): - fffixme could lead to orphans? set them to :removed too?
;;          (parent-array (if (and (consp old-nodenum-expr) ;checks that it's not a variable
;;                                 (not (eq 'quote (ffn-symb old-nodenum-expr))) ;is this case an error?
;;                                 )
;;                            (drop-parent-relationships old-nodenum (dargs old-nodenum-expr) parent-array-name parent-array)
;;                          parent-array))

;;          (old-nodenum-parents (aref1 parent-array-name parent-array old-nodenum))
;;          (dag-array (change-mentions-of-nodenum2 old-nodenum
;;                                                  new-nodenum
;;                                                  old-nodenum-parents
;;                                                  dag-array-name
;;                                                  dag-array))
;;          (parent-array (aset1-safe parent-array-name parent-array old-nodenum nil)) ;or don't bother since it was spliced out? (maybe needed to ensure a well-formed dag?)
;;          (new-nodenum-parents (aref1 parent-array-name parent-array new-nodenum))
;;          (new-nodenum-new-parents (union$ old-nodenum-parents new-nodenum-parents))
;;          (parent-array (aset1-safe parent-array-name parent-array new-nodenum new-nodenum-new-parents))
;;          )
;;     (mv dag-array parent-array)))

;; (skip- proofs (verify-guards replace-node))

;this one does not deal with parents (see the above one, which does), because we got weird crashes with non-true-list parent lists...
;; Returns dag-array
;; the old-nodenum should be larger to ensure that the resulting dag is well-formed
(defun replace-node (old-nodenum new-nodenum dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp old-nodenum)
                              (natp new-nodenum)
                              (<= dag-len 2147483645)
                              (<= new-nodenum old-nodenum)
                              (< old-nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (enable bounded-dag-exprp-when-myquotep)))))
  (let* ( ;; we could perhaps remove some child nodes as well:
         (dag-array (aset1 dag-array-name dag-array old-nodenum (enquote :removed))) ;fffixme add to dag-constant-alist?
         (dag-array (change-mentions-of-nodenum (+ 1 old-nodenum) dag-len old-nodenum new-nodenum dag-array-name dag-array)))
    dag-array))
