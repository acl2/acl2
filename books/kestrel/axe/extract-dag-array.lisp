; Extracting parts of DAG arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/supporting-nodes" :dir :system)

;move the indicated nodes (fixed up as needed) from old-dag-array to new-dag-array
;tag-array tells us which nodes to keep
;returns (mv new-dag-array-len new-dag-array translation-array)
;uses the array named TRANSLATION-ARRAY-NAME - what else?
;TODO: compare to build-reduced-dag2, except this one returns an array
;todo: avoid making a node that is a quotep?
;; We do not use the standard functions to add nodes to dags because we are just shifting and dropping nodes.
(defun extract-dag-array-aux (old-dag-nodenum dag-len old-dag-len old-dag-array-name old-dag-array
                                              dag-array-name dag-array
                                              tag-array
                                              translation-array)
  (declare (xargs :measure (nfix (+ 1 (- old-dag-len old-dag-nodenum)))
                  :guard (and (natp old-dag-nodenum)
                              (natp old-dag-len)
                              (natp dag-len)
                              (<= dag-len old-dag-nodenum) ;some nodes may be dropped
                              (array1p 'translation-array translation-array)
                              (equal (alen1 'translation-array translation-array) old-dag-len)
                              (array1p 'tag-array tag-array)
                              (equal (alen1 'tag-array tag-array) old-dag-len)
                              (pseudo-dag-arrayp old-dag-array-name old-dag-array old-dag-len)
                              (array1p dag-array-name dag-array)
                              (equal (alen1 dag-array-name dag-array)
                                     old-dag-len)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))))
  (if (or (>= old-dag-nodenum old-dag-len)
          (not (mbt (natp old-dag-nodenum)))
          (not (mbt (natp old-dag-len))))
      (mv dag-len dag-array translation-array)
    (let ((tag (aref1 'tag-array tag-array old-dag-nodenum)))
      (if (not tag)
          ;; we are to omit this node:
          (extract-dag-array-aux (+ 1 old-dag-nodenum) dag-len old-dag-len old-dag-array-name old-dag-array dag-array-name dag-array tag-array translation-array)
        ;;we are to keep this node:
        (let* ((expr (aref1 old-dag-array-name old-dag-array old-dag-nodenum))
               (expr (if (or (variablep expr)
                             (fquotep expr)) ;avoid inlining quoteps? but then the translation-array might give back a quotep...
                         expr
                       (let* ((fn (ffn-symb expr))
                              (args (dargs expr))
                              ;;could we use something like adjust-nodneums-down2?
                              (args (translate-args args translation-array)))
                         (cons fn args)))))
          (extract-dag-array-aux (+ 1 old-dag-nodenum)
                                 (+ 1 dag-len)
                                 old-dag-len
                                 old-dag-array-name
                                 old-dag-array
                                 dag-array-name
                                 (aset1 dag-array-name dag-array dag-len expr)
                                 tag-array
                                 (aset1 'translation-array translation-array old-dag-nodenum dag-len)))))))

;extracts the nodes that support NODENUMS
;smashes the arrays named 'translation-array and 'tag-array
;returns (mv new-dag-array new-dag-len translation-array)
;faster way to do this?
;todo: compare to drop-non-supporters
(defun extract-dag-array (nodenums ;must not be empty
                          dag-array-name dag-array dag-len
                          new-dag-array-name)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (consp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums dag-len)
                              (symbolp new-dag-array-name)))
           (ignore dag-len))
  (let* ((max-nodenum (maxelem nodenums))
         (relevant-dag-length (+ 1 max-nodenum))
         ;; TODO: Call tag-supporters-of-nodes here (but avoid computing the max twice):
         (tag-array (make-empty-array 'tag-array relevant-dag-length)) ;okay to use this name?
         (tag-array (aset1-list 'tag-array tag-array nodenums t))
         (tag-array (tag-supporters max-nodenum dag-array-name dag-array 'tag-array tag-array))
         (new-dag-array (make-empty-array new-dag-array-name relevant-dag-length)) ;probably won't need all the space?
         (translation-array (make-empty-array 'translation-array relevant-dag-length)))
    (mv-let (new-dag-len new-dag-array translation-array)
            (extract-dag-array-aux 0 0 relevant-dag-length dag-array-name dag-array new-dag-array-name new-dag-array tag-array translation-array)
            (mv new-dag-array new-dag-len translation-array))))
