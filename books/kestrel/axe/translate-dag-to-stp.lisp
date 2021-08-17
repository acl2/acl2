; Creating STP queries from DAGs
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

;fixme use an array instead of nodenum-type-alist everywhere?

;; I have found that is it much faster to write a bunch of strings to a file
;; than to append them all into one big string and write it to a file (at least
;; on Allegro and CCL).  So this file uses string-trees to represent things to
;; be printed to files.
;;
;; This is very fast:
;; (time$ (write-strings-to-file! (repeat 1000000 "foo") "/tmp/foo" 'ctx state))
;; but this takes superlinear time:
;; (defun string-append-all (strs acc) (if (endp strs) acc (string-append-all (rest strs) (string-append (first strs) acc))))
;; (time$ (len (string-append-all (repeat 10000 "foo") "")))
;; (time$ (len (string-append-all (repeat 20000 "foo") "")))
;; (time$ (len (string-append-all (repeat 30000 "foo") "")))
;; as does this:
;; (defun string-append-all2 (strs acc) (if (endp strs) acc (string-append-all2 (rest strs) (string-append acc (first strs)))))
;; (time$ (len (string-append-all2 (repeat 10000 "foo") "")))
;; (time$ (len (string-append-all2 (repeat 20000 "foo") "")))
;; (time$ (len (string-append-all2 (repeat 30000 "foo") "")))

; TODO: Consider adding support for array terms that are if-then-else nests.

; TODO: Consider adding support for if/myif in addition to bvif.

;The only variables appearing in the translated file should be of the forms NODE<num> or ARRAY<num>.  Even if, say, node 100 is the variable x, it is translated as the variable NODE100.  This should prevent any variable name clashes.
;FIXME could put in the real names of true input vars in comments?

;do we handle range types correctly everywhere?

;; See https://stp.readthedocs.io/en/latest/.

;; TODO: Consider doing all trimming, and perhaps even padding, using rewriting
;; in a separate pass before calling the STP translation code.

;(include-book "dag-arrays")
(include-book "depth-array")
(include-book "stp-counterexamples") ;brings in a bunch of the defs of bv functions...
(include-book "kestrel/bv-lists/bv-arrays" :dir :system) ; for bv-array-if
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(include-book "kestrel/utilities/file-io-string-trees" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/file-io-light/write-strings-to-file-bang" :dir :system) ;; todo reduce, just used to clear a file
(in-theory (disable revappend-removal)) ;caused problems (though this may be a better approach to adopt someday)
(include-book "kestrel/bv/defs" :dir :system) ;todo: make sure this book includes the definitions of all functions it translates.
(include-book "kestrel/bv/getbit-def" :dir :system)
(include-book "call-axe-script")
(include-book "safe-unquote") ; drop?
(include-book "axe-syntax-functions-bv") ;for get-type-of-bv-expr-axe, todo reduce
(include-book "kestrel/utilities/strings" :dir :system)
(include-book "kestrel/utilities/temp-dirs" :dir :system)
(include-book "conjunctions-and-disjunctions") ;for possibly-negated-nodenumsp
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system)) ;for character-listp-of-take
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))

(in-theory (disable open-output-channels open-output-channel-p1))

(local (in-theory (enable <-of-+-of-1-when-integers)))

;; (defthm equal-of-len-forward-to-cons
;;   (implies (and (equal k (len x))
;;                 (posp k))
;;            (consp x))
;;   :rule-classes :forward-chaining)

(defthm integerp-of-if
  (equal (integerp (if test tp ep))
         (if test
             (integerp tp)
           (integerp ep))))

(in-theory (disable (:e nat-to-string))) ;to avoid errors being printed in proofs

;dup
(defund unquote-if-possible (x)
  (declare (xargs :guard t))
  (if (and (quotep x)
           (consp (cdr x)))
      (unquote x)
    nil))

;(in-theory (disable string-append-lst)) ;move
;(in-theory (disable bounded-dag-exprp)) ;move?

(local (in-theory (disable string-append
                           ;LIST::EQUAL-CONS-CASES
                           alistp nat-listp ;don't induct on these
                           ;list::len-when-at-most-1
                           CONSP-FROM-LEN-CHEAP
                           ;LIST::LEN-OF-NON-CONSP
                           )))

;; Justifies the correctness of the translation
(defthm equality-of-zero-length-arrays
  (implies (and (bv-arrayp width1 0 x)
                (bv-arrayp width2 0 y))
           (equal x y))
  :rule-classes nil)

;drop? ;dup
(defthm character-listp-of-reverse-list
  (implies (character-listp l)
           (character-listp (reverse-list l)))
  :hints (("Goal" :in-theory (enable character-listp reverse-list))))


;fixme are there other functions like this to deprecate?
;returns a type or nil (if we could not determine the type)
;should some of the nil cases here be errors or warnings?
;fixme handle tuples?
;the args are nodenums or quoteps - we don't deref nodenums that may point to quoteps
;fixme make sure all callers of this handle nil okay (would it ever be better to throw an error?)?
;what if the number of arguments is wrong?
;; TODO: Consider adding support for constant arrays
;; TODO: Exclude FN from being 'QUOTE?
(defund get-type-of-expr (fn args)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args))))
  (or (get-type-of-bv-expr-axe fn args)
      (cond ;see unsigned-byte-p-1-of-bitxor, etc.:
       ((or (eq fn 'bv-array-write)
            (eq fn 'bv-array-if))
        (let ((second (unquote-if-possible (first args)))
              (third (unquote-if-possible (second args))))
          (if (and (natp second) (natp third))
              (make-bv-array-type second third)    ;fixme what if the width is 0?
            nil                                 ;error?
            )))
       ((member-eq fn *known-predicates-basic* ;;'(equal boolif booland boolor sbvlt bvlt bvle not unsigned-byte-p) ;TODO: Use the known-boolean stuff, in case we want to stub out a user-defined boolean function?
                   )
        (boolean-type)) ;nil ;BBOZO make sure these are handled right downstream
       (t nil ;should this be most-general-type or something like that?
          ))))

(defthm axe-typep-of-get-type-of-expr
  (implies (get-type-of-expr fn args)
           (axe-typep (get-type-of-expr fn args)))
  :hints (("Goal" :in-theory (enable get-type-of-expr))))

;get rid of this?
(defun get-type-of-expr-safe (fn args)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args))))
  (let ((type (get-type-of-expr fn args)))
    (or type
        (er hard? 'get-type-of-expr-safe "couldn't find type for call of ~x0 on args ~x1" fn args))))

;fixme rename ...-safe and have this return most-general-type instead of nil..
;use this more!?
;returns a type or nil for unknown
;val is the unquoted constant
(defund get-type-of-constant-if-possible (val)
  (declare (xargs :guard t))
  (if (natp val)
      (make-bv-type (max 1 (integer-length val)))
    (if (booleanp val)
        (boolean-type)
      ;;new (this is the tightest possible type, but wider element widths would also work):
      (if (and (consp val) ;new! disallows arrays of length 0
               (nat-listp val))
          (make-bv-array-type (max 1 (width-of-widest-int val)) ;fixme if the values are all 0, we consider the width to be 1
                              (len val))
        nil))))

(defthm axe-typep-of-get-type-of-constant-if-possible
  (implies (get-type-of-constant-if-possible val)
           (axe-typep (get-type-of-constant-if-possible val)))
  :hints (("Goal" :in-theory (enable get-type-of-constant-if-possible))))

(defun get-type-of-constant (val)
  (declare (xargs :guard t))
  (let ((type (get-type-of-constant-if-possible val)))
    (or type
        (progn$ nil ;(break$)
                (er hard? 'get-type-of-constant "Trying to get type of unrecognized constant: ~x0" val)))))

;returns a type (bv type, array type, etc.)
;ffixme can crash if given a nodenum of a weird constant (can that happen?)
(defund get-type-of-nodenum (arg ;a nodenum
                             dag-array-name
                             dag-array
                             nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                             )
  (declare (xargs :guard (and (alistp nodenum-type-alist)
                              (natp arg)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 arg))
                              (< arg (alen1 dag-array-name dag-array)))))
  ;;first check whether it is given a type in nodenum-type-alist (fffixme what if we could strengthen that type?):
  (or (lookup arg nodenum-type-alist)
      ;;otherwise, look up the expression at that nodenum:
      (let ((expr (aref1 dag-array-name dag-array arg)))
        (if (variablep expr)
            ;;(lookup-eq expr var-type-alist) ;fix up ranges?   <- huh?
            (er hard? 'get-type-of-nodenum "can't find type of var ~x0." expr)
          (let ((fn (ffn-symb expr)))
            (if (eq 'quote fn) ;;(myquotep expr) ;;was quotep.
                (get-type-of-constant (unquote expr))
              ;;it's a regular function call:
              (or (get-type-of-expr fn (dargs expr))
                  (er hard? 'get-type-of-nodenum "couldn't find size for expr ~x0 at nodenum ~x1" expr arg))))))))

;ffixme can crash if given a weird constant or a nodenum of a weird constant
;returns a type (bv type, array type, etc.)
(defund get-type-of-arg (arg ;a nodenum or quotep
                         dag-array-name
                         dag-array
                         nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                         )
  (declare (xargs :guard (and (or (myquotep arg)
                                  (and (natp arg)
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 arg))))
                              (alistp nodenum-type-alist))))
  (if (consp arg) ;tests for quotep
      (get-type-of-constant (unquote arg))
    (get-type-of-nodenum arg dag-array-name dag-array nodenum-type-alist)))

;;;
;;; nat-to-string

;deprecate? ;make the guard require natp?
;make a version that returns a string-tree?
(defund nat-to-string-debug (n)
  (declare (xargs :guard t))
  (if (not (natp n))
      (progn$ (cw "error: called nat-to-string on non-natural ~x0." n)
              (break$) ;(car 7) ;will crash and put us in the debugger
              )
    (nat-to-string n)))

(in-theory (disable (:e nat-to-string-debug)))

(defthm stringp-of-nat-to-string-debug
  (implies (natp n)
           (stringp (nat-to-string-debug n)))
  :hints (("Goal" :in-theory (enable nat-to-string-debug))))

(defthm string-treep-of-nat-to-string-debug
  (implies t;(natp n) ;todo: put back
           (string-treep (nat-to-string-debug n)))
  :hints (("Goal" :in-theory (enable nat-to-string-debug))))

;;;
;;; makevarname
;;;

;; Returns a string-tree.
(defund makevarname (n)
  (declare (type (integer 0 *) n))
  (cons "NODE" (nat-to-string-debug n)))

(defthm string-treep-of-makevarname
  (string-treep (makevarname n))
  :hints (("Goal" :in-theory (enable makevarname))))

;;;
;;; translating booleans
;;;

;; Check that, if ARG is a constant, it is a boolean constant.
(defund boolean-arg-okp (arg)
  (declare (xargs :guard (dargp arg)))
  (if (consp arg) ;check for quotep
      (if (booleanp (unquote arg))
          t
        (prog2$ (cw "Warning: Non-boolean constant ~x0 detected in a boolean context.~%" arg)
                nil))
    ;; it's a nodenum, so no checking is needed here (we will cut at that node if needed):
    t))

;; Returns a string-tree.
;; ARG must be a nodenum or 't or 'nil.
(defund translate-boolean-arg (arg)
  (declare (xargs :guard (and (dargp arg)
                              (boolean-arg-okp arg))))
  (if (consp arg) ;checks for quotep
      (if (equal arg *nil*)
          "FALSE"
        (if (equal arg *t*)
            "TRUE"
          ;;i suppose any constant other than nil could be translated as t (but print a warning?!):
          (er hard? 'translate-boolean-arg "unrecognized boolean constant: ~x0.~%" arg)))
    ;;arg is a node number:
    (makevarname arg)))

(defthm string-treep-of-translate-boolean-arg
  (string-treep (translate-boolean-arg arg))
  :hints (("Goal" :in-theory (enable translate-boolean-arg))))

;;;
;;; translating BVs
;;;

;; Returns a string-tree.
;make tail rec?
;make a table for a few common values?  process the bits in bigger chunks?
(defund translate-bits (val topbit)
  (declare (type integer val)
           (xargs :measure (if (natp topbit) (+ 1 topbit) 0)))
  (if (not (natp topbit))
      ""
    (cons (if (logbitp topbit val) ;(eql 1 (getbit topbit n))
              "1"
            "0")
          (translate-bits val (+ -1 topbit)))))

(defthm string-treep-of-translate-bits
  (string-treep (translate-bits val topbit))
  :hints (("Goal" :in-theory (enable translate-bits))))

;; Returns a string-tree,
(defund translate-bv-constant (val size)
  (declare (type integer val)
           (type (integer 1 *) size))
  (cons "0bin" (translate-bits val (+ -1 size))))

(defthm string-treep-of-translate-bv-constant
  (string-treep (translate-bv-constant val size))
  :hints (("Goal" :in-theory (enable translate-bv-constant))))

;the 0's go into the high bits
;returns a string-tree
(defund pad-with-zeros (numzeros val)
  (declare (xargs :guard (and (natp numzeros)
                              (string-treep val))))
  (if (zp numzeros)
      val
    (list* "("
           (translate-bv-constant 0 numzeros) ;bozo don't need to recompute each time...
           "@"
           val
           ")")))

(defthm string-treep-of-pad-with-zeros
  (implies (string-treep val)
           (string-treep (pad-with-zeros numzeros val)))
  :hints (("Goal" :in-theory (enable pad-with-zeros))))

;Here the actual size of the nodenum is known
;; Returns a string-tree
(defund translate-bv-nodenum-and-pad (nodenum desired-size actual-size)
  (declare (type (integer 0 *) desired-size actual-size)
           (xargs :guard (natp nodenum)))
  (let ((varname (makevarname nodenum)))
    ;;we need to pad with zeros if the node isn't wide enough:
    (if (< actual-size desired-size)
        (pad-with-zeros (- desired-size actual-size) varname)
      varname)))

(defthm string-treep-of-translate-bv-nodenum-and-pad
  (string-treep (translate-bv-nodenum-and-pad nodenum desired-size actual-size))
  :hints (("Goal" :in-theory (enable translate-bv-nodenum-and-pad))))

;; todo: consider adding a size param
;; check that, if it is a constant, then it is a bv constant
(defund bv-arg-okp (arg)
  (declare (xargs :guard (dargp arg)))
  (if (consp arg)
      (if (natp (unquote arg))
          t
        (prog2$ (cw "Warning: Non-integer constant ~x0 detected in a boolean context.~%" arg)
                nil))
    ;; it's a nodenum, so no checking is needed here (we will cut at that node if needed):
    t))

(defthm bv-arg-okp-forward
  (implies (and (bv-arg-okp arg)
                (consp arg))
           (natp (unquote arg)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bv-arg-okp))))

;ARG is either a quotep or a nodenum
;Here the actual size of the arg is known
;BOZO throw an error if the arg is too big for the size (or chop it down?)
;returns a string-tree.
(defund translate-bv-arg-and-pad (arg desired-size actual-size)
  (declare (type (integer 1 *) desired-size)
           (type (integer 0 *) actual-size)
           (xargs :guard (and (dargp arg)
                              (bv-arg-okp arg))))
  (if (consp arg) ;tests for quotep
      (translate-bv-constant (unquote arg) desired-size) ;;can we just handle this the same way as the below (just pad)?
    ;;Otherwise, arg is a nodenum:
    (translate-bv-nodenum-and-pad arg desired-size actual-size)))

(defthm string-treep-of-translate-bv-arg-and-pad
  (string-treep (translate-bv-arg-and-pad arg desired-size actual-size))
  :hints (("Goal" :in-theory (enable translate-bv-arg-and-pad))))

;; Returns a string-tree.
;Looks up the size of the arg and pads as appropriate
;ffffixme change this to chop and skip all the chops in the callers!
;ARG is either a quotep or a nodenum in the DAG-ARRAY
;FIXME throw an error if the arg is too big for the size (or chop it down? i guess this already in effect chops down constants - is that always sound?)
(defund translate-bv-arg (arg desired-size dag-array-name dag-array dag-len nodenum-type-alist)
  (declare (type (integer 1 *) desired-size)
           (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than arg dag-len)
                              (bv-arg-okp arg)
                              (alistp nodenum-type-alist)))
           (ignore dag-len))
  (if (consp arg) ;tests for quotep
      (translate-bv-constant (unquote arg) desired-size)
    ;;arg is a nodenum:
    (let ((type (get-type-of-nodenum arg dag-array-name dag-array nodenum-type-alist)))
      (if (bv-typep type)
          (translate-bv-nodenum-and-pad arg desired-size (bv-type-width type))
        (er hard? 'translate-bv-arg "bad type: ~x0 for argument ~x1" type arg)))))

(defthm string-treep-of-translate-bv-arg
  (string-treep (translate-bv-arg arg desired-size dag-array-name dag-array dag-len nodenum-type-alist))
  :hints (("Goal" :in-theory (enable translate-bv-arg))))

;returns a string-tree
(defund translate-array-element-equality (lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width elem-num)
  (declare (xargs :guard (and (integerp elem-num)
                              (natp lhs-pad-bits)
                              (natp rhs-pad-bits)
                              (posp index-width)
                              (string-treep lhs-string-tree)
                              (string-treep rhs-string-tree))))
  (let ((index (translate-bv-constant elem-num index-width)))
    (list* "("
           (pad-with-zeros lhs-pad-bits (list* lhs-string-tree "[" index "]"))
           " = "
           (pad-with-zeros rhs-pad-bits (list* rhs-string-tree "[" index "]"))
           ")")))

(defthm string-treep-of-translate-array-element-equality
  (implies (and (string-treep lhs-string-tree)
                (string-treep rhs-string-tree))
           (string-treep (translate-array-element-equality lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width elem-num)))
  :hints (("Goal" :in-theory (enable translate-array-element-equality))))

;makes an assertion for each possible index
;returns string-tree
(defund translate-array-equality-assertion (n ;the element number
                                       lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width
                                       acc ;a list of strings
                                       )
  (declare (type (integer 0 *) n lhs-pad-bits rhs-pad-bits)
           (xargs :guard (and (posp index-width)
                              (string-treep lhs-string-tree)
                              (string-treep rhs-string-tree))))
  (if (zp n)
      ;;for element zero we don't generate an AND
      (list* "(" ;matches the close paren passed in in ACC
             (newline-string)
             (translate-array-element-equality lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width n)
             acc)
    (translate-array-equality-assertion (+ -1 n) lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width
                                   (list* (newline-string)
                                          "AND "
                                          (translate-array-element-equality lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width n)
                                          acc))))

(defthm string-treep-of-translate-array-equality-assertion
  (implies (and (string-treep acc)
                (string-treep lhs-string-tree)
                (string-treep rhs-string-tree))
           (string-treep (translate-array-equality-assertion n lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width acc)))
  :hints (("Goal" :in-theory (enable translate-array-equality-assertion))))


;dup
;; ;fixme this returns true on -1 (it's considered an empty list)
;; (defun all-natp (lst)
;;   (declare (xargs :guard t))
;;   (if (atom lst)
;;       t
;;       (and (natp (car lst))
;;            (all-natp (cdr lst)))))

;; (defthm nodenum-or-consp-list-when-all-dargp-less-than
;;   (implies (all-dargp-less-than items nodenum)
;;            (nodenum-or-consp-list items))
;;   :hints (("Goal" :in-theory (enable all-dargp-less-than nodenum-or-consp-list))))


;; ;slow?
;; (defthm consp-of-cdr-of-aref1
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array arg)
;;                 (natp arg)
;; ;                (not (equal (car (aref1 dag-array-name dag-array arg)) 'quote))
;;                 (consp (aref1 dag-array-name dag-array arg)))
;;            (iff (consp (cdr (aref1 dag-array-name dag-array arg)))
;;                 (cdr (aref1 dag-array-name dag-array arg))))
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array arg))
;;            :in-theory (enable pseudo-dag-arrayp-aux bounded-dag-exprp))))

;recognizes a true list of items of the form (array-elems array-name element-width element-count)
(defund constant-array-infop (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq nil x)
    (let ((entry (first x)))
      (and (eql 4 (len entry))
           (nat-listp (first entry))
           (string-treep (second entry))
           (posp (third entry))
           (natp (fourth entry))
           (<= (fourth entry) (len (first entry))) ;fixme should we disallow the constant being longer?
           (constant-array-infop (rest x))))))

(defthm constant-array-infop-of-cdr
  (implies (constant-array-infop constant-array-info)
           (constant-array-infop (cdr constant-array-info)))
  :hints (("Goal" :in-theory (enable constant-array-infop))))

;returns a string, or nil if no match
;constant-array-info is a list of items of the form (array-constant array-name element-width element-count)
;fixme no need to store the data and also its length?
(defund get-array-constant-name (data element-width element-count constant-array-info)
  (declare (xargs :guard (constant-array-infop constant-array-info)
                  :guard-hints (("Goal" :in-theory (enable constant-array-infop)))))
  (if (endp constant-array-info)
      nil
    (let ((entry (first constant-array-info)))
      (if (and (equal data (first entry))
               (eql element-width (third entry))
               (eql element-count (fourth entry)))
          (second entry)
        (get-array-constant-name data element-width element-count (rest constant-array-info))))))

(defthm string-treep-of-get-array-constant-name
  (implies (constant-array-infop constant-array-info)
           (string-treep (get-array-constant-name data element-width element-count constant-array-info)))
  :hints (("Goal" :in-theory (enable get-array-constant-name constant-array-infop))))

;makes sure that if the same array constant (used with the same width) appears twice we only make one var for it..
;fixme think about two arrays with the same values but different element widths!
;returns a string for the array, and perhaps adds an entry to constant-array-info
;returns (mv array-name constant-array-info)
;constant-array-info is a list of items of the form (array-constant array-name element-width element-count)
;maybe we don't need to key off the element-count any more, since we always check that constant arrays have the right length (so element-count here will always just be constant-array-info)?
(defund translate-constant-array-mention (data element-width element-count constant-array-info)
  (declare (xargs :guard (and (myquotep data)
                              (posp element-width)
                              (constant-array-infop constant-array-info))))
  (let* ((data (unquote data))
         (match (get-array-constant-name data element-width element-count constant-array-info)))
    (if match
        (mv match constant-array-info)
      ;; no match:
      (let* ((array-number (len constant-array-info)) ;fixme do something better?
             (array-name (cons "ARRAY" (nat-to-string array-number))))
        (mv array-name
            (cons (list data array-name element-width element-count)
                  constant-array-info))))))

(defthm constant-array-infop-of-mv-nth-1-of-translate-constant-array-mention
  (implies (and (constant-array-infop constant-array-info)
                (nat-listp (unquote data))
                (posp element-width)
                (natp element-count)
                (<= element-count (len (unquote data))))
           (constant-array-infop (mv-nth 1 (translate-constant-array-mention data element-width element-count constant-array-info))))
  :hints (("Goal" :in-theory (enable translate-constant-array-mention constant-array-infop))))

(defthm stringp-of-mv-nth-0-of-translate-constant-array-mention
  (implies (constant-array-infop constant-array-info)
           (string-treep (mv-nth 0 (translate-constant-array-mention data element-width element-count constant-array-info))))
  :hints (("Goal" :in-theory (enable translate-constant-array-mention constant-array-infop))))

;returns (mv translated-expr constant-array-info) where translated-expr is a string-tree.
;fixme what if we can't translate the equality (maybe it mentions ':byte)?
(defund translate-equality (lhs ;a nodenum or quoted constant
                            rhs ;a nodenum or quoted constant
                            dag-array-name dag-array nodenum-type-alist constant-array-info)
  (declare (xargs :guard (and (or (myquotep rhs)
                                  (and (natp rhs)
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 rhs))))
                              (or (myquotep lhs)
                                  (and (natp lhs)
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 lhs))))
                              (alistp nodenum-type-alist)
                              (symbolp dag-array-name)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (e/d (GET-TYPE-OF-ARG ; causes lots of cases?
                                                         GET-TYPE-OF-CONSTANT-IF-POSSIBLE
                                                         )
                                                        ( ;;max
                                                         ;;BV-ARRAY-TYPEP ;for speed
                                                         ;;LIST-TYPEP
                                                         ;;GET-TYPE-OF-ARG
                                                         natp))
                                 :do-not '(generalize eliminate-destructors)))))
  (let* ((lhs-type (get-type-of-arg lhs dag-array-name dag-array nodenum-type-alist))
         (rhs-type (get-type-of-arg rhs dag-array-name dag-array nodenum-type-alist)))
    (if (and (bv-array-typep lhs-type)
             (bv-array-typep rhs-type)
             ;;the lengths must be the same (fixme if not, could translate the equality as false?? and print a warning!)
             (equal (bv-array-type-len lhs-type) (bv-array-type-len rhs-type)))
        ;; equality of two array terms of the same length:
        (let* ((lhs-element-width (bv-array-type-element-width lhs-type))
               (rhs-element-width (bv-array-type-element-width rhs-type))
               (common-len (bv-array-type-len lhs-type)) ;same as the len from rhs-type
               )
          (if (eql 0 common-len) ;; any two arrays of length 0 are equal (see theorem above)
              (mv (list "(TRUE)") ;todo: add a test of this case
                  constant-array-info)
            (if (eql 1 common-len)
                (mv (er hard? 'translate-equality "Arrays of length 1 are not supported.")
                    constant-array-info)
              (if (or (zp lhs-element-width)
                      (zp rhs-element-width))
                  (mv (er hard? 'translate-equality "Arrays whose elements have 0 width are not supported.")
                      constant-array-info)
                ;; translate the LHS (without padding yet):
                (mv-let (erp1 lhs-string-tree constant-array-info)
                  (if (atom lhs) ;checks for nodenum
                      (mv nil (makevarname lhs) constant-array-info)
                    ;;lhs is a constant array:
                    (if (and (nat-listp (unquote lhs)) ;these checks may be implied by the type tests above
                             )
                        (mv-let (lhs-string-tree constant-array-info)
                          (translate-constant-array-mention lhs lhs-element-width common-len constant-array-info)
                          (mv nil lhs-string-tree constant-array-info))
                      (prog2$ (er hard? 'translate-equality "Bad array constant: ~x0." lhs)
                              (mv t nil constant-array-info))))
                  ;; translate the RHS (without padding yet):
                  (mv-let (erp2 rhs-string-tree constant-array-info)
                    (if (atom rhs) ;checks for nodenum
                        (mv nil (makevarname rhs) constant-array-info)
                      ;;rhs is a constant array:
                      (if (and (nat-listp (unquote rhs)) ;these checks may be implied by the type tests above
                               )
                          (mv-let (rhs-string-tree constant-array-info)
                            (translate-constant-array-mention rhs rhs-element-width common-len constant-array-info)
                            (mv nil rhs-string-tree constant-array-info))
                        (prog2$ (er hard? 'translate-equality "Bad array constant: ~x0." rhs)
                                (mv t nil constant-array-info))))
                    (if (or erp1 erp2)
                        (mv nil constant-array-info)
                      ;;Now deal with padding:
                      (mv-let (lhs-pad-bits rhs-pad-bits)
                        (if (<= lhs-element-width rhs-element-width)
                            (mv (- rhs-element-width lhs-element-width) 0)
                          (mv 0 (- lhs-element-width rhs-element-width)))
                        (mv
                         ;; currently this doesn't use lets, but I guess it could?
                         ;;fixme think about arrays whose lengths are not powers of 2...
                         (translate-array-equality-assertion (+ -1 common-len)
                                                             lhs-string-tree
                                                             rhs-string-tree
                                                             lhs-pad-bits
                                                             rhs-pad-bits
                                                             (ceiling-of-lg common-len) ;; index-width; above we check for len=1
                                                             (list ")") ;acc
                                                             )
                         constant-array-info)))))))))
      ;; If we're comparing two booleans:
      (if (and (boolean-typep lhs-type)
               (boolean-typep rhs-type))
          (if (and (boolean-arg-okp lhs)
                   (boolean-arg-okp rhs))
              (mv
               (list* "("
                      (translate-boolean-arg lhs)
                      " <=> "
                      (translate-boolean-arg rhs)
                      ")")
               constant-array-info)
            ;;todo: pass back errors?
            (mv (er hard? 'translate-equality "A bad boolean arg was found.")
                constant-array-info))
        ;; If we're comparing two bit-vectors:
        (if (and (bv-typep lhs-type)
                 (bv-typep rhs-type))
            (if (and (bv-arg-okp lhs)
                     (bv-arg-okp rhs))
                (let* ((lhs-width (bv-type-width lhs-type))
                       (rhs-width (bv-type-width rhs-type))
                       (max-width (max lhs-width rhs-width)))
                  (if (or (zp lhs-width)
                          (zp rhs-width))
                      (mv (er hard? 'translate-equality "Bit vectors of width 0 are not supported.")
                          constant-array-info)
                    (mv (list* "("
                               (translate-bv-arg-and-pad lhs max-width lhs-width)
                               " = "
                               (translate-bv-arg-and-pad rhs max-width rhs-width)
                               ")")
                        constant-array-info)))
              ;;todo: pass back errors?
              (mv (er hard? 'translate-equality "A bad BV arg was found.")
                  constant-array-info))
          (prog2$ (print-array2 dag-array-name dag-array (max (if (natp lhs) (+ 1 lhs) 0) (if (natp rhs) (+ 1 rhs) 0)))
                  ;;fixme print the assumptions? or the literals? or nodenum-type-alist ?
                  ;;fixme be more flexible.  btw, nil is considered to be of type boolean, but what if it's being compared to a list of 0 size?
                  ;;fixme if the types are guaranteed to have disjoint value sets, we could just generate FALSE here, but watch out for things like nil (both a boolean and the empty list?)
                  (mv (er hard? 'translate-equality "Trying to equate things of different types (see above for dag): ~x0 (type: ~x1) and ~x2 (type: ~x3).~%"
                          lhs lhs-type rhs rhs-type)
                      constant-array-info)))))))

(defthm bv-array-type-len-of-get-type-of-arg-when-bv-array-typep
  (implies (and (consp x)
                (bv-array-typep (get-type-of-arg x dag-array-name dag-array cut-nodenum-type-alist)))
           (equal (bv-array-type-len (get-type-of-arg x dag-array-name dag-array cut-nodenum-type-alist))
                  (len (unquote x))))
  :hints (("Goal" :in-theory (enable get-type-of-arg get-type-of-constant-if-possible))))

(defthm string-treep-of-mv-nth-0-of-translate-equality
 (implies (constant-array-infop constant-array-info)
          (string-treep (mv-nth 0 (translate-equality lhs rhs dag-array-name dag-array cut-nodenum-type-alist constant-array-info))))
 :hints (("Goal" :in-theory (e/d (translate-equality) (list-typep bv-array-typep bv-array-type-len BV-ARRAY-TYPE-ELEMENT-WIDTH)))))

;; Returns (mv array-name constant-array-info actual-element-width) where ARRAY-NAME is a string-tree that can be used to refer to the array
(defund translate-array-arg (arg
                             desired-element-width
                             desired-array-length
                             dag-array-name
                             dag-array
                             nodenum-type-alist
                             calling-fn ;the function for which ARG is an argument
                             widths-must-matchp
                             constant-array-info)
  (declare (xargs :guard (and (posp desired-element-width)
                              (natp desired-array-length)
                              (symbolp calling-fn)
                              (or (myquotep arg)
                                  (and (natp arg) ;drop?
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 arg))
                                       (< arg (alen1 dag-array-name dag-array))))
                              (array1p dag-array-name dag-array)
                              (alistp nodenum-type-alist)
                              (constant-array-infop constant-array-info))))
  ;;todo: maybe split into cases here at the start based on whether it's a constant?
  (b* ((arg-type (get-type-of-arg arg dag-array-name dag-array nodenum-type-alist))
       ((when (not (bv-array-typep arg-type)))
        (mv (er hard? 'translate-array-arg "Tried to translate an argument, ~x0, of ~x1 that is not known to be an array." arg calling-fn)
            constant-array-info
            0))
       (arg-len (bv-array-type-len arg-type))
       (arg-element-width (bv-array-type-element-width arg-type))
       (constant-arrayp (consp arg)) ;checks for a quoted constant
       )
    (if (not (eql desired-array-length arg-len))
        (prog2$ (er hard? 'translate-array-arg "Tried to translate an array argument to ~x0 with desired length ~x1 but actual length ~x2.~%" calling-fn desired-array-length arg-len)
                (mv nil constant-array-info 0))
      (if (and (not constant-arrayp) ;; I guess we don't need to check this for constants (constant array elements that are too small are okay, elements that are too large get chopped)
               widths-must-matchp
               (not (eql desired-element-width arg-element-width))) ;could perhaps translate this to false...
          (prog2$ (er hard? 'translate-array-arg "Tried to translate an array argument to ~x0 with desired element width ~x1 but actual element width ~x2.~%"
                      calling-fn desired-element-width arg-element-width)
                  (mv nil constant-array-info 0))
        ;;We handle constant arrays by putting in a fresh variable and adding asserts about the values of each element
        ;;Here, we check whether the array argument is a constant. If possible, we reuse the name of an existing constant array with the same data, length, and width.
        (if constant-arrayp ;it's a constant array:
            (if (nat-listp (unquote arg))
                ;;fixme what if the data is of the wrong form?
                (b* (((mv array-name constant-array-info)
                      (translate-constant-array-mention arg desired-element-width desired-array-length constant-array-info)))
                  (mv array-name constant-array-info arg-element-width))
              (prog2$ (er hard? 'translate-array-arg "Tried to translate an array argument to ~x0 with bad data ~x1.~%"
                          calling-fn (unquote arg))
                      (mv nil constant-array-info 0)))
          ;;arg is a nodenum:
          (mv (makevarname arg)
              constant-array-info
              arg-element-width))))))

(defthm string-treep-of-mv-nth-0-of-translate-array-arg
  (implies (constant-array-infop constant-array-info)
           (string-treep (mv-nth 0 (translate-array-arg arg desired-element-width desired-array-length
                                                        dag-array-name dag-array nodenum-type-alist
                                                        calling-fn ;the function for which ARG is an argument
                                                        widths-must-matchp
                                                        constant-array-info))))
  :hints (("Goal" :in-theory (enable TRANSLATE-ARRAY-ARG
                                     constant-array-infop))))

(defthm constant-array-infop-of-mv-nth-1-of-translate-array-arg
  (implies (and ;(nat-listp (cadr arg))
                (posp desired-element-width)
                (constant-array-infop constant-array-info)
                )
           (constant-array-infop (mv-nth 1 (translate-array-arg arg desired-element-width desired-array-length
                                                                dag-array-name dag-array nodenum-type-alist
                                                                calling-fn ;the function for which arg is an argument
                                                                widths-must-matchp
                                                                constant-array-info))))
  :hints (("Goal" :in-theory (enable translate-array-arg))))

(defthm rationalp-of-mv-nth-2-of-translate-array-arg
  (rationalp (mv-nth 2 (translate-array-arg arg desired-element-width desired-array-length
                                            dag-array-name dag-array nodenum-type-alist
                                            calling-fn ;the function for which arg is an argument
                                            widths-must-matchp
                                            constant-array-info)))
  :hints (("Goal" :in-theory (enable translate-array-arg))))

(defthm integerp-of-mv-nth-2-of-translate-array-arg
  (integerp (mv-nth 2 (translate-array-arg arg desired-element-width desired-array-length
                                            dag-array-name dag-array nodenum-type-alist
                                            calling-fn ;the function for which arg is an argument
                                            widths-must-matchp
                                            constant-array-info)))
  :hints (("Goal" :in-theory (enable translate-array-arg))))

;; (defthm constant-array-infop-of-mv-nth-1-of-translate-array-arg
;;   (implies (and (constant-array-infop constant-array-info)
;;                 (natp desired-element-width)
;;                 (natp desired-array-length))
;;            (constant-array-infop (mv-nth 1 (translate-array-arg arg desired-element-width desired-array-length
;;                                                                 dag-array-name dag-array nodenum-type-alist
;;                                                                 calling-fn ;the function for which arg is an argument
;;                                                                 widths-must-matchp
;;                                                                 constant-array-info))))
;;   :hints (("Goal" :in-theory (enable translate-array-arg
;;                                      constant-array-infop))))



;; Returns (mv translated-expr-string constant-array-info).
;; (defun translate-dag-expr-bvplus (args dag-array-name dag-array constant-array-info cut-nodenum-type-alist)
;;   (declare (xargs :guard (and (array1p dag-array-name dag-array) ;;TODO: Instead, use pseudo-dag-arrayp.
;;                               (all-dargp-less-than args (alen1 dag-array-name dag-array))
;;                               (alistp cut-nodenum-type-alist)
;;                               (symbolp dag-array-name)
;;                               (equal 3 (len args))
;;                               (quoted-posp (first args))
;;                               )))
;;   (let* ((width (safe-unquote (first args)))
;;          (top-bit-string (nat-to-string-debug (+ -1 width))))
;;     (mv (n-string-append "(BVPLUS("
;;                          (nat-to-string-debug width)
;;                          ","
;;                          (translate-bv-arg (second args) width dag-array-name dag-array cut-nodenum-type-alist)
;;                          "["
;;                          top-bit-string
;;                          ":0],"
;;                          (translate-bv-arg (third args) width dag-array-name dag-array cut-nodenum-type-alist)
;;                          "["
;;                          top-bit-string
;;                          ":0]))")
;;         constant-array-info)))

(defthm myquote-forward-to-equal-of-nth-0-and-quote
  (implies (myquotep expr)
           (equal 'quote (nth 0 expr)))
  :rule-classes :forward-chaining)

(defthm natp-of-+-of--
  (implies (and (integerp x)
                (integerp y))
           (equal (natp (+ x (- y)))
                  (<= y x))))

;the nth-1 is to unquote
(defthm bv-typep-of-get-type-of-constant-if-possible-of-nth-1
  (implies (and (bv-arg-okp arg)
                (consp arg) ;it's a quotep
                )
           (bv-typep (get-type-of-constant-if-possible (nth 1 arg))))
  :hints (("Goal" :in-theory (enable get-type-of-constant-if-possible bv-arg-okp))))

;; Returns (mv translated-expr constant-array-info) where translated-expr is a string-tree.
;FFIXME think hard about sizes and chops..
;add support for leftrotate (not just leftrotate32? width may need to be a power of 2?), etc.?
;fixme the calls to safe-unquote below can cause crashes??
;thread through an accumulator?
;should this take a desired size (or type?) for the expr?
;should we separate out the handling of terms from formulas
;TODO: Pull out the constant case?
;TODO: Need to know that the arity is correct.
;; dag-len is only used in guards (including the guard of translate-bv-arg).
;todo: see repeated calls below to translate-bv-arg on same value...
(defund translate-dag-expr (expr ;either a quotep or a function call over nodenums and quoteps (never a variable)
                            dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-dag-exprp dag-len expr)
                              (consp expr)
                              ;;(all-< .. (alen1 dag-array-name dag-array))
                              (alistp cut-nodenum-type-alist)
;(symbolp dag-array-name)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (e/d (get-type-of-arg
                                                         car-becomes-nth-of-0
                                                         BOUNDED-DAG-EXPRP
                                                         dag-exprp0
                                                         NATP-OF-+-OF-1)
                                                        (DARGP
                                                         MYQUOTEP
                                                         NATP
                                                         QUOTEP))))))
  (let ((fn (ffn-symb expr)))
    (mv-let (erp translated-expr constant-array-info)
      (case fn
        (quote
         ;;fixme this had better occur only with boolean branches, not bv branches??
         ;;fixme, do we support constant nodes, or not?  what about ones put in for probably-constant nodes?
;fixme what about constant arrays?!
         (mv (erp-nil)
             (prog2$ (cw "WARNING: Translating the naked constant: ~x0.~%" expr) ;ffixme think about this
                     (let ((constant (unquote expr)))
                       (if (equal constant t)
                           "TRUE"
                         (if (equal constant nil)
                             "FALSE"
                           (if (natp constant)
                               (translate-bv-constant constant (max 1 (integer-length (unquote expr))))
                             (er hard? 'translate-dag-expr "bad constant: ~x0" constant))))))
             constant-array-info))
        (unsigned-byte-p ;(UNSIGNED-BYTE-P WIDTH X)
         (if (and (= 2 (len (dargs expr)))
                  (quoted-natp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (b* ((width-arg (darg1 expr)) ;had better be quoted
                  (claimed-width (safe-unquote width-arg))
                  (bv-arg (darg2 expr))
                  (bv-arg-type (get-type-of-arg bv-arg dag-array-name dag-array cut-nodenum-type-alist))
                  ((when (not (bv-typep bv-arg-type)))
                   (er hard? 'translate-dag-expr "unsigned-byte-p claim applied to non bv ~x0." bv-arg)
                   (mv (erp-t) nil constant-array-info)) ;todo: allow this function to return an error
                  (known-width (bv-type-width bv-arg-type))
                  (- (if (= 0 known-width)
                         (er hard? 'translate-dag-expr "unsigned-byte-p claim with a width of 0 applied to ~x0." bv-arg)
                       nil)))
               (mv
                (erp-nil)
                (if (<= known-width claimed-width)
                    "(TRUE)" ;the unsigned-byte-p doesn't tell us anything new
                  ;;the unsigned-byte-p-claim amounts to saying that the high bits are 0:
                  (list* "(("
                         (translate-bv-arg bv-arg known-width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         "["
                         (nat-to-string-debug (+ -1 known-width))
                         ":"
                         (nat-to-string-debug claimed-width)
                         "]) = "
                         (translate-bv-constant 0 (- known-width claimed-width))
                         ")"
                         ))
                constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        ;;boolean operators
        ;;fixme support boolxor [or is it called just xor]?  what about bool-to-bit?
        (boolor
         (if (and (= 2 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "(" (translate-boolean-arg (darg1 expr)) " OR " (translate-boolean-arg (darg2 expr)) ")")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (booland
         (if (and (= 2 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "(" (translate-boolean-arg (darg1 expr)) " AND " (translate-boolean-arg (darg2 expr)) ")")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (boolif
         (if (and (= 3 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr))
                  (boolean-arg-okp (darg3 expr)))
             (mv (erp-nil)
                 (list* "(IF "
                        (translate-boolean-arg (darg1 expr))
                        " THEN "
                        (translate-boolean-arg (darg2 expr))
                        " ELSE "
                        (translate-boolean-arg (darg3 expr))
                        " ENDIF)")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (not ;todo: not is commented out in can-always-translate-expr-to-stp
         (if (and (= 1 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr)))
             (mv (erp-nil)
                 (list* "(NOT(" (translate-boolean-arg (darg1 expr)) "))")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bv-array-read ;(BV-ARRAY-READ ELEMENT-WIDTH LEN INDEX DATA)
         ;;fixme an error occurs if we try to translate a bv-array-read of one length applied to a bv-array-write of a longer length? better to just cut there??
         ;;also an error if we translate two bv-array-reads with different len params but the same array param
         ;;fixme handle arrays with non-constant lengths? will have to think about array lengths that are not powers of 2.  may need to translate ceiling-of-lg...
         (if (and (= 4 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (quoted-posp (darg2 expr))
                  (< 1 (unquote (darg2 expr))) ;arrays of length 1 would have 0 index bits
                  (bv-arg-okp (darg3 expr)))
             (b* ((element-width (safe-unquote (darg1 expr)))
                  (len (safe-unquote (darg2 expr))) ;ffixme can the array length ever be 1? ;maybe we should get the len from the data argument... - fixme may need a case for when the index is > the len param - return 0? well, the index gets chpped down..
                  (index (darg3 expr))
                  (array-arg (darg4 expr))
                  (num-index-bits (ceiling-of-lg len))
                  ((mv array-name constant-array-info actual-element-width)
                   (translate-array-arg array-arg element-width len dag-array-name dag-array cut-nodenum-type-alist 'bv-array-read nil constant-array-info))
                  ;; given that we've checked the len, can we remove the index padding stuff below?
                  (trimmed-index (list*
                                  ;;the index gets chopped down to NUM-INDEX-BITS bits because that's what bv-array-read does (fixme should translate-bv-arg accomplish that?!):
                                  (translate-bv-arg index num-index-bits dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                  "["
                                  (nat-to-string-debug (+ -1 num-index-bits))
                                  ":0]"))
                  (array-access (list* array-name
                                       "[" ;; open bracket of array access
                                       ;; the index expression:
;i guess this padding is to support a long array being accessed in a bv-array-read with a shorter length parameter (currently that would throw an error). note that if the index is out-of-bounds with respect to the length parameter of the bv-array-read, the read returns 0, even if there are enough data values in the array that the read could be done.
                                       (pad-with-zeros
                                        (- (ceiling-of-lg len) num-index-bits) ;Mon Jul  5 00:12:37 2010 (fixme can this be negative?  that would be an error?!)
                                        trimmed-index)
                                       "]" ;; close bracket of array access
                                       ))
                  (access-when-in-bounds (list* "("
                                                (if (< actual-element-width element-width)
                                                    (pad-with-zeros (- element-width actual-element-width) array-access)
                                                  array-access)
                                                "["
                                                (nat-to-string-debug (+ -1 element-width)) ;may chop down the value (fixme omit if no chopping is needed?)
                                                ":0])"
                                                )))
               (mv ;Now handle out-of-bounds array accesses:
                (erp-nil)
                (if (power-of-2p len)
                    ;;If the length is a power of 2, the trimmed index is always in bounds:
                    access-when-in-bounds
                  (list* "(IF (BVLT("
                         trimmed-index
                         ","
                         (translate-bv-constant len num-index-bits)
                         ")) THEN ("
                         access-when-in-bounds
                         ") ELSE ("
                         (translate-bv-constant 0 element-width) ;out of bounds access gives 0
                         ") ENDIF)"))
                constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bv-array-write ;; (bv-array-write element-width len index val array-arg)
         ;;fixme handle arrays with non-constant lengths? will have to think about array lengths that are not powers of 2.  may need to translate ceiling-of-lg...
         (if (and (= 5 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (quoted-natp (darg2 expr))
                  (< 1 (unquote (darg2 expr))) ;arrays of length 1 would have 0 index bits
                  (bv-arg-okp (darg3 expr))
                  (bv-arg-okp (darg4 expr)))
             (b* ((element-width (safe-unquote (darg1 expr)))
                  (len (safe-unquote (darg2 expr)))
                  (index (darg3 expr))
                  (val (darg4 expr))
                  (array-arg (darg5 expr))
                  (num-index-bits (ceiling-of-lg len))
                  ((mv array-name constant-array-info &)
                   (translate-array-arg array-arg element-width len dag-array-name dag-array cut-nodenum-type-alist 'bv-array-write t constant-array-info)))
               (let* ((trimmed-index
                       (list* (translate-bv-arg index num-index-bits dag-array-name dag-array dag-len cut-nodenum-type-alist)
                              "["
                              (nat-to-string-debug (+ -1 num-index-bits))
                              ":0]"))
                      (expr-when-in-bounds
                       (list* "("
                              array-name
                              " WITH ["
                              trimmed-index ;fixme should we consider padding the index to work for arrays that are actually longer, as we do for bv-array-read?
                              "] := ("
                              ;; value:
                              (translate-bv-arg val element-width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                              "["
                              (nat-to-string-debug (+ -1 element-width))
                              ":0]))"
                              )))
                 (mv (erp-nil)
                     (if (power-of-2p len)
                         ;;if the length is a power of 2, any trimmed index is in bounds:
                         expr-when-in-bounds
                       (list* "(IF (BVLT("
                              trimmed-index
                              ","
                              (translate-bv-constant len num-index-bits)
                              ")) THEN ("
                              expr-when-in-bounds
                              ") ELSE ("
                              array-name ;out of bounds access has no effect
                              ") ENDIF)"))
                     constant-array-info)))
           (mv (erp-t) nil constant-array-info)))
        (bvnot ;; (bvnot size x)
         (if (and (= 2 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let ((width (safe-unquote (darg1 expr))))
               (mv (erp-nil)
                   (list* "(~"
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          (nat-to-string-debug (+ -1 width))
                          ":0]) ")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvand ;; (bvand size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr))
                  )
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0] & "
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0])")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvor ;; (bvor size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0] | "
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0])")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvxor ;; (bvxor size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(BVXOR("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvmult ;; (bvmult size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(BVMULT("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvminus ;; (bvminus size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(BVSUB("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvplus ;; (bvplus size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(BVPLUS("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvuminus ;; (bvuminus size x)
         (if (and (= 2 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let* ((width (safe-unquote (darg1 expr))))
               (mv (erp-nil)
                   (list* "(BVUMINUS("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          (nat-to-string-debug (+ -1 width))
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvdiv ;; (bvdiv size x y)
         ;; note the special case for 0 divisor
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(IF (" ;if the third arg is 0, then the bvdiv is 0
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "[" top-bit-string ":0]" ;this line is new, since translate-bv-arg doesn't chop?!
                          "="
                          (translate-bv-constant 0 width)
                          ") THEN ("
                          (translate-bv-constant 0 width)
                          ") ELSE "
                          "(BVDIV("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0])) ENDIF)")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvmod ;; (bvmod size x y)
         ;; note the special case for 0 divisor
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(IF (" ;if the third arg is 0, then the bvmod is bvchop of its second argument
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "[" top-bit-string ":0]" ;this line is new, since translate-bv-arg doesn't chop?!
                          "="
                          (translate-bv-constant 0 width)
                          ") THEN ("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "[" top-bit-string ":0]" ;this line is new, since translate-bv-arg doesn't chop?!
                          ") ELSE (BVMOD("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0])) ENDIF)")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvdiv ;; (sbvdiv size x y)
         ;; note the special case for 0 divisor
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(IF (" ;if the third arg is 0, then the sbvdiv is 0
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "[" top-bit-string ":0]" ;this line is new, since translate-bv-arg doesn't chop?!
                          "="
                          (translate-bv-constant 0 width)
                          ") THEN ("
                          (translate-bv-constant 0 width)
                          ") ELSE "
                          "(SBVDIV("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0])) ENDIF)")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvrem ;; (sbvrem size x y)
         ;; note the special case for 0 divisor
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(IF (" ;if the third arg is 0, then the sbvrem is bvchop of its second argument
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "[" top-bit-string ":0]" ;this line is new, since translate-bv-arg doesn't chop?!
                          "="
                          (translate-bv-constant 0 width)
                          ") THEN ("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "[" top-bit-string ":0]" ;this line is new, since translate-bv-arg doesn't chop?!
                          ") ELSE (SBVMOD("
                          (nat-to-string-debug width)
                          ","
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0],"
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0])) ENDIF)")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvchop ;; (bvchop size x)
         (if (and (= 2 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (let ((width (safe-unquote (darg1 expr))))
               (mv (erp-nil)
                   (list* "("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          (nat-to-string-debug (+ -1 width))
                          ":0])")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvsx ;; (bvsx new-size old-size val)
         ;; fixme, do I need to add a bracket expression at the end of this?
         (if (and (= 3 (len (dargs expr)))
                  (quoted-natp (darg1 expr)) ;can this be 0?
                  (quoted-posp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (mv (erp-nil)
                 (list*
                  "BVSX("
                  (translate-bv-arg (darg3 expr) (safe-unquote (darg2 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                  ;;fffixme chop here!?
                  ", "
                  (nat-to-string-debug (safe-unquote (darg1 expr)))
                  ")")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (slice ;; (slice high low x)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-natp (darg1 expr))
                  (quoted-natp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let ((high (safe-unquote (darg1 expr))))
               (mv (erp-nil)
                   (list* "("
                          (translate-bv-arg (darg3 expr) (+ 1 high) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          (nat-to-string-debug high)
                          ":"
                          (nat-to-string-debug (safe-unquote (darg2 expr)))
                          "])")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (getbit ;; (getbit n x)
         (if (and (= 2 (len (dargs expr)))
                  (quoted-natp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (let* ((bitnum (safe-unquote (darg1 expr)))
                        (bitnum-string (nat-to-string-debug bitnum)))
                   (list* "("
                          (translate-bv-arg (darg2 expr) (+ 1 bitnum) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          bitnum-string
                          ":"
                          bitnum-string
                          "])"))
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitxor ;; (bitxor x y)
         (if (and (= 2 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "(BVXOR("
                        (translate-bv-arg (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0],"
                        (translate-bv-arg (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0]))")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitor ;; (bitor x y)
         (if (and (= 2 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "("
                        (translate-bv-arg (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0] | "
                        (translate-bv-arg (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0])")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitand ;; (bitand x y)
         (if (and (= 2 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "("
                        (translate-bv-arg (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0] & "
                        (translate-bv-arg (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0])")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (bitnot ;; (bitnot x)
         (if (and (= 1 (len (dargs expr)))
                  (bv-arg-okp (darg1 expr)))
             (mv (erp-nil)
                 (list* "(~"
                        (translate-bv-arg (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "[0:0]) ")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (sbvlt ;; (sbvlt size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(SBVLT("
                          ;;fixme could add the brackets to translate-bv-arg?
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0], "
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (sbvle ;; (sbvle size x y)
         ;; TODO: Consider omitting this and instead introducing sbvlt through rewriting
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(SBVLE("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0], "
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvlt ;; (bvlt size x y)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(BVLT("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0], "
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvle ;; (bvle size x y)
         ;; TODO: Consider omitting this and instead introducing sbvlt through rewriting
         ;;fixme either drop this or add support for the other operators: bvge, etc. (same for the signed comparisons)
         (if (and (= 3 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv (erp-nil)
                   (list* "(BVLE("
                          (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0], "
                          (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                          "["
                          top-bit-string
                          ":0]))")
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bvcat ;; (bvcat highsize highval lowsize lowval)
         (if (and (= 4 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (bv-arg-okp (darg2 expr))
                  (quoted-posp (darg3 expr))
                  (bv-arg-okp (darg4 expr)))
             (mv (erp-nil)
                 (list* "("
                        (translate-bv-arg (darg2 expr) (safe-unquote (darg1 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "["
                        (nat-to-string-debug (+ -1 (safe-unquote (darg1 expr))))
                        ":0]@"
                        (translate-bv-arg (darg4 expr) (safe-unquote (darg3 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                        "["
                        (nat-to-string-debug (+ -1 (safe-unquote (darg3 expr))))
                        ":0])")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (leftrotate32 ;; (leftrotate32 amt val)
         ;;fixme handle leftrotate with any power of 2 size?
         (if (and (= 2 (len (dargs expr)))
                  (quoted-natp (darg1 expr)) ;todo: think about 0
                  (bv-arg-okp (darg2 expr)))
             (let* ((shift-amt (safe-unquote (darg1 expr))) ;fixme what if it's not a natp?
                    (shift-amt (mod shift-amt 32)))
               (if (= 0 shift-amt) ;in this case, it's just like bvchop (handling 0 separately avoids an error in the main case, a slice of [31:32])
                   (mv (erp-nil)
                       (list* "("
                              (translate-bv-arg (darg2 expr) 32 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                              "[31:0])")
                       constant-array-info)
                 ;;main case:
                 (let ((low-slice-size (- 32 shift-amt)) ;bad name?
                       ;;high-slice-size is shift-amt
                       )
                   (mv (erp-nil)
                       (list* "("
                              (translate-bv-arg (darg2 expr) 32 ;or should we use low-slice-size?
                                                dag-array-name dag-array dag-len cut-nodenum-type-alist)
                              "["
                              (nat-to-string-debug (+ -1 low-slice-size))
                              ":0]@"
                              (translate-bv-arg (darg2 expr) 32 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                              "[31:"
                              (nat-to-string-debug low-slice-size) "])")
                       constant-array-info))))
           (mv (erp-t) nil constant-array-info)))
        (equal
         (if (= 2 (len (dargs expr)))
             (mv-let (translated-expr constant-array-info)
               (translate-equality (darg1 expr)
                                   (darg2 expr)
                                   dag-array-name dag-array cut-nodenum-type-alist constant-array-info)
               (mv (erp-nil)
                   translated-expr
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))

        ;;                                               (let* ((lhs (darg1 expr)) ;are these nodenums-or-quoteps, or what?
        ;;                                                      (rhs (darg2 expr))
        ;;                                                      (lhs-size (get-size-of-expr3-old lhs dag-array var-type-alist))
        ;;                                                      (rhs-size (get-size-of-expr3-old rhs dag-array var-type-alist))

        ;;                                                      (max-size (max rhs-size lhs-size)))

        ;;                                                 (list* "("
        ;;                                                                  (translate-bv-arg lhs max-size dag-array var-type-alist)
        ;;                                                                  ;;(translate-arg-auto-sized lhs)
        ;;                                                                  "="
        ;;                                                                  (translate-bv-arg rhs max-size dag-array var-type-alist)
        ;;                                                                  ;;(translate-arg-auto-sized rhs)
        ;;                                                                  ")"))

        (bvif ;; (bvif size test thenpart elsepart)
         ;;skip the outer bracket expression (or the 2 inner ones?)
         (if (and (= 4 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (boolean-arg-okp (darg2 expr))
                  (bv-arg-okp (darg3 expr))
                  (bv-arg-okp (darg4 expr)))
             (let* ((width (safe-unquote (darg1 expr)))
                    (top-bit-string (nat-to-string-debug (+ -1 width))))
               (mv
                (erp-nil)
                (list* "(IF "
                       (translate-boolean-arg (darg2 expr))
                       " THEN "
                       (translate-bv-arg (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                       "["
                       top-bit-string
                       ":0] ELSE "
                       (translate-bv-arg (darg4 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                       "["
                       top-bit-string
                       ":0] ENDIF)[" ;drop this chop?:
                       top-bit-string
                       ":0]"
                       )
                constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (bv-array-if ;(bv-array-if element-width length test thenpart elsepart)
         (if (and (= 5 (len (dargs expr)))
                  (quoted-posp (darg1 expr))
                  (quoted-natp (darg2 expr)) ;exclude 0? exclude 1?
                  (boolean-arg-okp (darg3 expr)))
             (b* ((element-width (safe-unquote (darg1 expr)))
                  (length (safe-unquote (darg2 expr)))
                  (test (darg3 expr))
                  (then-branch (darg4 expr))
                  (else-branch (darg5 expr))
                  ((mv then-array-name constant-array-info &)
                   (translate-array-arg then-branch element-width length dag-array-name dag-array cut-nodenum-type-alist 'bv-array-if t constant-array-info))
                  ((mv else-array-name constant-array-info &)
                   (translate-array-arg else-branch element-width length dag-array-name dag-array cut-nodenum-type-alist 'bv-array-if t constant-array-info)))
               (mv
                (erp-nil)
                (list* "(IF "
                       (translate-boolean-arg test)
                       " THEN "
                       then-array-name
                       " ELSE "
                       else-array-name
                       " ENDIF)")
                constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (t (mv (erp-t) nil constant-array-info)))
      (if erp
          (prog2$ (er hard? 'translate-dag-expr "Unrecognized expr: ~x0.~%" expr)
                  ;;todo: pass back the error?
                  (mv nil constant-array-info))
        (mv translated-expr constant-array-info)))))

(defthm string-treep-of-mv-nth-0-of-translate-dag-expr
  (implies (and (bounded-dag-exprp dag-len expr)
                (constant-array-infop constant-array-info))
           (string-treep (mv-nth 0 (translate-dag-expr expr
                                                       dag-array-name
                                                       dag-array dag-len constant-array-info
                                                       cut-nodenum-type-alist))))
  :hints (("Goal" :in-theory (e/d (translate-dag-expr
                                   bounded-dag-exprp
                                   car-becomes-nth-of-0
                                   )
                                  ((:e nat-to-string-debug) ;problem!
                                   ;;for speed:
                                   nat-to-string-debug
                                   translate-array-arg
                                   translate-bv-arg
                                   pad-with-zeros
                                   max)))))

;just use repeat?
;optimize?
(defun n-close-parens (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      acc
    (n-close-parens (+ -1 n) (cons ")" acc))))

(defthm string-listp-of-n-close-parens
  (equal (string-listp (n-close-parens n acc))
         (string-listp acc)))

(defthm true-listp-of-n-close-parens
  (equal (true-listp (n-close-parens n acc))
         (true-listp acc)))

(defthm constant-array-infop-of-mv-nth-1-of-translate-equality
  (implies (and (constant-array-infop constant-array-info)
;                (nat-listp (unquote data))
  ;              (natp element-width)
   ;             (natp element-count)
    ;            (<= element-count (len (unquote data)))
                )
           (constant-array-infop (mv-nth 1 (translate-equality lhs rhs dag-array-name dag-array nodenum-type-alist constant-array-info))))
  :hints (("Goal" :in-theory (enable translate-equality))))

(in-theory (disable (:e nat-to-string)))

(defthm constant-array-infop-of-mv-nth-1-of-translate-dag-expr
  (implies (and (bounded-dag-exprp dag-len expr)
                (constant-array-infop constant-array-info))
           (constant-array-infop (mv-nth 1 (translate-dag-expr expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist))))
  :hints (("Goal" :in-theory (enable translate-dag-expr bounded-dag-exprp
                                     car-becomes-nth-of-0))))

;; (defthm <-of-maxelem-of-cdr
;;   (implies (and (all-< items x)
;;                 (< 1 (len items)))
;;            (< (maxelem (cdr items)) x))
;;   :hints (("Goal" :in-theory (enable all-< maxelem))))

;; (defthm <=-of-0-and-maxelem
;;   (implies (and (nat-listp x)
;;                 (<= 1 (len x)))
;;            (<= 0 (maxelem x)))
;;   :hints (("Goal" :in-theory (enable nat-listp maxelem))))

;; (defthm integerp-of-maxelem-when-nat-listp
;;   (implies (and (nat-listp x)
;;                 (<= 1 (len x)))
;;            (integerp (maxelem x)))
;;   :hints (("Goal" :in-theory (enable nat-listp maxelem))))

(defthm nat-listp-of-cdr
  (implies (nat-listp x)
           (nat-listp (cdr x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

(defthmd integer-listp-when-nat-listp
  (implies (nat-listp x)
           (integer-listp x))
  :hints (("Goal" :in-theory (enable integer-listp))))

(defthm nat-listp-forward-to-all-integerp
  (implies (nat-listp x)
           (all-integerp x))
  :rule-classes :forward-chaining)

;returns (mv translation constant-array-info opened-paren-count) where TRANSLATION is a string-tree
;handles nodes nodenum down through 0 (translates those which have been tagged for translation)
;could use a worklist?
(defund translate-nodes-to-stp (nodenums-to-translate ;sorted in decreasing order
                                dag-array-name
                                dag-array
                                dag-len
                                acc ;a string-tree, this should have the translated query (e.g., equality of two nodenums)
                                constant-array-info
                                opened-paren-count
                                cut-nodenum-type-alist
                                )
;  (declare (xargs :measure (nfix (+ 1 nodenum))))
  (declare (xargs :guard (and (nat-listp nodenums-to-translate)
                              (natp opened-paren-count)
                              (constant-array-infop constant-array-info)
                              (alistp cut-nodenum-type-alist)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums-to-translate dag-len)
                              (string-treep acc))
                  :guard-hints (("Goal" :in-theory (enable <-of-nth-when-all-<
                                                           car-becomes-nth-of-0
                                                           integer-listp-when-nat-listp
                                                           not-cddr-when-dag-exprp0-and-quotep)))))
  (if (endp nodenums-to-translate)
      (mv acc constant-array-info opened-paren-count)
    (let* ((nodenum (first nodenums-to-translate))
           (expr (aref1 dag-array-name dag-array nodenum)))
      (if (variablep expr) ;ffixme! we always cut at vars (do we still need to check this or is the tag clear for vars)?
          (translate-nodes-to-stp (rest nodenums-to-translate) dag-array-name dag-array dag-len acc constant-array-info opened-paren-count cut-nodenum-type-alist)
        ;; the node is to be translated...
        (mv-let (translated-expr constant-array-info)
          (translate-dag-expr expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist)
          (translate-nodes-to-stp (rest nodenums-to-translate)
                                  dag-array-name dag-array dag-len
                                  (list* "LET "
                                         (makevarname nodenum) ;ffixme any possible name clashes?
                                         " = "
                                         translated-expr
                                         " IN (" (newline-string)
                                         acc)
                                  constant-array-info
                                  (+ 1 opened-paren-count)
                                  cut-nodenum-type-alist))))))

;todo
;; (thm
;;  (implies
;;   (CONSTANT-ARRAY-INFOP CONSTANT-ARRAY-INFO)
;;   (CONSTANT-ARRAY-INFOP
;;    (MV-NTH 1
;;            (TRANSLATE-DAG-EXPR expr DAG-ARRAY-NAME DAG-ARRAY CONSTANT-ARRAY-INFO CUT-NODENUM-TYPE-ALIST))))
;;  :hints (("Goal" :in-theory (e/d (TRANSLATE-DAG-EXPR) ((:e NAT-TO-STRING-DEBUG))))))

;todo
;; (thm
;;  (implies (and (constant-array-infop constant-array-info))
;;           (constant-array-infop (mv-nth 1
;;                                         (translate-nodes-to-stp nodenums-to-translate dag-array-name
;;                                                                    dag-array translated-query-core
;;                                                                    constant-array-info
;;                                                                    opened-paren-count cut-nodenum-type-alist))))
;;  :hints (("Goal" :in-theory (enable translate-nodes-to-stp)))

;fffixme think about arrays whose lengths are not powers of 2...
;returns string-tree
(defun make-stp-type-declarations (nodenum-type-alist)
  (declare (xargs :guard (nodenum-type-alistp nodenum-type-alist) ;;TODO: This also allows :range types but axe-typep doesn't allow range types?
                  :guard-hints (("Goal" :expand (nodenum-type-alistp nodenum-type-alist)
                                 :in-theory (e/d (axe-typep empty-typep list-typep most-general-typep)
                                                 (boolean-typep))))))
  (if (endp nodenum-type-alist)
      nil
    (let* ((entry (first nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry))
           (varname (makevarname nodenum)) ;todo: store these in an array?
           )
      (if (bv-typep type)
          (list* varname
                 " : BITVECTOR("
                 (nat-to-string-debug (bv-type-width type))
                 ");" (newline-string)
                 (make-stp-type-declarations (rest nodenum-type-alist)))
        (if (bv-array-typep type) ;a certain kind of :list type
            (let* ((element-size (bv-array-type-element-width type))
                   (len (bv-array-type-len type)))
              (if (< len 2)
                  ;; An array in STP has to have a index with at least one bit, hence at least 2 elements:
                  (er hard? 'make-stp-type-declarations "Found an array of length 0 or 1 (neither is supported): ~x0." entry)
                (list* varname
                       " : ARRAY BITVECTOR("
                       (nat-to-string-debug (integer-length (+ -1 len)))
                       ") OF BITVECTOR("
                       (nat-to-string-debug element-size)
                       ");"
                       (newline-string)
                       (make-stp-type-declarations (rest nodenum-type-alist)))))
          (if (boolean-typep type)
              (list* varname
                     " : BOOLEAN;"
                     (newline-string)
                     (make-stp-type-declarations (rest nodenum-type-alist)))
            (if (call-of :range type)
                (er hard 'make-stp-type-declarations "range type detected.")
                ;; (let* ( ;(low (second type))
                ;;        (high (third type))
                ;;        (width (integer-length high)))
                ;;   (list* varname
                ;;          " : BITVECTOR("
                ;;          (nat-to-string-debug width)
                ;;          ");"
                ;;          (newline-string)
                ;;          (make-stp-type-declarations (rest nodenum-type-alist))))
              ;todo: prove this doesn't happen:
              (er hard? 'make-stp-type-declarations "Unknown form for type: ~x0." type))))))))

;; Returns string-tree.
(defun make-stp-range-assertions (nodenum-type-alist)
  (declare (xargs :guard (nodenum-type-alistp nodenum-type-alist) ;;TODO: This also allows :range types but axe-typep doesn't allow range types?
                  :guard-hints (("Goal" :expand (nodenum-type-alistp nodenum-type-alist)
                                 :in-theory (e/d (axe-typep empty-typep list-typep most-general-typep)
                                                 (boolean-typep))))))
  (if (endp nodenum-type-alist)
      nil
    (let* ((entry (first nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry)))
      (if (consp type)
          (if (bv-array-typep type) ;; nothing to do:
              (make-stp-range-assertions (rest nodenum-type-alist))
            (if (boolean-typep type) ;; nothing to do:
                (make-stp-range-assertions (rest nodenum-type-alist))
              (if (eq :range (car type))
                  (let* ((low (second type))
                         (high (third type))
                         (width (integer-length high))
                         (varname (makevarname nodenum)))
                    (list* "ASSERT(BVLE("
                           (translate-bv-constant low width)
                           ","
                           varname
                           "));"
                           (newline-string)
                           "ASSERT(BVLE("
                           varname
                           ","
                           (translate-bv-constant high width)
                           "));"
                           (newline-string)
                           (make-stp-range-assertions (rest nodenum-type-alist))))
                (er hard? 'make-stp-range-assertions "Unknown form for size: ~x0." type))))
        (make-stp-range-assertions (rest nodenum-type-alist))))))

;; Returns a string-tree.
;make tail rec?
(defun make-type-declarations-for-array-constants (constant-array-info)
  (declare (xargs :guard (constant-array-infop constant-array-info)
                  :guard-hints (("Goal" :in-theory (enable constant-array-infop)))))
  (if (endp constant-array-info)
      nil
    (let* ((entry (first constant-array-info))
           ;; (constant-data (first entry))
           (array-name (second entry))
           (element-width (third entry))
           (element-count (fourth entry))
           ;;If the array constant has a length that is not a power of 2, this rounds up the length to the next power of 2 (fffixme what if element-count is 1 or 0???)
           (index-width (integer-length (+ -1 element-count)))
           )
      (list* array-name
             " : ARRAY BITVECTOR("
             (nat-to-string-debug index-width) ;fixme throw an error if this is 0
             ") OF BITVECTOR("
             (nat-to-string-debug element-width)
             ");"
             (newline-string)
             (make-type-declarations-for-array-constants (rest constant-array-info))))))

; Returns a string-tree.
;fixme this used to generate too many asserts (which could contradict each other!) if the data is longer than would be expected for the index...  now it counts up to element-count
(defun make-value-assertions-for-array-constant (array-data array-name elemnum element-count index-size element-size acc)
  (declare (xargs :guard (and (natp elemnum)
                              (natp index-size)
                              (posp element-size)
                              (natp element-count)
                              (nat-listp array-data)
                              (<= (- element-count elemnum) (len array-data))
                              )
                  :measure (nfix (+ 1 (- element-count elemnum)))))
  (if (or (<= element-count elemnum)
          (not (natp element-count))
          (not (natp elemnum)))
      acc
    (make-value-assertions-for-array-constant (cdr array-data)
                                              array-name
                                              (+ 1 elemnum)
                                              element-count
                                              index-size element-size
                                              ;;fixme we could speed this up by precomputing stuff that doesn't change between elements
                                              (list* "ASSERT "
                                                     array-name
                                                     "[0bin"
                                                     ;;call a version that returns a list of strings
                                                     (translate-bits elemnum (+ -1 index-size)) ;don't redo the -1
                                                     "]="
                                                     ;;fixme inline and call a version that returns a list of strings
                                                     (translate-bv-constant (car array-data) element-size)
                                                     ";"
                                                     (newline-string)
                                                     acc))))

;; Returns a string-tree.
(defun make-value-assertions-for-array-constants (constant-array-info acc)
  (declare (xargs :guard (constant-array-infop constant-array-info)
                  :guard-hints (("Goal" :in-theory (enable constant-array-infop)))))
  (if (endp constant-array-info)
      acc
    (let* ((entry (first constant-array-info))
           (constant-data (first entry))
           (array-name (second entry))
           (element-width (third entry))
           (element-count (fourth entry))
           (index-size (ceiling-of-lg element-count)) ;FIXME: What if this is not at least 1?
           )
      (make-value-assertions-for-array-constants
       (rest constant-array-info)
       (make-value-assertions-for-array-constant constant-data array-name 0 element-count index-size element-width acc)))))

(defthm string-treep-of-n-close-parens
  (implies (string-treep acc)
           (string-treep (n-close-parens n acc))))

(defthm string-treep-of-make-stp-range-assertions
  (string-treep (make-stp-range-assertions cut-nodenum-type-alist))
  :hints (("Goal" :in-theory (enable make-stp-range-assertions))))

(defthm string-treep-of-make-type-declarations-for-array-constants
  (implies (constant-array-infop constant-array-info)
           (string-treep (make-type-declarations-for-array-constants constant-array-info)))
  :hints (("Goal" :in-theory (enable make-type-declarations-for-array-constants constant-array-infop))))

(defthm string-treep-of-make-stp-type-declarations
  (string-treep (make-stp-type-declarations nodenum-type-alist))
  :hints (("Goal" :in-theory (enable make-stp-type-declarations))))

(defthm string-treep-of-make-value-assertions-for-array-constant
  (implies (and (string-treep acc)
                (string-treep array-name))
           (string-treep (make-value-assertions-for-array-constant array-data array-name elemnum element-count index-size element-size acc)))
  :hints (("Goal" :in-theory (enable make-value-assertions-for-array-constant))))

(defthm string-treep-of-make-value-assertions-for-array-constants
  (implies (and (string-treep acc)
                (constant-array-infop constant-array-info))
           (string-treep (make-value-assertions-for-array-constants constant-array-info acc)))
  :hints (("Goal" :in-theory (enable make-value-assertions-for-array-constants
                                     make-value-assertions-for-array-constant
                                     constant-array-infop))))

(defthm natp-of-mv-nth-2-of-translate-nodes-to-stp
  (implies (natp opened-paren-count)
           (natp
            (mv-nth 2
                    (translate-nodes-to-stp nodenums-to-translate dag-array-name
                                            dag-array dag-len acc
                                            constant-array-info
                                            opened-paren-count cut-nodenum-type-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable translate-nodes-to-stp))))

(defthm string-treep-of-mv-nth-0-of-translate-nodes-to-stp
  (implies (and (string-treep acc)
                (constant-array-infop constant-array-info)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (nat-listp nodenums-to-translate)
                (all-< nodenums-to-translate dag-len))
           (string-treep
            (mv-nth 0
                    (translate-nodes-to-stp nodenums-to-translate dag-array-name
                                            dag-array dag-len acc
                                            constant-array-info
                                            opened-paren-count cut-nodenum-type-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable translate-nodes-to-stp nat-listp))))

(defthm constant-array-infop-of-mv-nth-1-of-translate-nodes-to-stp
  (implies (and (constant-array-infop constant-array-info )
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (nat-listp nodenums-to-translate)
                (all-< nodenums-to-translate dag-len))
           (constant-array-infop
            (mv-nth 1
                    (translate-nodes-to-stp nodenums-to-translate dag-array-name
                                            dag-array dag-len acc
                                            constant-array-info
                                            opened-paren-count cut-nodenum-type-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable translate-nodes-to-stp nat-listp))))

;returns (mv erp state)
;translates the DAG to STP and writes the result to FILENAME
;also handle vars with dashes in their names!
;Also prints the filename
(defund write-stp-query-to-file (translated-query-core ; a string-tree, mentions nodes in the dag-array
                                 dag-array-name
                                 dag-array
                                 dag-len
                                 nodenums-to-translate ;sorted in decreasing order
                                 extra-asserts
                                 filename
                                 cut-nodenum-type-alist
                                 constant-array-info
                                 state)
  (declare (xargs :stobjs state
                  :guard (and (string-treep translated-query-core)
                              (symbolp dag-array-name)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp nodenums-to-translate)
                              (all-< nodenums-to-translate dag-len)
                              (string-treep extra-asserts)
                              (stringp filename)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (constant-array-infop constant-array-info)
                              )))
  (prog2$
   (cw "  ~s0~%" filename)
   (mv-let (translation constant-array-info opened-paren-count)
     (translate-nodes-to-stp nodenums-to-translate
                             dag-array-name
                             dag-array
                             dag-len
                             translated-query-core
                             constant-array-info
                             0 ;opened-paren-count
                             cut-nodenum-type-alist
                             )
     (write-string-tree!
      (list* (make-stp-type-declarations cut-nodenum-type-alist)
             (make-stp-range-assertions cut-nodenum-type-alist)
             (make-type-declarations-for-array-constants constant-array-info)
             (make-value-assertions-for-array-constants constant-array-info nil)
             extra-asserts
             "QUERY (" (newline-string)
             translation                             ;includes the query..
             (n-close-parens opened-paren-count nil) ;don't bother to cons this up?
             ");" (newline-string))
      filename
      'write-stp-query-to-file
      state))))

(local (in-theory (disable subseq take)))

;; We use these constants instead of their corresponding keywords, so that we
;; don't accidentally mis-type the keywords:
(defconst *error* :error)
(defconst *valid* :valid)
(defconst *invalid* :invalid)
(defconst *timedout* :timedout)
(defconst *counterexample* :counterexample)
(defconst *possible-counterexample* :possible-counterexample)

;INPUT-FILENAME is the STP input (.cvc) file name
;OUTPUT-FILENAME is the STP output (.out) file name
;Runs an external script to call STP, using sys-call.
;FFIXME think about which STP options to use. pass them in via this function?
;Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, or (:counterexample <raw-counterexample>)
;; We don't fix up the counterexample here because we don't have access to the cut-nodenum-type-alist, etc.
(defund call-stp-on-file (input-filename
                         output-filename
                         print ;whether to print the result (valid/invalid/timeout)
                         timeout ;a number of seconds (now conflicts!), or nil for no timeout
                         counterexamplep
                         state)
  (declare (xargs :stobjs state
                  :guard (and (stringp input-filename)
                              (stringp output-filename)
                              ;;(booleanp print)
                              (or (null timeout)
                                  (natp timeout))
                              (booleanp counterexamplep))))
  (let ((counterexample-arg (if counterexamplep "y" "n")))
    (mv-let
      (status state)
      (if timeout ;;timeout is the the number of seconds (now conflicts!):
          (call-axe-script "callstplimited.bash" (list input-filename output-filename (nat-to-string timeout) counterexample-arg) state)
        ;;don't time out:
        (call-axe-script "callstp.bash" (list input-filename output-filename counterexample-arg) state))
      ;;(prog2$ (cw "sys-call status: ~x0~%" status)
      ;;(STP seems to exit with status 0 for both Valid and Invalid examples and with non-zero status for errors.)
      (if (not (eql 0 status)) ;;todo: do we still need to do all these checks?
          (if (eql 143 status)
              ;;exit status 143 seems to indicate timeout (why?!  perhaps it's 128+15 where 15 represents the TERM signal)
              (prog2$ (cw "!! STP timed out !!")
                      (mv *timedout* state))
            (if (eql 201 status)
                (progn$ (er hard? 'call-stp-on-file "!! ERROR: Unable to find STP (define an STP environment var or add its location to your path) !!")
                        (mv *error* state))
              ;; TODO: What is exit status 134?
              (progn$ (er hard? 'call-stp-on-file "!! ERROR: STP experienced an unknown error (exit status ~x0) !!" status)
                      (mv *error* state))))
        ;;check whether the output file contains "Valid."
        (mv-let (errmsg/contents state)
          ;; we just need to check whether the output file starts with the characters "Valid."
          (read-file-characters output-filename state)
          (if (stringp errmsg/contents) ;a string means error
              (prog2$ (er hard? 'call-stp-on-file "Unable to read STP output from file ~x0.  Message is: ~s1.~%" output-filename errmsg/contents)
                      (mv *error* state))
            (let ((chars errmsg/contents))
              (if (equal chars '(#\V #\a #\l #\i #\d #\. #\Newline)) ;;Look for "Valid."
                  (prog2$ (and print (cw "  STP said Valid."))
                          (mv *valid* state))
                ;; Test whether chars end with "Invalid.", perhaps preceded by a printed counterexample.
                (if (and (<= 9 (len chars)) ;9 is the length of "Invalid." followed by newline - todo make a function 'char-list-ends-with'
                         (equal (nthcdr (- (len chars) 9) chars)
                                '(#\I #\n #\v #\a #\l #\i #\d #\. #\Newline))) ;;Look for "Invalid."
                    (b* ((- (and print (cw "  STP said Invalid.~%")))
                         ;; Print the counterexample (TODO: What if it is huge?):
                         (counterexamplep-chars (butlast chars 9))
                         ;(- (and print counterexamplep (cw "~%Counterexample:~%~S0" (coerce counterexamplep-chars 'string))))
                         (parsed-counterexample (parse-counterexample counterexamplep-chars nil))
                         ;(- (and print counterexamplep (cw "~%Parsed counterexample:~%~x0~%" parsed-counterexample)))
                         )
                      (mv (if counterexamplep
                              `(,*counterexample* ,parsed-counterexample)
                            *invalid*)
                          state))
                  (if (or ;(equal chars '(#\T #\i #\m #\e #\d #\Space #\O #\u #\t #\, #\Space  #\e #\x #\i #\t #\i #\n #\g #\.)) ;add newline??
                       (equal chars '(#\T #\i #\m #\e #\d #\Space #\O #\u #\t #\. #\Newline))) ;;Look for "Timed Out."
                      (prog2$ (and print (cw "  STP timed out."))
                              (mv *timedout* state))
                    (prog2$ (er hard? 'call-stp-on-file "STP returned an unexpected result (~x0).  Check the .out file: ~x1.~%" chars output-filename)
                            (mv *error* state))))))))))))

(defthm call-stp-on-file-return-type
  (let ((res (mv-nth 0 (call-stp-on-file
                        input-filename
                        output-filename
                        print ;whether to print the result (valid/invalid/timeout)
                        timeout ;a number of seconds (now conflicts!), or nil for no timeout
                        counterexamplep
                        state
                        ))))
    (implies (and (not (equal *error* res))
                  (not (equal *valid* res))
                  (not (equal *invalid* res))
                  (not (equal *timedout* res)))
             (and (true-listp res)
                  (equal (car res) *counterexample*)
                  (raw-counterexamplep (second res))
                  (equal (len res) 2))))
  :hints (("Goal" :in-theory (enable call-stp-on-file))))

(defthm raw-counterexamplep-of-cadr-of-mv-nth-0-of-call-stp-on-file
  (implies (consp (mv-nth 0 (call-stp-on-file input-filename output-filename print timeout counterexamplep state)))
           (raw-counterexamplep (cadr (mv-nth 0 (call-stp-on-file input-filename output-filename print timeout counterexamplep state)))))
  :hints (("Goal" :in-theory (enable call-stp-on-file))))

(defthm len-of-mv-nth-0-of-call-stp-on-file
  (implies (consp (mv-nth 0 (call-stp-on-file input-filename output-filename print timeout counterexamplep state)))
           (equal (len (mv-nth 0 (call-stp-on-file input-filename output-filename print timeout counterexamplep state)))
                  2))
  :hints (("Goal" :in-theory (e/d (call-stp-on-file) (;LIST::EQUAL-CONS-CASES
                                                      )))))

(defund print-counterexample (cex dag-array-name dag-array)
  (declare (xargs :guard (and (counterexamplep cex)
                              (if (consp cex)
                                  (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem (strip-cars cex))))
                                t))))
  (if (endp cex)
      nil
    (b* ((entry (first cex))
         (nodenum (car entry))
         (value (cdr entry))
         ;(expr (aref1 dag-array-name dag-array nodenum))
         (expr (dag-to-term-aux-array dag-array-name dag-array nodenum))
         (- (cw "  Node ~x0: ~x1 is ~x2." nodenum expr value))
         ;; Print newline unless this is the last line:
         (- (and (consp (rest cex)) (cw "~%"))))
      (print-counterexample (rest cex) dag-array-name dag-array))))

(defund maybe-shorten-filename (base-filename)
  (declare (xargs :guard (stringp base-filename)))
  (if (< 200 (length base-filename)) ;fixme could increase the 200
      ;;shorten the filename if it would be too long:
      (string-append (subseq base-filename 0 199) "SHORTENED")
    base-filename))

;; TODO: What if we cut out some structure but it is not involved in the counterexample?
(defun all-cuts-are-at-vars (cut-nodenum-type-alist dag-array-name dag-array)
  (declare (xargs :guard (and (nodenum-type-alistp cut-nodenum-type-alist)
                              (symbolp dag-array-name)
                              (array1p dag-array-name dag-array)
                              (all-< (strip-cars cut-nodenum-type-alist)
                                     (alen1 dag-array-name dag-array)))
                  :guard-hints (("Goal" :in-theory (enable nodenum-type-alistp)))))
  (if (endp cut-nodenum-type-alist)
      t
    (and (let* ((entry (first cut-nodenum-type-alist))
                (nodenum (car entry)))
           (symbolp (aref1 dag-array-name dag-array nodenum)))
         (all-cuts-are-at-vars (rest cut-nodenum-type-alist) dag-array-name dag-array))))

;; BASE-FILENAME gets .cvc and .out extensions added to it (will be shortenend if it's too long)
;Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, or (:counterexample <counterexample>), or (:possible-counterexample <counterexample>)
(defund prove-query-with-stp (translated-query-core ; a string-tree, mentions nodenums in the dag-array, often a translated equality or disjunction
                              extra-string ;printed after "Calling STP"
                              dag-array-name
                              dag-array
                              dag-len
                              nodenums-to-translate ;sorted in decreasing order
                              extra-asserts
                              base-filename
                              cut-nodenum-type-alist ;tells the types of vars introduced at the cuts (some may be true input vars)
                              print
                              timeout ;a number of seconds (now conflicts!), or nil for no timeout
                              constant-array-info ;may get an entry when we create translated-query-core (e.g., if a term is equated to a constant array)
                              counterexamplep
                              state)
  (declare (xargs :stobjs state
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable PSEUDO-DAG-ARRAYP ;todo
                                                    )))
                  :guard (and (nat-listp nodenums-to-translate)
                              (stringp extra-string)
                              (string-treep extra-asserts)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              ;;(consp nodenums-to-translate) ;think
                              (stringp base-filename)
                              (or (null timeout)
                                  (natp timeout))
                              (booleanp counterexamplep)
                              (symbolp dag-array-name)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums-to-translate dag-len)
                              (all-< (strip-cars cut-nodenum-type-alist) ;drop?
                                     (alen1 dag-array-name dag-array))
                              (all-< (strip-cars cut-nodenum-type-alist)
                                     dag-len)
                              (string-treep translated-query-core)
                              (constant-array-infop constant-array-info))))
  (b* (((mv temp-dir-name state)
        (maybe-make-temp-dir state))
       (base-filename (concatenate 'string temp-dir-name "/" base-filename))
       (base-filename (maybe-shorten-filename base-filename))
       (- (and print (cw "(Calling STP ~s0 (timeout ~x1):~%" extra-string timeout)))
       (stp-input-filename (string-append base-filename ".cvc"))
       (stp-output-filename (string-append base-filename ".out"))
       ;;write the STP file...
       ((mv erp state)
        (write-stp-query-to-file translated-query-core
                                 dag-array-name dag-array dag-len
                                 nodenums-to-translate ;sorted in decreasing order
                                 extra-asserts
                                 stp-input-filename
                                 cut-nodenum-type-alist
                                 constant-array-info
                                 state))
       ((when erp)
        (er hard? 'prove-query-with-stp "Unable to write the STP input file: ~s0 before calling STP." stp-input-filename)
        (mv *error* state))
       ;;clear out the output file (test this)
       ;;this is in case something fails (like permissions) and the attempt to run STP leaves an old .out file in place
       ;;(which might have the wrong answer in it!)
       ((mv erp state)
        (write-strings-to-file! nil stp-output-filename 'prove-query-with-stp state)) ;todo: make a function to clear a file..
       ((when erp)
        (er hard? 'prove-query-with-stp "Unable to clear the output file: ~s0 before calling STP." stp-output-filename)
        (mv *error* state))
       ;; Call STP on the file:
       ((mv result state)
        (call-stp-on-file stp-input-filename stp-output-filename print timeout counterexamplep state))
       (counterexamplep (and (consp result)
                             (eq *counterexample* (car result)))) ;todo: maybe this should be labeled as :raw-counterexample?
       (counterexample
        (and counterexamplep
             (let ((raw-counterexample (cadr result)))
               (fixup-counterexample (sort-nodenum-type-alist cut-nodenum-type-alist) raw-counterexample))))
       (counterexample-certainp (and counterexamplep
                                     (all-cuts-are-at-vars cut-nodenum-type-alist dag-array-name dag-array)))
       (- (and counterexamplep
               (if counterexample-certainp
                   (cw "Counterexample is certain.~%") ;TODO actually test it by evaluating the DAG!
                 (cw "Counterexample is possible (may be spurious).~%"))))
       ;; Replace the raw with the fixed up counterexample:
       (result (if counterexamplep
                   (if counterexample-certainp
                       `(,*counterexample* ,counterexample)
                     `(,*possible-counterexample* ,counterexample))
                 result))
       (- (and print
               counterexamplep
               (b* ((- (cw "(Counterexample:~%"))
                    (- (print-counterexample counterexample dag-array-name dag-array))
                    (- (cw ")~%")))
                 nil)))
       ;; ((when (eq result *error*)) ;todo: can this happen or would a hard error have already been thrown?
       ;;  (progn$ (cw "!! ERROR !! Translated query core: ~x0~%" translated-query-core)
       ;;          (if nodenums-to-translate
       ;;              (print-dag-only-supporters-list nodenums-to-translate dag-array-name dag-array)
       ;;            (cw "No nodenums to translate!"))
       ;;          (cw "cut-nodenum-type-alist:~%")
       ;;          (print-list cut-nodenum-type-alist)
       ;;          (cw ; hard-error 'prove-query-with-stp
       ;;           "STP returned an error on input file ~s0 from translating the dag above. See output file ~s1.  Also, check file permissions.~%"
       ;;           ;;(acons #\0 stp-input-filename (acons #\1 stp-output-filename nil))
       ;;           stp-input-filename stp-output-filename
       ;;           )
       ;;          (and print (cw ")")) ;matches "(Calling STP"
       ;;          (mv *error* state)))
       (- (and print (cw ")~%"))) ;matches "(Calling STP"
       )
    ;;no error:
    (mv result state)))

(defthmd prove-query-with-stp-return-type
  (implies (nodenum-type-alistp cut-nodenum-type-alist)
           (let ((res (mv-nth 0 (prove-query-with-stp translated-query-core
                                                      extra-string
                                                      dag-array-name
                                                      dag-array
                                                      dag-len
                                                      nodenums-to-translate
                                                      extra-asserts
                                                      base-filename
                                                      cut-nodenum-type-alist
                                                      print
                                                      timeout
                                                      constant-array-info
                                                      counterexamplep
                                                      state))))
             (or (eq *error* res)
                 (eq *valid* res)
                 (eq *invalid* res)
                 (eq *timedout* res)
                 (and (true-listp res)
                      (eq (first res) *counterexample*)
                      (counterexamplep (second res))
                      (equal (len res) 2))
                 (and (true-listp res)
                      (eq (first res) *possible-counterexample*)
                      (counterexamplep (second res))
                      (equal (len res) 2)))))
  :hints (("Goal" :in-theory (enable prove-query-with-stp)
           :use ())))

;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>)
;; TODO: Unify param order with prove-query-with-stp
(defund prove-equality-query-with-stp (lhs ;a nodenum or quotep
                                       rhs ;a nodenum or quotep
                                       ;;todo: add an extra-string arg
                                       dag-array-name
                                       dag-array
                                       dag-len
                                       nodenums-to-translate ;sorted in decreasing order
                                       base-filename
                                       cut-nodenum-type-alist
                                       extra-asserts
                                       print
                                       timeout ;a number of seconds (now conflicts!), or nil for no timeout
                                       counterexamplep
                                       state)
  (declare (xargs :stobjs state
            :guard (and (or (myquotep rhs)
                            (and (natp rhs)
                                 (pseudo-dag-arrayp dag-array-name dag-array (+ 1 rhs))))
                        (or (myquotep lhs)
                            (and (natp lhs)
                                 (pseudo-dag-arrayp dag-array-name dag-array (+ 1 lhs))))
                        (booleanp counterexamplep)
                        (stringp base-filename)
                        (symbolp dag-array-name)
                        (consp nodenums-to-translate) ;why?
                        (nat-listp nodenums-to-translate)
                        (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                        (all-< nodenums-to-translate dag-len)
                        (natp timeout)
                        (nodenum-type-alistp cut-nodenum-type-alist)
                        (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                        (string-treep extra-asserts))))
  (mv-let (translated-expr constant-array-info)
    (translate-equality lhs rhs dag-array-name dag-array cut-nodenum-type-alist nil)
    (prove-query-with-stp translated-expr
                          "" ;extra-string: todo: use this
                          dag-array-name
                          dag-array
                          dag-len
                          nodenums-to-translate
                          extra-asserts
                          base-filename
                          cut-nodenum-type-alist
                          print timeout constant-array-info
                          counterexamplep
                          state)))

(defthmd prove-equality-query-with-stp-return-type
  (implies (nodenum-type-alistp cut-nodenum-type-alist)
           (let ((res (mv-nth 0 (prove-equality-query-with-stp lhs rhs
                                                               dag-array-name
                                                               dag-array
                                                               dag-len
                                                               nodenums-to-translate
                                                               base-filename
                                                               cut-nodenum-type-alist
                                                               extra-asserts
                                                               print
                                                               timeout
                                                               counterexamplep
                                                               state))))
             (or (eq *error* res)
                 (eq *valid* res)
                 (eq *invalid* res)
                 (eq *timedout* res)
                 (and (consp res)
                      (eq (first res) *counterexample*)
                      (counterexamplep (second res))
                      (null (cddr res)))
                 (and (consp res)
                      (eq (first res) *possible-counterexample*)
                      (counterexamplep (second res))
                      (null (cddr res))))))
  :hints (("Goal" :in-theory (enable prove-equality-query-with-stp)
           :use (:instance prove-query-with-stp-return-type
                           (translated-query-core (mv-nth 0
                                                          (translate-equality lhs rhs dag-array-name
                                                                              dag-array cut-nodenum-type-alist nil)))
                           (extra-string "")
                           (constant-array-info (mv-nth 1
                                                        (translate-equality lhs rhs dag-array-name
                                                                            dag-array cut-nodenum-type-alist nil)))))))

;get this working by generating an appropriate cut-nodenum-type-alist
;; ;pass in a dag-array-name?
;; ;; returns (mv validp timedoutp state) where validp indicates whether STP said "Valid."
;; (defun prove-with-stp-quick (dag-lst var-type-alist timeout state)
;;   (declare (xargs :mode :program
;;                   :stobjs state))
;;   (let* ((dag-array (make-into-array 'dag-array dag-lst))
;;          (dag-len (len dag-lst)))
;;     (prove-equality-query-with-stp (+ -1 dag-len) ;top node of the dag (we prove it equals true)
;;                              *t*
;;                              'dag-array
;;                              dag-array
;;                              :all ;ffixme what if there are non-pure operators?  should probably cut there!
;;                              "stpquick"
;;                              ;var-type-alist
;;                              nil ;cut-nodenum-type-alist fffixme!
;;                              nil t   ;print
;;                              timeout
;;                              state)))

;; ;; ;get this working again by generating an appropriate cut-nodenum-type-alist
;; ;dag-len might be smaller than the actual-len?
;; ;pass in a dag-array-name?
;; ;; returns (mv validp timedoutp state)
;; ;was called prove-whole-dag-with-stp before changes
;; (defun prove-array-node-with-stp (dag-array
;;                                   nodenum ;; the node to be proved true
;;                                   var-type-alist timeout state)
;;   (declare (xargs :mode :program
;;                   :stobjs state))
;;   (prove-equality-query-with-stp nodenum
;;                            *t*
;;                            'dag-array
;;                            dag-array
;;                            :all ;;ffffixme this may be overkill and may cause errors?  ;ffixme what if there are non-pure operators?  should probably cut there!
;;                            "stptmpfile"
;;                            ;var-type-alist
;;                            nil   ;cut-nodenum-type-alist
;;                           nil t     ;print
;;                            timeout
;;                            state))

;; ;now can return nil
;; (defun get-bit-vector-width-from-var-size-alist (var var-size-alist)
;;   (let ((type (lookup-eq var var-size-alist)))
;;     (if type
;;         (if (natp type)
;;             type
;;           (if (and (consp type)
;;                    (eq :range (car type)))
;;               (let* ((high (third type))
;;                      (size (ceiling-of-lg high)))
;;                 size)
;;             (hard-error 'get-bit-vector-width-from-var-size-alist "bad type : ~x0" (acons #\0 type nil))))
;;       nil ;(hard-error 'get-bit-vector-width-from-var-size-alist "no type found for var ~x0 in alist ~x1"
;;     ;              (acons #\0 var (acons #\1 var-size-alist nil)))
;;     )))

;; (skip -proofs (verify-guards get-bit-vector-width-from-var-size-alist))

;; (defun get-size-of-bit-vector-expr (expr nodenum var-size-alist)
;;   (if (variablep expr)
;;       (let ((width (get-bit-vector-width-from-var-size-alist expr var-size-alist)))
;;         (if width
;;             width
;; ;repeated below:
;;           (let* ((varname (pack$ 'node nodenum))
;;                  (type (lookup-eq varname var-size-alist)))
;;             (if (natp type)
;;                 type
;;               (hard-error 'get-size-of-bit-vector-expr "can't find a bit-vector size for ~x0" (acons #\0 expr nil))))))
;;     (if (quotep expr)
;;         (max 1 (integer-length (unquote expr))) ;this seems to be what we use to translate a constant
;;       ;;call a version of get-size-of-expr that is only for bit vectors?
;;       (let ((size (get-size-of-expr-aux expr nil)))
;;         (if (natp size)
;;             size
;; ;size might be nil, if this is an expr for which we introduced a cut variable (those can be non-BV exprs)
;;           (let* ((varname (pack$ 'node nodenum))
;;                  (type (lookup-eq varname var-size-alist)))
;;             (if (natp type)
;;                 type
;;               (hard-error 'get-size-of-bit-vector-expr "expected a bit-vector size for ~x0, but we got ~x1 " (acons #\0 expr (acons #\1 size nil))))))))))

;; (defun translate-arg-auto-sized (item)
;;   (if (consp item) ;quotep
;;       (translate-bv-constant (unquote item) (max 1 (integer-length (unquote item)))) ;the max causes 0 (which has an integer-length of 0 to nevertheless result in a positive size)
;;     (makevarname item)))

;; Returns a string-tree.
(defun translate-possibly-negated-nodenum (item)
  (declare (xargs :guard (possibly-negated-nodenump item)
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenump)))))
  (if (consp item) ;test for call of NOT
      (list* "(NOT("
             (makevarname (farg1 item))
             "))")
    (makevarname item)))

;returns a string-tree
;the input must have at least one element
;make tail rec with an acc?
(defun translate-disjunction-aux (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)
                  :guard-hints (("Goal" ;:use (:instance consp-of-car-when-possibly-negated-nodenumsp-weaken-cheap)
                                 :expand (POSSIBLY-NEGATED-NODENUMSP ITEMS)
                                 ;:in-theory (disable consp-of-car-when-possibly-negated-nodenumsp-weaken-cheap)
                                 ))))
  (if (endp items)
      (er hard? 'translate-disjunction-aux "No items (must be at least one)!")
    (if (endp (cdr items))
        (translate-possibly-negated-nodenum (first items))
      (cons (translate-possibly-negated-nodenum (first items))
            (cons " OR "
                  (translate-disjunction-aux (rest items)))))))

;; TODO: Handle constant disjunctions?
;returns a string-tree
(defun translate-disjunction (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)))
  (if (endp items)
      ;; the disjunction of no items is false
      (prog2$ (cw "WARNING: Empty disjunction.~%")
              "(FALSE)")
    (list* "("
           (translate-disjunction-aux items)
           ")")))

;;(flatten-string-tree (translate-disjunction '(2 3 (not 4) 5))) = "(NODE2 OR NODE3 OR (NOT(NODE4)) OR NODE5)"

(defthm string-treep-of-translate-disjunction
  (string-treep (translate-disjunction items)))
