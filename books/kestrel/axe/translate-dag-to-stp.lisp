; Creating STP queries from DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Ensures this book and all STP examples get rebuilt when the script changes:
;; (depends-on "callstp.bash")

;; This book has a trust tag due to the use of tshell (via call-axe-script).

;; TODO: Use an array instead of nodenum-type-alist everywhere?

;; TODO: Consider adding support for the shift operators (bvshl, bvshr, bvashr).

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

;The only variables appearing in the translated file should be of the forms NODE<num> or ARRAY<num>.  Even if, say, node 100 is the variable x, it is translated as the variable NODE100.  This should prevent any variable name clashes.
;FIXME could put in the real names of true input vars in comments?

;do we handle range types correctly everywhere?

;; See https://stp.readthedocs.io/en/latest/.

;; TODO: Consider doing all trimming, and perhaps even padding, using rewriting
;; in a separate pass before calling the STP translation code.

(include-book "type-inference")
;(include-book "depth-array")
(include-book "stp-counterexamples")
(include-book "call-axe-script") ; has ttags
(include-book "pure-dags")
(include-book "conjunctions-and-disjunctions") ;for possibly-negated-nodenumsp
(include-book "kestrel/bv/defs" :dir :system) ;todo: make sure this book includes the definitions of all functions it translates.
(include-book "kestrel/bv/leftrotate32" :dir :system) ; todo: split out the def
(include-book "kestrel/bv/bvequal" :dir :system)
;(include-book "kestrel/bv/getbit-def" :dir :system)
;(include-book "kestrel/bv-lists/bv-arrays" :dir :system)
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(include-book "kestrel/bv-lists/bv-array-if" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/file-io-string-trees" :dir :system)
;(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/utilities/strings" :dir :system) ; for newline-string
(include-book "kestrel/utilities/temp-dirs" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/file-io-light/write-strings-to-file-bang" :dir :system) ;; todo reduce, just used to clear a file
(include-book "kestrel/file-io-light/read-file-into-character-list" :dir :system)
;(in-theory (disable revappend-removal)) ;caused problems (though this may be a better approach to adopt someday)
(include-book "kestrel/acl2-arrays/print-array" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(local (include-book "rational-lists"))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/bv/bvdiv" :dir :system))
(local (include-book "kestrel/bv/bvmod" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system)) ;for character-listp-of-take
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(local (include-book "kestrel/utilities/read-run-time" :dir :system))

(in-theory (disable open-output-channels open-output-channel-p1)) ; drop?

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

;; (defthmd integer-listp-when-nat-listp
;;   (implies (nat-listp x)
;;            (integer-listp x))
;;   :hints (("Goal" :in-theory (enable integer-listp))))

(defthm nat-listp-forward-to-all-integerp
  (implies (nat-listp x)
           (all-integerp x))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (e/d (<-of-+-of-1-when-integers)
                       ;; Avoid printing during proofs
                       ((:e fmt-to-comment-window)
                        string-append
                        alistp nat-listp ;don't induct on these
                        consp-from-len-cheap
                        subseq
                        take
                        w
                        state-p))))

(defthm myquote-forward-to-equal-of-nth-0-and-quote
  (implies (myquotep expr)
           (equal 'quote (nth 0 expr)))
  :rule-classes :forward-chaining)

;todo: make local
(defthm natp-of-+-of--
  (implies (and (integerp x)
                (integerp y))
           (equal (natp (+ x (- y)))
                  (<= y x))))

(local
  (defthm natp-of-+-of---arg1
    (implies (and (integerp x)
                  (integerp y))
             (equal (natp (+ (- x) y))
                    (<= x y)))))

;move
(in-theory (disable (:e nat-to-string))) ;to avoid errors being printed in proofs -- huh?

;; Helps justify the correctness of the translation
(defthm equality-of-zero-length-arrays
  (implies (and (bv-arrayp width1 0 x)
                (bv-arrayp width2 0 y))
           (equal x y))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund maybe-shorten-filename (base-filename)
  (declare (xargs :guard (stringp base-filename)))
  (if (< 200 (length base-filename)) ;; todo: could increase the 200
      ;;shorten the filename if it would be too long:
      (string-append (subseq base-filename 0 199) "SHORTENED")
    base-filename))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;just use repeat?
;optimize?
(defund n-close-parens (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      acc
    (n-close-parens (+ -1 n) (cons ")" acc))))

(local
  (defthm string-treep-of-n-close-parens
    (implies (string-treep acc)
             (string-treep (n-close-parens n acc)))
    :hints (("Goal" :in-theory (enable n-close-parens)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
(defund make-node-var (n)
  (declare (type (integer 0 *) n))
  ;; would it be cheaper to use a version of nat-to-string that returns a string-tree?
  (cons "NODE" (nat-to-string n)))

;; can't be local
(defthm string-treep-of-make-node-var
  (string-treep (make-node-var n))
  :hints (("Goal" :in-theory (enable make-node-var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
;; DARG must be a nodenum or 't or 'nil.
(defund translate-boolean-arg (darg dag-array-name dag-array cut-nodenum-type-alist)
  (declare (xargs :guard (and (dargp darg)
                              (boolean-arg-okp darg) ; todo: this excludes the ER call below -- drop one?
                              (if (consp darg)       ; test for quotep
                                  t
                                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 darg)))
                              (nodenum-type-alistp cut-nodenum-type-alist))))
  (if (consp darg) ;checks for quotep
      (if (equal darg *nil*)
          "FALSE"
        (if (equal darg *t*)
            "TRUE"
          ;;i suppose any constant other than nil could be translated like t (but print a warning?!):
          (er hard? 'translate-boolean-arg "Bad constant (should be boolean): ~x0.~%" darg)))
    ;; arg is a nodenum, so check the type:
    (let ((maybe-type (maybe-get-type-of-nodenum darg dag-array-name dag-array cut-nodenum-type-alist)))
      (if (boolean-typep maybe-type)
          (make-node-var darg)
        (er hard? 'translate-boolean-arg "bad type, ~x0, for boolean argument ~x1, with expression ~x2" maybe-type darg (aref1 dag-array-name dag-array darg))))))

(local
  (defthm string-treep-of-translate-boolean-arg
    (string-treep (translate-boolean-arg darg dag-array-name dag-array cut-nodenum-type-alist))
    :hints (("Goal" :in-theory (enable translate-boolean-arg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree (actually a list of strings).
;make tail rec?
;make a table for a few common values?  process the bits in bigger chunks?
(defund translate-bv-constant-aux (val topbit)
  (declare (xargs :guard (and (integerp val) ; require natp?
                              (integerp topbit)
                              (<= -1 topbit))
                  :measure (if (natp topbit) (+ 1 topbit) 0)
                  :split-types t)
           (type integer val))
  (if (not (natp topbit))
      nil
    (cons (if (logbitp topbit val) ;(eql 1 (getbit topbit n))
              "1"
            "0")
          (translate-bv-constant-aux val (+ -1 topbit)))))

(local
  (defthm string-treep-of-translate-bv-constant-aux
    (string-treep (translate-bv-constant-aux val topbit))
    :hints (("Goal" :in-theory (enable translate-bv-constant-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
;; todo: swap the args?
(defund translate-bv-constant (val size)
  (declare (xargs :guard (and (integerp val)
                              (posp size))
                  :split-types t)
           (type integer val)
           (type (integer 1 *) size))
  (cons "0bin" (translate-bv-constant-aux val (+ -1 size))))

;; non-local because add-assert-if-a-mult calls translate-bv-constant
(defthm string-treep-of-translate-bv-constant
  (string-treep (translate-bv-constant val size))
  :hints (("Goal" :in-theory (enable translate-bv-constant))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;the 0's go into the high bits
;returns a string-tree
(defund pad-with-zeros (numzeros bv-string-tree)
  (declare (xargs :guard (and (natp numzeros)
                              (string-treep bv-string-tree))))
  (if (zp numzeros) ; todo: make a version that skips this check, when we know if fails
      bv-string-tree
    (list* "("
           (translate-bv-constant 0 numzeros) ;bozo don't need to recompute each time...
           "@"
           bv-string-tree
           ")")))

(local
  (defthm string-treep-of-pad-with-zeros
    (implies (string-treep bv-string-tree)
             (string-treep (pad-with-zeros numzeros bv-string-tree)))
    :hints (("Goal" :in-theory (enable pad-with-zeros)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
;; The parens may not always be needed, but we include them to be safe.
(defund translate-bvchop (desired-size bv-string-tree)
  (declare (xargs :guard (and (posp desired-size)
                              (string-treep bv-string-tree))))
  (list* "(" bv-string-tree "["
         (nat-to-string (+ -1 desired-size))
         ":0])"))

(local
  (defthm string-treep-of-translate-bvchop
    (implies (string-treep bv-string-tree)
             (string-treep (translate-bvchop desired-size bv-string-tree)))
    :hints (("Goal" :in-theory (enable translate-bvchop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund chop-or-pad-bv (bv-string-tree actual-size desired-size)
  (declare (xargs :guard (and (string-treep bv-string-tree)
                              (posp actual-size)
                              (posp desired-size))))
  (if (< actual-size desired-size)
      (pad-with-zeros (- desired-size actual-size) bv-string-tree)
    (if (> actual-size desired-size)
        (translate-bvchop desired-size bv-string-tree)
      bv-string-tree ;; already the right size
      )))

(local
  (defthm string-treep-of-chop-or-pad-bv
    (implies (string-treep bv-string-tree)
             (string-treep (chop-or-pad-bv bv-string-tree actual-size desired-size)))
    :hints (("Goal" :in-theory (enable chop-or-pad-bv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Here the actual size of the nodenum is known
;; Returns a string-tree
(defund translate-bv-nodenum-and-pad (nodenum desired-size actual-size)
  (declare (xargs :guard (and (natp nodenum)
                              (natp desired-size) ; todo: disallow 0?
                              (natp actual-size))
                  :split-types t)
           (type (integer 0 *) desired-size actual-size))
  (let ((varname (make-node-var nodenum)))
    ;;we need to pad with zeros if the node isn't wide enough:
    (if (< actual-size desired-size)
        (pad-with-zeros (- desired-size actual-size) varname)
      varname)))

(local
  (defthm string-treep-of-translate-bv-nodenum-and-pad
    (string-treep (translate-bv-nodenum-and-pad nodenum desired-size actual-size))
    :hints (("Goal" :in-theory (enable translate-bv-nodenum-and-pad)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Here the actual size of the arg is known (rare).
;BOZO throw an error if the arg is too big for the size (or chop it down?)
;returns a string-tree.
(defund translate-bv-arg-and-pad-width-known (arg desired-size actual-size)
  (declare (xargs :guard (and (dargp arg)
                              (bv-arg-okp arg)
                              (posp desired-size)
                              (natp actual-size))
                  :split-types t)
           (type (integer 1 *) desired-size)
           (type (integer 0 *) actual-size))
  (if (consp arg) ;tests for quotep
      (translate-bv-constant (unquote arg) desired-size) ;;can we just handle this the same way as the below (just pad)?
    ;;Otherwise, arg is a nodenum:
    (translate-bv-nodenum-and-pad arg desired-size actual-size)))

(local
  (defthm string-treep-of-translate-bv-arg-and-pad-width-known
    (string-treep (translate-bv-arg-and-pad-width-known arg desired-size actual-size))
    :hints (("Goal" :in-theory (enable translate-bv-arg-and-pad-width-known)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Translates the arg, with padding (but not chopping) as needed to make it have size DESIRED-SIZE.
;; Returns a string-tree.
;Looks up the size of the arg and pads as appropriate
;ffffixme change this to chop and skip all the chops in the callers!
;ARG is either a quotep or a nodenum in the DAG-ARRAY
;FIXME throw an error if the arg is too big for the size (or chop it down? i guess this already in effect chops down constants - is that always sound?)
(defund translate-bv-arg (arg desired-size dag-array-name dag-array dag-len cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than arg dag-len)
                              (bv-arg-okp arg)
                              (posp desired-size)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :split-types t)
           (type (integer 1 *) desired-size)
           (ignore dag-len) ; only needed for the guard
           )
  (if (consp arg) ;tests for quotep
      (translate-bv-constant (unquote arg) desired-size)
    ;;arg is a nodenum:
    (let ((maybe-type (maybe-get-type-of-nodenum arg dag-array-name dag-array cut-nodenum-type-alist)))
      (if (bv-typep maybe-type)
          (translate-bv-nodenum-and-pad arg desired-size (bv-type-width maybe-type))
        (er hard? 'translate-bv-arg "bad type, ~x0, for BV argument ~x1, with expression ~x2" maybe-type arg (aref1 dag-array-name dag-array arg))))))

(local
  (defthm string-treep-of-translate-bv-arg
    (string-treep (translate-bv-arg arg desired-size dag-array-name dag-array dag-len cut-nodenum-type-alist))
    :hints (("Goal" :in-theory (enable translate-bv-arg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Translates DARG, with padding or chopping as needed to make it have size DESIRED-SIZE.
;; Returns a string-tree.
;; TODO: Justify the chopping for all operators whose translation uses this.
;; todo: use this more
(defund translate-bv-arg2 (darg desired-size dag-array-name dag-array dag-len cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than darg dag-len)
                              (bv-arg-okp darg)
                              (posp desired-size)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :split-types t)
           (type (integer 1 *) desired-size)
           (ignore dag-len) ; only needed for the guard
           )
  (if (consp darg)                                        ;tests for quotep
      (translate-bv-constant (unquote darg) desired-size) ; puts in exactly DESIRED-SIZE bits of the constant
    ;; darg is a nodenum:
    (let ((maybe-type (maybe-get-type-of-nodenum darg dag-array-name dag-array cut-nodenum-type-alist)))
      (if (not (bv-typep maybe-type))
          (er hard? 'translate-bv-arg2 "bad type, ~x0, for BV argument ~x1, with expression ~x2" maybe-type darg (aref1 dag-array-name dag-array darg))
        (if (= 0 (bv-type-width maybe-type))
            (er hard? 'translate-bv-arg2 "BV of size 0 found: ~x0." darg)
          (let ((translated-nodenum (make-node-var darg)))
            (chop-or-pad-bv translated-nodenum (bv-type-width maybe-type) desired-size)))))))

(local
  (defthm string-treep-of-translate-bv-arg2
    (string-treep (translate-bv-arg2 darg desired-size dag-array-name dag-array dag-len cut-nodenum-type-alist))
    :hints (("Goal" :in-theory (enable translate-bv-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
;; At most one of LHS-PAD-BITS and RHS-PAD-BITS is non-zero.
;; See also translate-equality-of-bvs-to-stp-aux.
(defund translate-array-element-equality (lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width elem-num)
  (declare (xargs :guard (and (string-treep lhs-string-tree)
                              (string-treep rhs-string-tree)
                              (natp lhs-pad-bits)
                              (natp rhs-pad-bits)
                              (posp index-width)
                              (integerp elem-num))))
  (let ((index (translate-bv-constant elem-num index-width))) ; todo: use base 10?
    (list* "("
           (pad-with-zeros lhs-pad-bits (list* lhs-string-tree "[" index "]"))
           " = "
           (pad-with-zeros rhs-pad-bits (list* rhs-string-tree "[" index "]"))
           ")")))

(local
 (defthm string-treep-of-translate-array-element-equality
   (implies (and (string-treep lhs-string-tree)
                 (string-treep rhs-string-tree))
            (string-treep (translate-array-element-equality lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width elem-num)))
   :hints (("Goal" :in-theory (enable translate-array-element-equality)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;makes an assertion for each possible index
;; Returns a string-tree.
;; At most one of LHS-PAD-BITS and RHS-PAD-BITS is non-zero.
(defund translate-array-equality (n ;the element number
                                  lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width
                                  acc ;a list of strings, initially containing a single close paren
                                  )
  (declare (xargs :guard (and (natp n)
                              (string-treep lhs-string-tree)
                              (string-treep rhs-string-tree)
                              (natp lhs-pad-bits)
                              (natp rhs-pad-bits)
                              (posp index-width))
                  :split-types t)
           (type (integer 0 *) n lhs-pad-bits rhs-pad-bits))
  (if (zp n)
      ;;for element zero we don't generate an AND
      (list* "(" ;matches the close paren passed in in ACC
             (newline-string)
             (translate-array-element-equality lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width n)
             acc)
    (translate-array-equality (+ -1 n) lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width
                              (list* (newline-string)
                                     "AND "
                                     (translate-array-element-equality lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width n)
                                     acc))))

(local
 (defthm string-treep-of-translate-array-equality
   (implies (and (string-treep acc)
                 (string-treep lhs-string-tree)
                 (string-treep rhs-string-tree))
            (string-treep (translate-array-equality n lhs-string-tree rhs-string-tree lhs-pad-bits rhs-pad-bits index-width acc)))
   :hints (("Goal" :in-theory (enable translate-array-equality)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;recognizes a true list of items of the form (array-elems array-name element-width)
; todo require that the data elements are no wider than the width?
(defund constant-array-infop (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((entry (first x)))
      (and (= 3 (len entry))
           (let ((data (first entry))
                 (name (second entry)) ; "name" which we can use to refer to the array
                 (element-width (third entry)))
             (and (nat-listp data)
                  (<= 2 (len data)) ; an array of length 1 would have 0 index bits
                  (string-treep name)
                  (posp element-width) ; element-width (disallows 0)
                  ))
           (constant-array-infop (rest x))))))

(defthm constant-array-infop-of-cdr
  (implies (constant-array-infop constant-array-info)
           (constant-array-infop (cdr constant-array-info)))
  :hints (("Goal" :in-theory (enable constant-array-infop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns a string-tree representing the array, or nil if no match
(defund get-array-constant-name (data element-width constant-array-info)
  (declare (xargs :guard (and (nat-listp data)
                              (posp element-width)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (enable constant-array-infop)))))
  (if (endp constant-array-info)
      nil
    (let ((entry (first constant-array-info)))
      (if (and (equal data (first entry))
               (= element-width (third entry)))
          (second entry) ; return the name
        ;; keep looking:
        (get-array-constant-name data element-width (rest constant-array-info))))))

(local
  (defthm string-treep-of-get-array-constant-name
    (implies (constant-array-infop constant-array-info)
             (string-treep (get-array-constant-name data element-width constant-array-info)))
    :hints (("Goal" :in-theory (enable get-array-constant-name constant-array-infop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;makes sure that if the same array constant (used with the same width) appears twice we only make one var for it..
;fixme think about two arrays with the same values but different element widths!
;; Returns (mv array-name constant-array-info) where array-name is a string and constant-array-info may have been extended.
(defund translate-constant-array-mention (data element-width constant-array-info)
  (declare (xargs :guard (and (nat-listp data)
                              (<= 2 (len data)) ; arrays of length 1 would have 0 index bits
                              (posp element-width)
                              (constant-array-infop constant-array-info))))
  (let* ((match (get-array-constant-name data element-width constant-array-info)))
    (if match
        (mv match constant-array-info)
      ;; no match:
      (let* ((array-number (len constant-array-info)) ;fixme do something better?
             (array-name (cons "ARRAY" (nat-to-string array-number))))
        (mv array-name
            (cons (list data array-name element-width)
                  constant-array-info))))))

(local
  (defthm stringp-of-mv-nth-0-of-translate-constant-array-mention
    (implies (constant-array-infop constant-array-info)
             (string-treep (mv-nth 0 (translate-constant-array-mention data element-width constant-array-info))))
    :hints (("Goal" :in-theory (enable translate-constant-array-mention constant-array-infop)))))

(local
  (defthm constant-array-infop-of-mv-nth-1-of-translate-constant-array-mention
    (implies (and (constant-array-infop constant-array-info)
                  (nat-listp data)
                  (<= 2 (len data))
                  (posp element-width))
             (constant-array-infop (mv-nth 1 (translate-constant-array-mention data element-width constant-array-info))))
    :hints (("Goal" :in-theory (enable translate-constant-array-mention constant-array-infop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Should work for EQUAL (once we choose a size) and BVEQUAL.
;; Returns a string-tree.
(defund translate-equality-of-bvs-to-stp-aux (width lhs rhs lhs-width rhs-width)
  (declare (xargs :guard (and (posp width)
                              (dargp lhs)
                              (bv-arg-okp lhs)
                              (dargp rhs)
                              (bv-arg-okp rhs)
                              (posp lhs-width)
                              (posp rhs-width))))

  (list* "("
         (translate-bv-arg-and-pad-width-known lhs width lhs-width)
         " = "
         (translate-bv-arg-and-pad-width-known rhs width rhs-width)
         ")"))

(local
  (defthm string-treep-of-translate-equality-of-bvs-to-stp-aux
    (string-treep (translate-equality-of-bvs-to-stp-aux width lhs rhs lhs-width rhs-width))
    :hints (("Goal" :in-theory (enable translate-equality-of-bvs-to-stp-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp translated-equality) where TRANSLATED-EQUALITY is a
;; string-tree but is meaningless if ERP is non-nil.
(defund translate-equality-of-bvs-to-stp (lhs rhs lhs-type rhs-type)
  (declare (xargs :guard (and (dargp lhs)
                              (dargp rhs)
                              (bv-typep lhs-type)
                              (bv-typep rhs-type))))
  (let* ((lhs-width (bv-type-width lhs-type))
         (rhs-width (bv-type-width rhs-type)))
    (if (or (zp lhs-width)
            (zp rhs-width))
        (prog2$ (er hard? 'translate-equality-of-bvs-to-stp "Bit vectors of width 0 are not supported.")
                (mv :bv-of-width-0 nil))
      (let ((max-width (max lhs-width rhs-width)))
        (if (and (bv-arg-okp lhs) ;; can these tests fail?
                 (bv-arg-okp rhs))
            (mv (erp-nil)
                (translate-equality-of-bvs-to-stp-aux max-width lhs rhs lhs-width rhs-width))
          (prog2$ (er hard? 'translate-equality-of-bvs-to-stp "A bad BV arg was found.")
                  (mv :bad-bv-arg nil)))))))

(local
  (defthm string-treep-of-mv-nth-1-of-translate-equality-of-bvs-to-stp
    (string-treep (mv-nth 1 (translate-equality-of-bvs-to-stp lhs rhs lhs-type rhs-type)))
    :hints (("Goal" :in-theory (enable translate-equality-of-bvs-to-stp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns (mv translated-expr constant-array-info) where translated-expr is a string-tree.
;fixme what if we can't translate the equality (maybe it mentions ':byte)?
;; TODO: Add ability to return errors.
(defund translate-equality-to-stp (lhs ;a nodenum or quoted constant
                                   rhs ;a nodenum or quoted constant
                                   dag-array-name dag-array dag-len
                                   cut-nodenum-type-alist constant-array-info)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (or (myquotep lhs)
                                  (and (natp lhs)
                                       (< lhs dag-len)))
                              (or (myquotep rhs)
                                  (and (natp rhs)
                                       (< rhs dag-len)))
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (symbolp dag-array-name)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (disable natp)
                                 :do-not '(generalize eliminate-destructors))))
           (ignore dag-len) ; only used in the guard
           )
  (let* ((lhs-type (get-type-of-arg-checked lhs dag-array-name dag-array cut-nodenum-type-alist))
         (rhs-type (get-type-of-arg-checked rhs dag-array-name dag-array cut-nodenum-type-alist)))
    (if (and (bv-array-typep lhs-type)
             (bv-array-typep rhs-type)
             ;;the lengths must be the same (fixme if not, could translate the equality as false?? and print a warning!)
             (equal (bv-array-type-len lhs-type) (bv-array-type-len rhs-type)))
        ;; Equality of two array terms of the same length:
        (let* ((lhs-element-width (bv-array-type-element-width lhs-type))
               (rhs-element-width (bv-array-type-element-width rhs-type))
               (common-len (bv-array-type-len lhs-type)) ;same as the len from rhs-type
               )
          (if (eql 0 common-len) ;; any two arrays of length 0 are equal (see theorem above)
              (mv (list "(TRUE)") ;todo: add a test of this case
                  constant-array-info)
            (if (eql 1 common-len)
                ;; because such arrays would have 0 bits of index:
                (mv (er hard? 'translate-equality-to-stp "Arrays of length 1 are not supported.")
                    constant-array-info)
              (if (or (zp lhs-element-width)
                      (zp rhs-element-width))
                  (mv (er hard? 'translate-equality-to-stp "Arrays whose elements have 0 width are not supported.")
                      constant-array-info)
                ;; translate the LHS (without padding yet):
                (mv-let (erp1 lhs-string-tree constant-array-info)
                  (if (atom lhs) ;checks for nodenum
                      (mv nil (make-node-var lhs) constant-array-info)
                    ;;lhs is a constant array:
                    (if (and (nat-listp (unquote lhs)) ;these checks may be implied by the type tests above
                             )
                        (mv-let (lhs-string-tree constant-array-info)
                          (translate-constant-array-mention (unquote lhs) lhs-element-width constant-array-info)
                          (mv nil lhs-string-tree constant-array-info))
                      (prog2$ (er hard? 'translate-equality-to-stp "Bad array constant: ~x0." lhs)
                              (mv t nil constant-array-info))))
                  ;; translate the RHS (without padding yet):
                  (mv-let (erp2 rhs-string-tree constant-array-info)
                    (if (atom rhs) ;checks for nodenum
                        (mv nil (make-node-var rhs) constant-array-info)
                      ;;rhs is a constant array:
                      (if (and (nat-listp (unquote rhs)) ;these checks may be implied by the type tests above
                               )
                          (mv-let (rhs-string-tree constant-array-info)
                            (translate-constant-array-mention (unquote rhs) rhs-element-width constant-array-info)
                            (mv nil rhs-string-tree constant-array-info))
                        (prog2$ (er hard? 'translate-equality-to-stp "Bad array constant: ~x0." rhs)
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
                         (translate-array-equality (+ -1 common-len)
                                                   lhs-string-tree
                                                   rhs-string-tree
                                                   lhs-pad-bits
                                                   rhs-pad-bits
                                                   (ceiling-of-lg common-len) ;; index-width; above we check for len=1
                                                   (list ")") ;acc; tod: drop the LIST here since this is a string-tree?
                                                   )
                         constant-array-info)))))))))
      (if (and (boolean-typep lhs-type)
               (boolean-typep rhs-type))
          ;; Equality of two booleans:
          (if (and (boolean-arg-okp lhs)
                   (boolean-arg-okp rhs))
              (mv
               (list* "("
                      (translate-boolean-arg lhs dag-array-name dag-array cut-nodenum-type-alist)
                      " <=> "
                      (translate-boolean-arg rhs dag-array-name dag-array cut-nodenum-type-alist)
                      ")")
               constant-array-info)
            ;;todo: pass back errors?
            (mv (er hard? 'translate-equality-to-stp "A bad boolean arg was found.")
                constant-array-info))
        (if (and (bv-typep lhs-type)
                 (bv-typep rhs-type))
            ;; Equality of two bit-vectors:
            (b* (((mv erp translated-equality)
                  (translate-equality-of-bvs-to-stp lhs rhs lhs-type rhs-type))
                 ((when erp)
                  (er hard? 'translate-equality-to-stp "Error translating equality of BVs.")
                  ;; meaningless:
                  (mv nil constant-array-info)))
              (mv translated-equality constant-array-info))
          (prog2$ (print-array dag-array-name dag-array (max (if (natp lhs) (+ 1 lhs) 0) (if (natp rhs) (+ 1 rhs) 0)))
                  ;;fixme print the assumptions? or the literals? or cut-nodenum-type-alist ?
                  ;;fixme be more flexible.  btw, nil is considered to be of type boolean, but what if it's being compared to a list of 0 size?
                  ;;fixme if the types are guaranteed to have disjoint value sets, we could just generate FALSE here, but watch out for things like nil (both a boolean and the empty list?)
                  (mv (er hard? 'translate-equality-to-stp "Trying to equate things of different types (see above for dag): ~x0 (type: ~x1) and ~x2 (type: ~x3).~%"
                          lhs lhs-type rhs rhs-type)
                      constant-array-info)))))))

(local
  (defthm string-treep-of-mv-nth-0-of-translate-equality-to-stp
    (implies (constant-array-infop constant-array-info)
             (string-treep (mv-nth 0 (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist constant-array-info))))
    :hints (("Goal" :in-theory (e/d (translate-equality-to-stp) (;list-typep bv-array-typep bv-array-type-len bv-array-type-element-width
                                                                 ))))))

(local
  (defthm constant-array-infop-of-mv-nth-1-of-translate-equality-to-stp
    (implies (constant-array-infop constant-array-info)
             (constant-array-infop (mv-nth 1 (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist constant-array-info))))
    :hints (("Goal" :in-theory (enable translate-equality-to-stp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv array-name constant-array-info actual-element-width) where ARRAY-NAME is a string-tree that can be used to refer to the array
(defund translate-bv-array-arg (arg
                                desired-element-width
                                desired-array-length
                                dag-array-name dag-array dag-len
                                cut-nodenum-type-alist
                                calling-fn ;the function for which ARG is an argument (used for error reporting) ; todo: pass the caller's nodenum?
                                widths-must-matchp
                                constant-array-info)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than arg dag-len)
                              (posp desired-element-width)
                              (integerp desired-array-length)
                              (<= 2 desired-array-length)
                              (bv-array-arg-okp desired-array-length arg)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (symbolp calling-fn)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (enable bv-array-arg-okp))))
           (ignore dag-len) ; only needed for the guard
           )
  (if (consp arg) ; check for constant (fixme: what if arg is a nodenum of a constant?)
      ;; since we have a guard of bv-array-arg-okp, we know the constant is a nat-list of the correct length:
      ;; (constant array elements that are too narrow are okay, elements that are too wide get chopped)
      (b* (;(arg-type (get-type-of-arg-checked arg dag-array-name dag-array cut-nodenum-type-alist)) ; todo: drop?
           ;;(arg-len (bv-array-type-len arg-type))
           ;(arg-element-width (bv-array-type-element-width arg-type))
           ;;We handle constant arrays by putting in a fresh variable and adding asserts about the values of each element
           ;; If possible, we reuse the name of an existing constant array with the same data, length, and width.
           ;;fixme what if the data is of the wrong form?
           ((mv array-name constant-array-info)
            (translate-constant-array-mention (unquote arg) desired-element-width constant-array-info)))
        (mv array-name constant-array-info desired-element-width))
    ;; arg is a nodenum:
    (b* ((arg-type (get-type-of-arg-checked arg dag-array-name dag-array cut-nodenum-type-alist))
         ((when (not (bv-array-typep arg-type)))
          ;; (- (cw "DAG for error:~%"))
          ;; (print-dag-array-all arg dag-array-name dag-array) ; todo: would be good to print the caller too
          (er hard? 'translate-bv-array-arg "Tried to translate an argument, ~x0, of ~x1 that is not known to be an array." arg calling-fn)
          (mv nil constant-array-info 0))
         (arg-len (bv-array-type-len arg-type))
         (arg-element-width (bv-array-type-element-width arg-type))
         ((when (not (eql desired-array-length arg-len)))
          (er hard? 'translate-bv-array-arg "Tried to translate an array argument to ~x0 with desired length ~x1 but actual length ~x2.~%" calling-fn desired-array-length arg-len)
          (mv nil constant-array-info 0))
         ((when (and widths-must-matchp ; for a read, arg might legitimately be the nodenum of a narrower (or wider) array constant or var (todo: what about such args to bv-array-write and bv-array-if?)
                     (not (eql desired-element-width arg-element-width))))
          (er hard? 'translate-bv-array-arg "Tried to translate an array argument to ~x0 with desired element width ~x1 but actual element width ~x2.~%" calling-fn desired-element-width arg-element-width)
          (mv nil constant-array-info 0)))
      (mv (make-node-var arg) constant-array-info arg-element-width))))

(local
  (defthm string-treep-of-mv-nth-0-of-translate-bv-array-arg
    (implies (constant-array-infop constant-array-info)
             (string-treep (mv-nth 0 (translate-bv-array-arg arg desired-element-width desired-array-length dag-array-name dag-array dag-len cut-nodenum-type-alist calling-fn widths-must-matchp constant-array-info))))
    :hints (("Goal" :in-theory (enable translate-bv-array-arg constant-array-infop)))))

(local
  (defthm constant-array-infop-of-mv-nth-1-of-translate-bv-array-arg
    (implies (and ;(nat-listp (cadr arg))
               (posp desired-element-width)
               (integerp desired-array-length)
               (<= 2 desired-array-length)
               (constant-array-infop constant-array-info)
               (bv-array-arg-okp desired-array-length arg)
               )
             (constant-array-infop (mv-nth 1 (translate-bv-array-arg arg desired-element-width desired-array-length dag-array-name dag-array dag-len cut-nodenum-type-alist calling-fn widths-must-matchp constant-array-info))))
    :hints (("Goal" :in-theory (enable translate-bv-array-arg bv-array-arg-okp)))))

(local
  (defthm integerp-of-mv-nth-2-of-translate-bv-array-arg
    (implies (posp desired-element-width)
             (integerp (mv-nth 2 (translate-bv-array-arg arg desired-element-width desired-array-length dag-array-name dag-array dag-len cut-nodenum-type-alist calling-fn widths-must-matchp constant-array-info))))
    :hints (("Goal" :in-theory (enable translate-bv-array-arg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorems justifying the translation:
(thm (equal (bvdiv size x 0) 0))
(thm (equal (bvmod size x 0) (bvchop size x)))
(thm (implies (natp amt) (equal (leftrotate32 amt x) (leftrotate32 (mod amt 32) x))))
;; Special case of leftrotate32 with 0 shift amount: We handle it like bvchop
(thm (equal (leftrotate32 0 x) (bvchop 32 x)))

;; Returns (mv translated-expr-string constant-array-info).
;; (defun translate-dag-expr-bvplus (args dag-array-name dag-array constant-array-info cut-nodenum-type-alist)
;;   (declare (xargs :guard (and (array1p dag-array-name dag-array) ;;TODO: Instead, use pseudo-dag-arrayp.
;;                               (bounded-darg-listp args (alen1 dag-array-name dag-array))
;;                               (nodenum-type-alistp cut-nodenum-type-alist)
;;                               (symbolp dag-array-name)
;;                               (equal 3 (len args))
;;                               (darg-quoted-posp (first args))
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

;; Returns (mv translated-expr constant-array-info) where translated-expr is a string-tree.
;FFIXME think hard about sizes and chops..
;todo: add support for leftrotate (not just leftrotate32). width may need to be a power of 2
;fixme the calls to safe-unquote below can cause crashes??
;thread through an accumulator?
;should this take a desired size (or type?) for the expr?
;should we separate out the handling of terms from formulas
;TODO: Pull out the constant case?
;; dag-len is only used in guards (including the guard of translate-bv-arg).
;todo: see repeated calls below to translate-bv-arg on same value...
;; We do not handle MYIF or IF, only BOOLIF, BVIF, and BV-ARRAY-IF.
;; TODO: Consider supporting BOOL-TO-BIT and BIT-TO-BOOL.
(defund translate-dag-expr (expr ;either a quotep or a function call over nodenums and quoteps (never a variable)
                            dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-dag-exprp dag-len expr)
                              (consp expr) ; we never translate variables
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (constant-array-infop constant-array-info))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0 dag-exprp natp-of-+-of-1 rationalp-when-integerp)
                                                        (myquotep natp quotep))))))
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
        ;; boolean operators (we could perhaps support BOOLXOR (or just XOR) as well):
        (not
          (if (and (= 1 (len (dargs expr)))
                   (boolean-arg-okp (darg1 expr)))
              (mv (erp-nil)
                  (list* "(NOT(" (translate-boolean-arg (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist) "))")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (booland
         (if (and (= 2 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "("
                        (translate-boolean-arg (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist)
                        " AND "
                        (translate-boolean-arg (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)
                        ")")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (boolor
         (if (and (= 2 (len (dargs expr)))
                  (boolean-arg-okp (darg1 expr))
                  (boolean-arg-okp (darg2 expr)))
             (mv (erp-nil)
                 (list* "("
                        (translate-boolean-arg (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist)
                        " OR "
                        (translate-boolean-arg (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)
                        ")")
                 constant-array-info)
           (mv (erp-t) nil constant-array-info)))
        (boolif
          (if (and (= 3 (len (dargs expr)))
                   (boolean-arg-okp (darg1 expr))
                   (boolean-arg-okp (darg2 expr))
                   (boolean-arg-okp (darg3 expr)))
              (mv (erp-nil)
                  (list* "(IF "
                         (translate-boolean-arg (darg1 expr) dag-array-name dag-array cut-nodenum-type-alist)
                         " THEN "
                         (translate-boolean-arg (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)
                         " ELSE "
                         (translate-boolean-arg (darg3 expr) dag-array-name dag-array cut-nodenum-type-alist)
                         " ENDIF)")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        ;; bit operators
        (bitnot ;; (bitnot x)
          (if (and (= 1 (len (dargs expr)))
                   (bv-arg-okp (darg1 expr)))
              (mv (erp-nil)
                  (list* "(~"
                         (translate-bv-arg2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         ")")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (bitand ;; (bitand x y)
          (if (and (= 2 (len (dargs expr)))
                   (bv-arg-okp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (mv (erp-nil)
                  (list* "("
                         (translate-bv-arg2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         " & "
                         (translate-bv-arg2 (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         ")")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (bitor ;; (bitor x y)
          (if (and (= 2 (len (dargs expr)))
                   (bv-arg-okp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (mv (erp-nil)
                  (list* "("
                         (translate-bv-arg2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         " | "
                         (translate-bv-arg2 (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         ")")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (bitxor ;; (bitxor x y)
          (if (and (= 2 (len (dargs expr)))
                   (bv-arg-okp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (mv (erp-nil)
                  (list* "(BVXOR("
                         (translate-bv-arg2 (darg1 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         ","
                         (translate-bv-arg2 (darg2 expr) 1 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         "))")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        ;; bv operators:
        (bvchop ;; (bvchop size x)
          (if (and (= 2 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (let ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "("
                           (translate-bv-arg (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "["
                           (nat-to-string (+ -1 width))
                           ":0])")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvnot ;; (bvnot size x)
          (if (and (= 2 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (let ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(~"
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ") ")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvuminus ;; (bvuminus size x)
          (if (and (= 2 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVUMINUS("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (getbit ;; (getbit n x)
          (if (and (= 2 (len (dargs expr)))
                   (darg-quoted-natp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (mv (erp-nil)
                  (let* ((bitnum (unquote (darg1 expr)))
                         (bitnum-string (nat-to-string bitnum)))
                    (list* "("
                           (translate-bv-arg (darg2 expr) (+ 1 bitnum) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "["
                           bitnum-string
                           ":"
                           bitnum-string
                           "])"))
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (slice ;; (slice high low x)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-natp (darg1 expr))
                   (darg-quoted-natp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let ((high (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "("
                           (translate-bv-arg (darg3 expr) (+ 1 high) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "["
                           (nat-to-string high)
                           ":"
                           (nat-to-string (unquote (darg2 expr)))
                           "])")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvequal ; (bvequal size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           " = "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ")")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvand ;; (bvand size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr))
                   )
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           " & "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ")")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvor ;; (bvor size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           " | "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ")")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvxor ;; (bvxor size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVXOR("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvplus ;; (bvplus size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVPLUS("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvminus ;; (bvminus size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVSUB("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvmult ;; (bvmult size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVMULT("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvdiv ;; (bvdiv size x y)
          ;; note the special case for 0 divisor
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(IF (" ;if the third arg is 0, then the bvdiv is 0 (see thm above)
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "="
                           (translate-bv-constant 0 width)
                           ") THEN ("
                           (translate-bv-constant 0 width) ; todo: done just above
                           ") ELSE "
                           "(BVDIV("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist) ; todo: done just above
                           ")) ENDIF)")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvmod ;; (bvmod size x y)
          ;; note the special case for 0 divisor
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(IF (" ;if the third arg is 0, then the bvmod is bvchop of its second argument (see thm above)
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "="
                           (translate-bv-constant 0 width)
                           ") THEN ("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ") ELSE (BVMOD("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist) ; todo: done just above
                           ")) ENDIF)")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (sbvdiv ;; (sbvdiv size x y)
          ;; note the special case for 0 divisor
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(IF (" ;if the third arg is 0, then the sbvdiv is 0
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "="
                           (translate-bv-constant 0 width)
                           ") THEN ("
                           (translate-bv-constant 0 width)
                           ") ELSE "
                           "(SBVDIV("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ")) ENDIF)")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (sbvrem ;; (sbvrem size x y)
          ;; note the special case for 0 divisor
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(IF (" ;if the third arg is 0, then the sbvrem is bvchop of its second argument
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "="
                           (translate-bv-constant 0 width)
                           ") THEN ("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ") ELSE (SBVMOD("
                           (nat-to-string width)
                           ","
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ","
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ")) ENDIF)")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvlt ;; (bvlt size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVLT("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ", "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvle ;; (bvle size x y)
          ;; TODO: Consider omitting this and instead introducing bvlt through rewriting
          ;; Or add support for the other operators: (bvgt, bvge).
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(BVLE("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ", "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (sbvlt ;; (sbvlt size x y)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(SBVLT("
                           ;;fixme could add the brackets to translate-bv-arg?
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ", "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (sbvle ;; (sbvle size x y)
          ;; TODO: Consider omitting this and instead introducing sbvlt through rewriting
          ;; Or add support for the other operators: (sbvgt, sbvge).
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr)))
              (let* ((width (unquote (darg1 expr))))
                (mv (erp-nil)
                    (list* "(SBVLE("
                           (translate-bv-arg2 (darg2 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           ", "
                           (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                           "))")
                    constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (bvcat ;; (bvcat highsize highval lowsize lowval)
          (if (and (= 4 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (bv-arg-okp (darg2 expr))
                   (darg-quoted-posp (darg3 expr))
                   (bv-arg-okp (darg4 expr)))
              (mv (erp-nil)
                  (list* "("
                         (translate-bv-arg2 (darg2 expr) (unquote (darg1 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         "@"
                         (translate-bv-arg2 (darg4 expr) (unquote (darg3 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         ")")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (bvsx ;; (bvsx new-size old-size val)
          (if (and (= 3 (len (dargs expr)))
                   (darg-quoted-integerp (darg1 expr))
                   (darg-quoted-posp (darg2 expr))
                   (<= (unquote (darg2 expr)) (unquote (darg1 expr)))
                   (bv-arg-okp (darg3 expr)))
              (mv (erp-nil)
                  (list*
                    "BVSX("
                    (translate-bv-arg2 (darg3 expr) (unquote (darg2 expr)) dag-array-name dag-array dag-len cut-nodenum-type-alist)
                    ","
                    (nat-to-string (unquote (darg1 expr)))
                    ")")
                  constant-array-info)
            (mv (erp-t) nil constant-array-info)))
        (bvif ;; (bvif size test thenpart elsepart)
          ;;skip the outer bracket expression (or the 2 inner ones?)
          (if (and (= 4 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (boolean-arg-okp (darg2 expr))
                   (bv-arg-okp (darg3 expr))
                   (bv-arg-okp (darg4 expr)))
              (let* ((width (unquote (darg1 expr)))
                     (top-bit-string (nat-to-string (+ -1 width))))
                (mv
                  (erp-nil)
                  (list* "(IF "
                         (translate-boolean-arg (darg2 expr) dag-array-name dag-array cut-nodenum-type-alist)
                         " THEN "
                         (translate-bv-arg2 (darg3 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         " ELSE "
                         (translate-bv-arg2 (darg4 expr) width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                         " ENDIF)[" ;todo: drop this chop?:
                         top-bit-string
                         ":0]"
                         )
                  constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (leftrotate32 ; (leftrotate32 '<rotate-amount> <val>), note that rotate-amount must be a constant
          (if (and (= 2 (len (dargs expr)))
                   (darg-quoted-natp (darg1 expr))
                   (bv-arg-okp (darg2 expr)))
              (let* ((rotate-amount (unquote (darg1 expr)))
                     (rotate-amount (mod rotate-amount 32)) ; todo: require this reduction to have already been done
                     )
                (if (= 0 rotate-amount) ;in this case, it's just like bvchop (handling 0 separately avoids an error in the main case, a slice of [31:32])
                    (mv (erp-nil)
                        (list* "(" ; todo: drop these parens?
                               (translate-bv-arg2 (darg2 expr) 32 dag-array-name dag-array dag-len cut-nodenum-type-alist)
                               ")")
                        constant-array-info)
                  ;;main case:
                  (let ((low-slice-size (- 32 rotate-amount)) ; becomes the high bits of the result
                        ;;high-slice-size is rotate-amount
                        (translated-arg (translate-bv-arg (darg2 expr) 32 dag-array-name dag-array dag-len cut-nodenum-type-alist)))
                    (mv (erp-nil)
                        (list* "("
                               translated-arg
                               "["
                               (nat-to-string (+ -1 low-slice-size))
                               ":0]@"
                               translated-arg
                               "[31:"
                               (nat-to-string low-slice-size) "])")
                        constant-array-info))))
            (mv (erp-t) nil constant-array-info)))
        (bv-array-read ; (bv-array-read <element-width> <len> <index> <data>)
          ;;fixme an error occurs if we try to translate a bv-array-read of one length applied to a bv-array-write of a longer length? better to just cut there??
          ;;also an error if we translate two bv-array-reads with different len params but the same array param
          ;;fixme handle arrays with non-constant lengths? will have to think about array lengths that are not powers of 2.  may need to translate ceiling-of-lg...
          (if (and (= 4 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr)) ; element width must not be 0
                   (darg-quoted-integerp (darg2 expr))
                   (<= 2 (unquote (darg2 expr))) ;arrays of length 1 would have 0 index bits
                   (bv-arg-okp (darg3 expr))
                   (bv-array-arg-okp (unquote (darg2 expr)) (darg4 expr)))
              (b* ((element-width (unquote (darg1 expr)))
                   (len (unquote (darg2 expr)))
                   (index (darg3 expr))
                   (array-arg (darg4 expr))
                   (num-index-bits (ceiling-of-lg len))
                   ((mv array-name constant-array-info actual-element-width)
                    (translate-bv-array-arg array-arg element-width len dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-read
                                            nil ; element width does not have to match (see array-width-test2)
                                            constant-array-info))
                   ;; given that we've checked the len, can we remove the index padding stuff below?
                   (trimmed-index ;;the index gets chopped down to NUM-INDEX-BITS bits because that's what bv-array-read does
                     (translate-bv-arg2 index num-index-bits dag-array-name dag-array dag-len cut-nodenum-type-alist)
                     )
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
                                                   (if (< element-width actual-element-width)
                                                       ;; need to chop down the value:
                                                       (list* array-access "[" (nat-to-string (+ -1 element-width)) ":0]" )
                                                     ;; no padding or chopping:
                                                     array-access))
                                                 ")")))
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
                   (darg-quoted-posp (darg1 expr))
                   (darg-quoted-integerp (darg2 expr))
                   (<= 2 (unquote (darg2 expr))) ;arrays of length 1 would have 0 index bits
                   (bv-arg-okp (darg3 expr))
                   (bv-arg-okp (darg4 expr))
                   (bv-array-arg-okp (unquote (darg2 expr)) (darg5 expr)))
              (b* ((element-width (unquote (darg1 expr)))
                   (len (unquote (darg2 expr)))
                   (index (darg3 expr))
                   (val (darg4 expr))
                   (array-arg (darg5 expr))
                   (num-index-bits (ceiling-of-lg len))
                   ((mv array-name constant-array-info &)
                    (translate-bv-array-arg array-arg element-width len dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-write t constant-array-info)))
                (let* ((trimmed-index
                         (translate-bv-arg2 index num-index-bits dag-array-name dag-array dag-len cut-nodenum-type-alist))
                       (expr-when-in-bounds
                         (list* "("
                                array-name
                                " WITH ["
                                trimmed-index ;fixme should we consider padding the index to work for arrays that are actually longer, as we do for bv-array-read?
                                "] := ("
                                ;; value:
                                (translate-bv-arg2 val element-width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                                "))"
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
        (bv-array-if ; (bv-array-if element-width length test thenpart elsepart)
          (if (and (= 5 (len (dargs expr)))
                   (darg-quoted-posp (darg1 expr))
                   (darg-quoted-integerp (darg2 expr))
                   (<= 2 (unquote (darg2 expr))) ;arrays of length 1 would have 0 index bits
                   (boolean-arg-okp (darg3 expr))
                   (bv-array-arg-okp (unquote (darg2 expr)) (darg4 expr))
                   (bv-array-arg-okp (unquote (darg2 expr)) (darg5 expr)))
              (b* ((element-width (unquote (darg1 expr)))
                   (length (unquote (darg2 expr)))
                   (test (darg3 expr))
                   (then-branch (darg4 expr))
                   (else-branch (darg5 expr))
                   ((mv then-array-name constant-array-info &)
                    (translate-bv-array-arg then-branch element-width length dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-if t constant-array-info))
                   ((mv else-array-name constant-array-info &)
                    (translate-bv-array-arg else-branch element-width length dag-array-name dag-array dag-len cut-nodenum-type-alist 'bv-array-if t constant-array-info)))
                (mv
                  (erp-nil)
                  (list* "(IF "
                         (translate-boolean-arg test dag-array-name dag-array cut-nodenum-type-alist)
                         " THEN "
                         then-array-name
                         " ELSE "
                         else-array-name
                         " ENDIF)")
                  constant-array-info))
            (mv (erp-t) nil constant-array-info)))
        (unsigned-byte-p ;(UNSIGNED-BYTE-P WIDTH X), needed for things like (unsigned-byte-p 1 (bvplus 8 x y))
         (if (and (= 2 (len (dargs expr)))
                  (darg-quoted-natp (darg1 expr))
                  (bv-arg-okp (darg2 expr)))
             (b* ((claimed-width (unquote (darg1 expr)))
                  (bv-arg (darg2 expr))
                  (bv-arg-type (get-type-of-arg-checked bv-arg dag-array-name dag-array cut-nodenum-type-alist))
                  ((when (not (bv-typep bv-arg-type)))
                   (er hard? 'translate-dag-expr "unsigned-byte-p claim applied to non-bv ~x0." bv-arg)
                   (mv (erp-t) nil constant-array-info)) ;todo: allow this function to return an error
                  (known-width (bv-type-width bv-arg-type))
                  ((when (= 0 known-width))
                   (er hard? 'translate-dag-expr "unsigned-byte-p claim with a width of 0 applied to ~x0." bv-arg)
                   (mv :bad-width nil constant-array-info)))
               (mv (erp-nil)
                   (if (<= known-width claimed-width)
                       "(TRUE)" ;the unsigned-byte-p doesn't tell us anything new
                     ;;the unsigned-byte-p-claim amounts to saying that the high bits are 0:
                     (list* "(("
                            (translate-bv-arg bv-arg known-width dag-array-name dag-array dag-len cut-nodenum-type-alist)
                            "["
                            (nat-to-string (+ -1 known-width))
                            ":"
                            (nat-to-string claimed-width)
                            "]) = "
                            (translate-bv-constant 0 (- known-width claimed-width))
                            ")"
                            ))
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        ;; todo: use the typed equality operators?
        (equal
         (if (= 2 (len (dargs expr)))
             (mv-let (translated-expr constant-array-info)
               ;; todo: add this to return an error:
               (translate-equality-to-stp (darg1 expr)
                                          (darg2 expr)
                                          dag-array-name dag-array dag-len cut-nodenum-type-alist constant-array-info)
               (mv (erp-nil)
                   translated-expr
                   constant-array-info))
           (mv (erp-t) nil constant-array-info)))
        (t (mv (erp-t) nil constant-array-info)))
      (if erp
          (prog2$ (er hard? 'translate-dag-expr "Error (~x0) translating expr ~x1.~%" erp expr)
                  ;;todo: pass back the error?
                  (mv nil constant-array-info))
        (mv translated-expr constant-array-info)))))

(local
  (defthm string-treep-of-mv-nth-0-of-translate-dag-expr
    (implies (and (bounded-dag-exprp dag-len expr)
                  (constant-array-infop constant-array-info))
             (string-treep (mv-nth 0 (translate-dag-expr expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (e/d (translate-dag-expr bounded-dag-exprp car-becomes-nth-of-0)
                                    (;(:e nat-to-string-debug) ;problem!
                                     ;;for speed:
                                     ;nat-to-string-debug
                                     max))))))

(local
  (defthm constant-array-infop-of-mv-nth-1-of-translate-dag-expr
    (implies (and (bounded-dag-exprp dag-len expr)
                  (constant-array-infop constant-array-info))
             (constant-array-infop (mv-nth 1 (translate-dag-expr expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable translate-dag-expr bounded-dag-exprp car-becomes-nth-of-0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: strengthen to check that all the nodes are translatable
(defund no-nodes-are-variablesp (nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              ;;combine these 2 things?
                              (nat-listp nodenums)
                              (all-< nodenums dag-len))))
  (if (endp nodenums)
      t
    (let ((expr (aref1 dag-array-name dag-array (first nodenums))))
      (and (consp expr) ; excludes variables
           (no-nodes-are-variablesp (rest nodenums) dag-array-name dag-array dag-len)))))

(defthm no-nodes-are-variablesp-of-append
  (equal (no-nodes-are-variablesp (append list1 list2) dag-array-name dag-array dag-len)
         (and (no-nodes-are-variablesp list1 dag-array-name dag-array dag-len)
              (no-nodes-are-variablesp list2 dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable no-nodes-are-variablesp reverse-list))))

(defthm no-nodes-are-variablesp-of-cons
  (equal (no-nodes-are-variablesp (cons node nodes) dag-array-name dag-array dag-len)
         (and (consp (aref1 dag-array-name dag-array node))
              (no-nodes-are-variablesp nodes dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable no-nodes-are-variablesp))))

(defthm no-nodes-are-variablesp-of-when-not-consp
  (implies (not (consp list))
           (no-nodes-are-variablesp list dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable no-nodes-are-variablesp reverse-list))))

(defthm no-nodes-are-variablesp-of-reverse-list
  (equal (no-nodes-are-variablesp (reverse-list list) dag-array-name dag-array dag-len)
         (no-nodes-are-variablesp list dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable no-nodes-are-variablesp reverse-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv translation constant-array-info) where TRANSLATION is a string-tree.
;; Handles all of the NODENUMS-TO-TRANSLATE.
;could use a worklist?
(defund translate-nodes-to-stp (nodenums-to-translate ;sorted in decreasing order, all translatable (no vars)
                                dag-array-name
                                dag-array
                                dag-len
                                acc ;a string-tree, this should have the translated query (e.g., equality of two nodenums)
                                constant-array-info ; may get extended
                                opened-paren-count  ; may get incremented
                                cut-nodenum-type-alist)
  (declare (xargs :guard (and (nat-listp nodenums-to-translate)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len) ; todo: strengthen to all translatable
                              (string-treep acc)
                              (constant-array-infop constant-array-info)
                              (natp opened-paren-count)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :guard-hints (("Goal" :in-theory (enable <-of-nth-when-all-<
                                                           car-becomes-nth-of-0
                                                           integer-listp-when-nat-listp
                                                           not-cddr-when-dag-exprp-and-quotep
                                                           no-nodes-are-variablesp)))))
  (if (endp nodenums-to-translate)
      (mv (cons acc
                (n-close-parens opened-paren-count nil) ;avoid consing this up?
                )
          constant-array-info)
    (let* ((nodenum (first nodenums-to-translate))
           (expr (aref1 dag-array-name dag-array nodenum)))
      (mv-let (translated-expr constant-array-info)
        (translate-dag-expr expr dag-array-name dag-array dag-len constant-array-info cut-nodenum-type-alist)
        (translate-nodes-to-stp (rest nodenums-to-translate)
                                dag-array-name dag-array dag-len
                                (list* "LET "
                                       (make-node-var nodenum) ;ffixme any possible name clashes?
                                       " = "
                                       translated-expr
                                       " IN (" (newline-string) ; todo: combine these
                                       acc)
                                constant-array-info
                                (+ 1 opened-paren-count)
                                cut-nodenum-type-alist)))))

(local
  (defthm string-treep-of-mv-nth-0-of-translate-nodes-to-stp
    (implies (and (string-treep acc)
                  (constant-array-infop constant-array-info)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (nat-listp nodenums-to-translate)
                  (all-< nodenums-to-translate dag-len))
             (string-treep (mv-nth 0 (translate-nodes-to-stp nodenums-to-translate dag-array-name dag-array dag-len acc constant-array-info opened-paren-count cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable translate-nodes-to-stp nat-listp)))))

(local
  (defthm constant-array-infop-of-mv-nth-1-of-translate-nodes-to-stp
    (implies (and (constant-array-infop constant-array-info)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (nat-listp nodenums-to-translate)
                  (all-< nodenums-to-translate dag-len))
             (constant-array-infop (mv-nth 1 (translate-nodes-to-stp nodenums-to-translate dag-array-name dag-array dag-len acc constant-array-info opened-paren-count cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable translate-nodes-to-stp nat-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;fffixme think about arrays whose lengths are not powers of 2...
;; Returns a string-tree.
(defund make-stp-type-declarations (nodenum-type-alist)
  (declare (xargs :guard (nodenum-type-alistp nodenum-type-alist)
                  :guard-hints (("Goal" :expand (nodenum-type-alistp nodenum-type-alist)
                                 :in-theory (enable axe-typep)))))
  (if (endp nodenum-type-alist)
      nil
    (let* ((entry (first nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry))
           (varname (make-node-var nodenum)) ;todo: could cache and reuse these
           )
      (if (bv-typep type)
          (list* varname
                 " : BITVECTOR("
                 (nat-to-string (bv-type-width type))
                 ");" (newline-string)
                 (make-stp-type-declarations (rest nodenum-type-alist)))
        (if (bv-array-typep type)
            (let* ((element-size (bv-array-type-element-width type))
                   (len (bv-array-type-len type)))
              (if (< len 2)
                  ;; An array in STP must have an index with at least one bit, hence at least 2 elements:
                  (er hard? 'make-stp-type-declarations "Found an array of length 0 or 1 (neither is supported): ~x0." entry)
                (list* varname
                       " : ARRAY BITVECTOR("
                       (nat-to-string (integer-length (+ -1 len)))
                       ") OF BITVECTOR("
                       (nat-to-string element-size)
                       ");"
                       (newline-string)
                       (make-stp-type-declarations (rest nodenum-type-alist)))))
          (if (boolean-typep type)
              (list* varname
                     " : BOOLEAN;"
                     (newline-string)
                     (make-stp-type-declarations (rest nodenum-type-alist)))
            ;; TODO: Tighten the guard to exclude some of these cases:
            (if (empty-typep type)
                (er hard? 'make-stp-type-declarations "empty type detected.")
              (if (most-general-typep type)
                  (er hard? 'make-stp-type-declarations "universal type detected.")
                ;; impossible, given the guard:
                (er hard 'make-stp-type-declarations "Unknown form for type: ~x0." type)))))))))

(local
  (defthm string-treep-of-make-stp-type-declarations
    (string-treep (make-stp-type-declarations nodenum-type-alist))
    :hints (("Goal" :in-theory (enable make-stp-type-declarations)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns a string-tree.
;; (defund make-stp-range-assertions (nodenum-type-alist)
;;   (declare (xargs :guard (nodenum-type-alistp nodenum-type-alist) ;;TODO: This also allows :range types but axe-typep doesn't allow range types?
;;                   :guard-hints (("Goal" :expand (nodenum-type-alistp nodenum-type-alist)
;;                                  :in-theory (enable axe-typep empty-typep list-typep most-general-typep)))))
;;   (if (endp nodenum-type-alist)
;;       nil
;;     (let* ((entry (first nodenum-type-alist))
;;            (nodenum (car entry))
;;            (type (cdr entry)))
;;       (if (consp type)
;;           (if (bv-array-typep type) ;; nothing to do:
;;               (make-stp-range-assertions (rest nodenum-type-alist))
;;             (if (boolean-typep type) ;; nothing to do:
;;                 (make-stp-range-assertions (rest nodenum-type-alist))
;;               (if (eq :range (car type))
;;                   (prog2$ (er hard 'make-stp-range-assertions "range type detected: ~x0." type)
;;                           (let* ((low (second type))
;;                                  (high (third type))
;;                                  (width (integer-length high))
;;                                  (varname (make-node-var nodenum)))
;;                             (list* "ASSERT(BVLE("
;;                                    (translate-bv-constant low width)
;;                                    ","
;;                                    varname
;;                                    "));"
;;                                    (newline-string)
;;                                    "ASSERT(BVLE("
;;                                    varname
;;                                    ","
;;                                    (translate-bv-constant high width)
;;                                    "));"
;;                                    (newline-string)
;;                                    (make-stp-range-assertions (rest nodenum-type-alist)))))
;;                 (er hard? 'make-stp-range-assertions "Unknown form for size: ~x0." type))))
;;         (make-stp-range-assertions (rest nodenum-type-alist))))))

;; (local
;;   (defthm string-treep-of-make-stp-range-assertions
;;     (string-treep (make-stp-range-assertions cut-nodenum-type-alist))
;;     :hints (("Goal" :in-theory (enable make-stp-range-assertions)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
;make tail rec?
(defund make-type-declarations-for-array-constants (constant-array-info)
  (declare (xargs :guard (constant-array-infop constant-array-info)
                  :guard-hints (("Goal" :expand (constant-array-infop constant-array-info)
                                 :in-theory (enable constant-array-infop)))))
  (if (endp constant-array-info)
      nil
    (let* ((entry (first constant-array-info))
           (data (first entry))
           (array-name (second entry))
           (element-width (third entry))
           ;;If the array constant has a length that is not a power of 2, this rounds up the length to the next power of 2
           (index-width (the (integer 1 *) (integer-length (+ -1 (len data))))) ; will be at least 1
           )
      (list* array-name
             " : ARRAY BITVECTOR("
             (nat-to-string index-width)
             ") OF BITVECTOR("
             (nat-to-string element-width)
             ");"
             (newline-string)
             (make-type-declarations-for-array-constants (rest constant-array-info))))))

(local
  (defthm string-treep-of-make-type-declarations-for-array-constants
    (implies (constant-array-infop constant-array-info)
             (string-treep (make-type-declarations-for-array-constants constant-array-info)))
    :hints (("Goal" :in-theory (enable make-type-declarations-for-array-constants constant-array-infop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Returns a string-tree.
;fixme this used to generate too many asserts (which could contradict each other!) if the data is longer than would be expected for the index...  now it counts up to element-count
;; TODO: Optimize by precomputing strings that are the same for each element, including the leading "0bin" parts of the constants.
(defund make-value-assertions-for-array-constant (array-data array-name elemnum element-count index-size element-size acc)
  (declare (xargs :guard (and (natp elemnum)
                              (posp index-size)
                              (posp element-size)
                              (natp element-count)
                              (nat-listp array-data)
                              (<= (- element-count elemnum) (len array-data)))
                  :measure (nfix (+ 1 (- element-count elemnum)))))
  (if (or (<= element-count elemnum)
          (not (natp element-count))
          (not (natp elemnum)))
      acc
    (make-value-assertions-for-array-constant (rest array-data)
                                              array-name
                                              (+ 1 elemnum)
                                              element-count
                                              index-size element-size
                                              (list* "ASSERT "
                                                     array-name
                                                     "["
                                                     (translate-bv-constant elemnum index-size)
                                                     "]="
                                                     (translate-bv-constant (first array-data) element-size)
                                                     ";"
                                                     (newline-string)
                                                     acc))))

(local
  (defthm string-treep-of-make-value-assertions-for-array-constant
    (implies (and (string-treep acc)
                  (string-treep array-name))
             (string-treep (make-value-assertions-for-array-constant array-data array-name elemnum element-count index-size element-size acc)))
    :hints (("Goal" :in-theory (enable make-value-assertions-for-array-constant)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree.
(defund make-value-assertions-for-array-constants (constant-array-info acc)
  (declare (xargs :guard (constant-array-infop constant-array-info)
                  :guard-hints (("Goal" :in-theory (enable constant-array-infop)))))
  (if (endp constant-array-info)
      acc
    (let* ((entry (first constant-array-info))
           (constant-data (first entry))
           (element-count (len constant-data))
           (array-name (second entry))
           (element-width (third entry))
           (index-size (ceiling-of-lg element-count)))
      (if (not (<= 2 element-count))
          (er hard? 'make-value-assertions-for-array-constants "Array is too short: ~x0." entry) ; todo: prove that this can't happen (strengthen constant-array-infop first)
        (make-value-assertions-for-array-constants
          (rest constant-array-info)
          (make-value-assertions-for-array-constant constant-data array-name 0 element-count index-size element-width acc))))))

(local
  (defthm string-treep-of-make-value-assertions-for-array-constants
    (implies (and (string-treep acc)
                  (constant-array-infop constant-array-info))
             (string-treep (make-value-assertions-for-array-constants constant-array-info acc)))
    :hints (("Goal" :in-theory (enable make-value-assertions-for-array-constants make-value-assertions-for-array-constant constant-array-infop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp state).
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
                                 print
                                 state)
  (declare (xargs :stobjs state
                  :guard (and (string-treep translated-query-core)
                              (symbolp dag-array-name)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp nodenums-to-translate)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (string-treep extra-asserts)
                              (stringp filename)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (constant-array-infop constant-array-info)
                              (print-levelp print))))
  (prog2$
   (and (print-level-at-least-tp print) (cw "  ~s0~%" filename))
   (mv-let (translation constant-array-info)
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
             ;; (make-stp-range-assertions cut-nodenum-type-alist)
             (make-type-declarations-for-array-constants constant-array-info)
             (make-value-assertions-for-array-constants constant-array-info nil)
             extra-asserts
             "QUERY (" (newline-string)
             translation                             ;includes the query..
             ");" (newline-string))
      filename
      'write-stp-query-to-file
      state))))

(local
  (defthm w-of-mv-nth-1-of-write-stp-query-to-file
    (equal (w (mv-nth 1 (write-stp-query-to-file translated-query-core dag-array-name dag-array dag-len nodenums-to-translate extra-asserts filename cut-nodenum-type-alist constant-array-info print state)))
           (w state))
    :hints (("Goal" :in-theory (enable write-stp-query-to-file)))))

(local
  (defthm state-p-of-mv-nth-1-of-write-stp-query-to-file
    (implies (state-p state)
             (state-p (mv-nth 1 (write-stp-query-to-file translated-query-core dag-array-name dag-array dag-len nodenums-to-translate extra-asserts filename cut-nodenum-type-alist constant-array-info print state))))
    :hints (("Goal" :in-theory (e/d (write-stp-query-to-file) ())))))

;; We use these constants instead of their corresponding keywords, so that we
;; don't accidentally mis-type the keywords:
(defconst *error* :error)
(defconst *valid* :valid)
(defconst *invalid* :invalid)
(defconst *timedout* :timedout)
(defconst *counterexample* :counterexample)
(defconst *possible-counterexample* :possible-counterexample)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;INPUT-FILENAME is the STP input (.cvc) file name
;OUTPUT-FILENAME is the STP output (.out) file name
;Runs an external script to call STP, using tshell-call.
;FFIXME think about which STP options to use. pass them in via this function?
;Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, or (:counterexample <raw-counterexample>)
;; We don't fix up the counterexample here because we don't have access to the cut-nodenum-type-alist, etc.
(defund call-stp-on-file (input-filename
                          output-filename
                          print ;whether to print the result (valid/invalid/max-conflicts)
                          max-conflicts ;a number of conflicts, or nil for no max
                          counterexamplep
                          state)
  (declare (xargs :guard (and (stringp input-filename)
                              (stringp output-filename)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp counterexamplep))
                  :stobjs state))
  (b* ((counterexample-arg (if counterexamplep "y" "n"))
       (max-conflicts-string (if max-conflicts (nat-to-string max-conflicts) "-1")) ; -1 means no max
       ((mv start-real-time state) (get-real-time state))
       ((mv status state) (call-axe-script "callstp.bash" (list input-filename output-filename max-conflicts-string counterexample-arg) state))
       ;;(- (cw "STP exit status: ~x0~%" status))
       ((mv elapsed-time state) (real-time-since start-real-time state))
       )
    ;;(prog2$ (cw "sys-call status: ~x0~%" status)
    ;;(STP seems to exit with status 0 for both Valid and Invalid examples and with non-zero status for errors.)
    (if (not (eql 0 status)) ;;todo: do we still need to do all these checks?
        (if (eql 143 status)
            ;;exit status 143 seems to indicate max-conflicts (why?!  perhaps it's 128+15 where 15 represents the TERM signal)
            (prog2$ (and print (cw "!! STP timed out !!")) ; todo: there is also a timeout case below
                    (mv *timedout* state))
          (if (eql 201 status)
              (progn$ (er hard? 'call-stp-on-file "!! ERROR: Unable to find STP (define an STP environment var or add its location to your path) !!")
                      (mv *error* state))
            ;; TODO: What is exit status 134?
            (progn$ (er hard? 'call-stp-on-file "!! ERROR: STP experienced an unknown error.  Exit status ~x0.  Input:~%~s1~%Output:~%~s2~% !!"
                        status input-filename output-filename)
                    (mv *error* state))))
      (let ((chars (read-file-into-character-list output-filename state)))
        (if (null chars)
            (prog2$ (er hard? 'call-stp-on-file "Unable to read STP output from file ~x0.~%" output-filename)
                    (mv *error* state))
          ;; Check whether the output file contains "Valid."
          (if (equal chars '(#\V #\a #\l #\i #\d #\. #\Newline)) ;;Look for "Valid."
              (prog2$ (and (print-level-at-least-tp print) (progn$ (cw "  STP said Valid in ")
                                                                   (print-to-hundredths elapsed-time)
                                                                   (cw "s.~%" )))
                      (mv *valid* state))
            ;; Test whether chars end with "Invalid.", perhaps preceded by a printed counterexample.
            (if (and (<= 9 (len chars)) ;9 is the length of "Invalid." followed by newline - todo make a function 'char-list-ends-with'
                     (equal (nthcdr (- (len chars) 9) chars)
                            '(#\I #\n #\v #\a #\l #\i #\d #\. #\Newline))) ;;Look for "Invalid."
                (b* ((- (and (print-level-at-least-tp print) (progn$ (cw "  STP said Invalid in ")
                                                                     (print-to-hundredths elapsed-time)
                                                                     (cw "s.~%" ))))
                     ;; Print the counterexample (TODO: What if it is huge?):
                     (counterexamplep-chars (butlast chars 9))
;(- (and print counterexamplep (cw "~%Counterexample:~%~S0" (coerce counterexamplep-chars 'string))))
                     (parsed-counterexample (parse-counterexample counterexamplep-chars nil))
;(- (and print counterexamplep (cw "~%Parsed counterexample:~%~x0~%" parsed-counterexample)))
                     ((when (eq :error parsed-counterexample))
                      (er hard? 'call-stp-on-file "!! ERROR parsing counterexample.")
                      (mv *error* state)))
                  (mv (if counterexamplep
                          `(,*counterexample* ,parsed-counterexample)
                        *invalid*)
                      state))
              (if (or ;(equal chars '(#\T #\i #\m #\e #\d #\Space #\O #\u #\t #\, #\Space  #\e #\x #\i #\t #\i #\n #\g #\.)) ;add newline??
                   (equal chars '(#\T #\i #\m #\e #\d #\Space #\O #\u #\t #\. #\Newline))) ;;Look for "Timed Out."
                  (prog2$ (and print (progn$ (cw "  STP timed out (max conflicts) in ")
                                             (print-to-hundredths elapsed-time)
                                             (cw "s.~%")))
                          (mv *timedout* state))
                (prog2$ (er hard? 'call-stp-on-file "STP returned an unexpected result (~x0).  Check the .out file: ~x1.~%" chars output-filename)
                        (mv *error* state))))))))))

(local
  (defthm call-stp-on-file-return-type
    (let ((res (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state))))
      (implies (and (not (equal *error* res))
                    (not (equal *valid* res))
                    (not (equal *invalid* res))
                    (not (equal *timedout* res)))
               (and (true-listp res)
                    (equal (car res) *counterexample*)
                    (raw-counterexamplep (second res))
                    (equal (len res) 2))))
    :hints (("Goal" :in-theory (enable call-stp-on-file)))))

(local
  (defthm raw-counterexamplep-of-cadr-of-mv-nth-0-of-call-stp-on-file
    (implies (consp (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state)))
             (raw-counterexamplep (cadr (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state)))))
    :hints (("Goal" :in-theory (enable call-stp-on-file)))))

(local
  (defthm len-of-mv-nth-0-of-call-stp-on-file
    (implies (consp (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state)))
             (equal (len (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state)))
                    2))
    :hints (("Goal" :in-theory (e/d (call-stp-on-file) ())))))

(local
  (defthm consp-of-mv-nth-0-of-call-stp-on-file
    (implies (not (member-equal (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state)) (list *error* *valid* *invalid* *timedout*)))
             (consp (mv-nth 0 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state))))
    :hints (("Goal" :in-theory (e/d (call-stp-on-file) ())))))

(local
  (defthm w-of-mv-nth-1-of-call-stp-on-file
    (equal (w (mv-nth 1 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state)))
           (w state))
    :hints (("Goal" :in-theory (enable call-stp-on-file)))))

(local
  (defthm state-p-of-mv-nth-1-of-call-stp-on-file
    (implies (state-p state)
             (state-p (mv-nth 1 (call-stp-on-file input-filename output-filename print max-conflicts counterexamplep state))))
    :hints (("Goal" :in-theory (enable call-stp-on-file)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: What if we cut out some structure but it is not involved in the counterexample?
(defund all-cuts-are-at-varsp (cut-nodenum-type-alist dag-array-name dag-array)
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
         (all-cuts-are-at-varsp (rest cut-nodenum-type-alist) dag-array-name dag-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                              max-conflicts ;a number of conflicts!, or nil for no max
                              constant-array-info ;may get an entry when we create translated-query-core (e.g., if a term is equated to a constant array)
                              counterexamplep
                              print-cex-as-signedp
                              state)
  (declare (xargs :guard (and (nat-listp nodenums-to-translate)
                              (stringp extra-string)
                              (string-treep extra-asserts)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (symbolp dag-array-name)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (all-< (strip-cars cut-nodenum-type-alist) ;drop?
                                     (alen1 dag-array-name dag-array))
                              (all-< (strip-cars cut-nodenum-type-alist)
                                     dag-len)
                              (string-treep translated-query-core)
                              (constant-array-infop constant-array-info))
                  :stobjs state))
  (b* (((mv temp-dir-name state)
        (maybe-make-temp-dir state))
       (base-filename (concatenate 'string temp-dir-name "/" base-filename))
       (base-filename (maybe-shorten-filename base-filename))
       (- (and (print-level-at-least-tp print) (cw "(Calling STP ~s0 (max-conflicts ~x1):~%" extra-string max-conflicts)))
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
                                 print
                                 state))
       ((when erp)
        (er hard? 'prove-query-with-stp "Unable to write the STP input file: ~s0 before calling STP." stp-input-filename)
        (mv *error* state))
       ;;clear the output file:
       ;;this is in case something fails (like permissions) and the attempt to run STP leaves an old .out file in place
       ;;(which might have the wrong answer in it!)
       ((mv erp state)
        (write-strings-to-file! nil stp-output-filename 'prove-query-with-stp state)) ;todo: make a function to clear a file..
       ((when erp)
        (er hard? 'prove-query-with-stp "Unable to clear the output file: ~s0 before calling STP." stp-output-filename)
        (mv *error* state))
       ;; Call STP on the file:
       ((mv result state)
        (call-stp-on-file stp-input-filename stp-output-filename print max-conflicts counterexamplep state))
       (counterexamplep (and (consp result)
                             (eq *counterexample* (car result)))) ;todo: maybe this should be labeled as :raw-counterexample?
       ((mv erp counterexample)
        (if (not counterexamplep)
            (mv (erp-nil) nil)
          (let ((raw-counterexample (cadr result)))
            (fixup-counterexample (sort-nodenum-type-alist cut-nodenum-type-alist) raw-counterexample nil))))
       ((when erp) (mv *error* state))
       (counterexample-certainp (and counterexamplep
                                     (all-cuts-are-at-varsp cut-nodenum-type-alist dag-array-name dag-array)))
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
                    (- (print-counterexample counterexample cut-nodenum-type-alist print-cex-as-signedp dag-array-name dag-array))
                    (- (cw ")~%")))
                 nil)))
       ;; ((when (eq result *error*)) ;todo: can this happen or would a hard error have already been thrown?
       ;;  (progn$ (cw "!! ERROR !! Translated query core: ~x0~%" translated-query-core)
       ;;          (if nodenums-to-translate
       ;;              (print-dag-array-node-and-supporters-list nodenums-to-translate dag-array-name dag-array)
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
       (- (and (print-level-at-least-tp print) (cw "Done calling STP.)~%"))) ;matches "(Calling STP"
       )
    ;;no error:
    (mv result state)))

;; use this more?
(defund stp-resultp (res)
  (declare (xargs :guard t))
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
           (equal (len res) 2))))

(defthmd len-when-stp-resultp
  (implies (stp-resultp res)
           (equal (len res)
                  (if (member-eq res (list *error* *valid* *invalid* *timedout*))
                      0
                    2)))
  :hints (("Goal" :in-theory (enable stp-resultp member-equal))))

(defthmd true-listp-when-stp-resultp
  (implies (stp-resultp res)
           (equal (true-listp res)
                  (not (member-eq res (list *error* *valid* *invalid* *timedout*)))))
  :hints (("Goal" :in-theory (enable stp-resultp member-equal))))

(defthmd cdr-when-stp-resultp-iff
  (implies (stp-resultp res)
           (iff (cdr res)
                (not (member-eq res (list *error* *valid* *invalid* *timedout*)))))
  :hints (("Goal" :in-theory (enable stp-resultp member-equal))))

(defthmd consp-when-stp-resultp
  (implies (stp-resultp res)
           (equal (consp res)
                  (not (member-eq res (list *error* *valid* *invalid* *timedout*)))))
  :hints (("Goal" :in-theory (enable stp-resultp))))

(defthm prove-query-with-stp-return-type
  (implies (nodenum-type-alistp cut-nodenum-type-alist)
           (stp-resultp (mv-nth 0 (prove-query-with-stp translated-query-core extra-string dag-array-name dag-array dag-len nodenums-to-translate extra-asserts base-filename cut-nodenum-type-alist print max-conflicts constant-array-info counterexamplep print-cex-as-signedp state))))
  :hints (("Goal" :in-theory (enable prove-query-with-stp stp-resultp))))

;do we need this?
(defthm prove-query-with-stp-return-type-corollary-1
  (implies (nodenum-type-alistp cut-nodenum-type-alist)
           (let ((res (mv-nth 0 (prove-query-with-stp translated-query-core extra-string dag-array-name dag-array dag-len nodenums-to-translate extra-asserts base-filename cut-nodenum-type-alist print max-conflicts constant-array-info counterexamplep print-cex-as-signedp state))))
             (implies (eq (first res) *counterexample*)
                      (counterexamplep (second res)))))
  :hints (("Goal" :use prove-query-with-stp-return-type
           :in-theory (e/d (stp-resultp) (prove-query-with-stp-return-type)))))

(defthm w-of-mv-nth-1-of-prove-query-with-stp
  (equal (w (mv-nth 1 (prove-query-with-stp translated-query-core extra-string dag-array-name dag-array dag-len nodenums-to-translate extra-asserts base-filename cut-nodenum-type-alist
                                            print max-conflicts constant-array-info counterexamplep print-cex-as-signedp state)))
         (w state))
  :hints (("Goal" :in-theory (enable prove-query-with-stp))))

(defthm state-p-of-mv-nth-1-of-prove-query-with-stp
  (implies (state-p state)
           (state-p (mv-nth 1 (prove-query-with-stp translated-query-core extra-string dag-array-name dag-array dag-len nodenums-to-translate extra-asserts base-filename cut-nodenum-type-alist
                                                    print max-conflicts constant-array-info counterexamplep print-cex-as-signedp state))))
  :hints (("Goal" :in-theory (e/d (prove-query-with-stp) (state-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bounded-stp-resultp (res bound)
  (declare (xargs :guard (natp bound)))
  (or (eq *error* res)
      (eq *valid* res)
      (eq *invalid* res)
      (eq *timedout* res)
      (and (true-listp res)
           (eq (first res) *counterexample*)
           (bounded-counterexamplep (second res) bound)
           (equal (len res) 2))
      (and (true-listp res)
           (eq (first res) *possible-counterexample*)
           (bounded-counterexamplep (second res) bound)
           (equal (len res) 2))))

(defthm bounded-stp-resultp-of-mv-nth-0-of-prove-query-with-stp
  (implies (and (nodenum-type-alistp cut-nodenum-type-alist)
                (all-< (strip-cars cut-nodenum-type-alist) dag-len))
           (bounded-stp-resultp
             (mv-nth 0 (prove-query-with-stp translated-query-core extra-string dag-array-name dag-array dag-len nodenums-to-translate extra-asserts base-filename cut-nodenum-type-alist print max-conflicts constant-array-info counterexamplep print-cex-as-signedp state))
             dag-len))
  :hints (("Goal" :in-theory (enable prove-query-with-stp bounded-stp-resultp))))

(defthm bounded-stp-resultp-atoms
  (and (bounded-stp-resultp *error* bound)
       (bounded-stp-resultp *valid* bound)
       (bounded-stp-resultp *invalid* bound)
       (bounded-stp-resultp *timedout* bound))
  :hints (("Goal" :in-theory (enable bounded-stp-resultp))))

(defthm bounded-counterexamplep-of-second-when-bounded-stp-resultp
  (implies (and (bounded-stp-resultp res bound)
                (or (equal (first res) *counterexample*)
                    (equal (first res) *possible-counterexample*)))
           (bounded-counterexamplep (second res) bound))
  :hints (("Goal" :in-theory (enable bounded-stp-resultp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to prove the equality of LHS and RHS, which are dargs.
;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
;; TODO: Unify param order with prove-query-with-stp
;; todo: start by checking whether LHS and RHS are equal?
(defund prove-equality-with-stp (lhs ;a nodenum or quotep
                                 rhs ;a nodenum or quotep
                                 ;;todo: add an extra-string arg
                                 dag-array-name dag-array dag-len
                                 nodenums-to-translate ;sorted in decreasing order
                                 base-filename
                                 cut-nodenum-type-alist
                                 extra-asserts
                                 print
                                 max-conflicts ;a number of conflicts, or nil for no max
                                 counterexamplep
                                 print-cex-as-signedp
                                 state)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (or (myquotep lhs)
                                  (and (natp lhs)
                                       (< lhs dag-len)))
                              (or (myquotep rhs)
                                  (and (natp rhs)
                                       (< rhs dag-len)))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (stringp base-filename)
                              (symbolp dag-array-name)
                              (nat-listp nodenums-to-translate)
                              (all-< nodenums-to-translate dag-len)
                              (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                              (string-treep extra-asserts)
                              (print-levelp print))
                  :stobjs state))
  (mv-let (translated-expr constant-array-info)
    (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist nil)
    (prove-query-with-stp translated-expr
                          "" ;extra-string: todo: use this
                          dag-array-name
                          dag-array
                          dag-len
                          nodenums-to-translate
                          extra-asserts
                          base-filename
                          cut-nodenum-type-alist
                          print max-conflicts constant-array-info
                          counterexamplep
                          print-cex-as-signedp
                          state)))

(defthm stp-resultp-of-mv-nth-0-of-prove-equality-with-stp
  (implies (nodenum-type-alistp cut-nodenum-type-alist)
           (stp-resultp (mv-nth 0 (prove-equality-with-stp lhs rhs dag-array-name dag-array dag-len nodenums-to-translate base-filename cut-nodenum-type-alist extra-asserts
                                                           print max-conflicts counterexamplep print-cex-as-signedp state))))
  :hints (("Goal" :in-theory (enable prove-equality-with-stp)
           :use (:instance prove-query-with-stp-return-type
                           (translated-query-core (mv-nth 0 (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist nil)))
                           (extra-string "")
                           (constant-array-info (mv-nth 1 (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist nil)))))))

;; do we need both this and the one just above?
(defthm bounded-stp-resultp-of-mv-nth-0-of-prove-equality-with-stp
  (implies (and (nodenum-type-alistp cut-nodenum-type-alist)
                (all-< (strip-cars cut-nodenum-type-alist) dag-len))
           (bounded-stp-resultp (mv-nth 0 (prove-equality-with-stp lhs rhs dag-array-name dag-array dag-len nodenums-to-translate base-filename cut-nodenum-type-alist extra-asserts
                                                                   print max-conflicts counterexamplep print-cex-as-signedp state))
                                dag-len))
  :hints (("Goal" :in-theory (e/d (prove-equality-with-stp) (bounded-stp-resultp-of-mv-nth-0-of-prove-query-with-stp))
           :use (:instance bounded-stp-resultp-of-mv-nth-0-of-prove-query-with-stp
                           (translated-query-core (mv-nth 0 (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist nil)))
                           (extra-string "")
                           (constant-array-info (mv-nth 1 (translate-equality-to-stp lhs rhs dag-array-name dag-array dag-len cut-nodenum-type-alist nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;get this working by generating an appropriate cut-nodenum-type-alist
;; ;pass in a dag-array-name?
;; ;; returns (mv validp timedoutp state) where validp indicates whether STP said "Valid."
;; (defun prove-with-stp-quick (dag-lst var-type-alist max-conflicts state)
;;   (declare (xargs
;;                   :stobjs state))
;;   (let* ((dag-array (make-into-array 'dag-array dag-lst))
;;          (dag-len (len dag-lst)))
;;     (prove-equality-with-stp (+ -1 dag-len) ;top node of the dag (we prove it equals true)
;;                              *t*
;;                              'dag-array
;;                              dag-array
;;                              :all ;ffixme what if there are non-pure operators?  should probably cut there!
;;                              "stpquick"
;;                              ;var-type-alist
;;                              nil ;cut-nodenum-type-alist fffixme!
;;                              nil t   ;print
;;                              max-conflicts
;;                              state)))

;; ;; ;get this working again by generating an appropriate cut-nodenum-type-alist
;; ;dag-len might be smaller than the actual-len?
;; ;pass in a dag-array-name?
;; ;; returns (mv validp timedoutp state)
;; ;was called prove-whole-dag-with-stp before changes
;; (defun prove-array-node-with-stp (dag-array
;;                                   nodenum ;; the node to be proved true
;;                                   var-type-alist max-conflicts state)
;;   (declare (xargs
;;                   :stobjs state))
;;   (prove-equality-with-stp nodenum
;;                            *t*
;;                            'dag-array
;;                            dag-array
;;                            :all ;;ffffixme this may be overkill and may cause errors?  ;ffixme what if there are non-pure operators?  should probably cut there!
;;                            "stptmpfile"
;;                            ;var-type-alist
;;                            nil   ;cut-nodenum-type-alist
;;                           nil t     ;print
;;                            max-conflicts
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
;;     (make-node-var item)))

;; Returns a string-tree.
(defund translate-possibly-negated-nodenum (item)
  (declare (xargs :guard (possibly-negated-nodenump item)
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenump)))))
  (if (consp item) ;test for call of NOT
      (list* "(NOT("
             (make-node-var (farg1 item))
             "))")
    (make-node-var item)))

(local
  (defthm string-treep-of-translate-possibly-negated-nodenum
    (string-treep (translate-possibly-negated-nodenum item))
    :hints (("Goal" :in-theory (enable translate-possibly-negated-nodenum)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns a string-tree
;the input must have at least one element
;make tail rec with an acc?
(defund translate-disjunction-aux (items)
  (declare (xargs :guard (and (consp items)
                              (possibly-negated-nodenumsp items))
                  :guard-hints (("Goal" ;:use (:instance consp-of-car-when-possibly-negated-nodenumsp-weaken-cheap)
                                 :expand (POSSIBLY-NEGATED-NODENUMSP ITEMS)
                                 ;:in-theory (disable consp-of-car-when-possibly-negated-nodenumsp-weaken-cheap)
                                 ))))
  (if (endp items)
      (er hard 'translate-disjunction-aux "No items (must be at least one)!")
    (if (endp (cdr items))
        (translate-possibly-negated-nodenum (first items))
      (cons (translate-possibly-negated-nodenum (first items))
            (cons " OR "
                  (translate-disjunction-aux (rest items)))))))

(local
  (defthm string-treep-of-translate-disjunction-aux
    (string-treep (translate-disjunction-aux items))
    :hints (("Goal" :in-theory (enable translate-disjunction-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Handle constant disjunctions?
;returns a string-tree
(defund translate-disjunction (items)
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
  (string-treep (translate-disjunction items))
  :hints (("Goal" :in-theory (enable translate-disjunction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
