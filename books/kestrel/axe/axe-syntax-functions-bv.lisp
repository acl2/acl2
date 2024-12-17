; BV-related syntactic tests
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

;; This book contains bit-vector-related functions that support Axe
;; rules that call axe-syntaxp and axe-bind-free.

(include-book "axe-types") ;reduce?  we just need the bv-type stuff
(include-book "dag-arrays")
(include-book "kestrel/bv/bv-syntax" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (enable car-becomes-nth-of-0
                          integerp-of-nth-when-darg-listp
                          not-cddr-of-nth-when-darg-listp
                          consp-of-cdr-of-nth-when-darg-listp
                          equal-of-quote-and-nth-0-of-nth-when-darg-listp
                          symbolp-of-nth-0-when-dag-exprp
                          dargp-of-nth-when-darg-listp)))

(defund unquote-if-possible (x)
  (declare (xargs :guard t))
  (if (and (quotep x)
           (consp (cdr x)))
      (unquote x)
    nil))

;; Returns a bv-typep or nil (if we could not determine a type).
;the args are nodenums or quoteps - we don't deref nodenums that may point to quoteps
;what if the number of arguments is wrong?
;; NOTE: Soundness depends on this since it is used in the STP translation.
(defund maybe-get-type-of-bv-function-call (fn dargs)
  (declare (xargs :guard (darg-listp dargs)))
  ;; todo: use case here:
  (cond ;see unsigned-byte-p-1-of-bitxor, etc.:
   ((member-eq fn '(getbit bitxor bitand bitor bitnot bool-to-bit))
    (make-bv-type 1))
   ;; Functions whose type is indicated by the first argument:
   ((member-eq fn '(bvchop ;$inline
                    bvxor bvand bvor bvnot
                    bvplus bvminus bvuminus bvmult
                    bvsx
                    bv-array-read
                    repeatbit
                    bvdiv bvmod
                    sbvdiv sbvrem
                    leftrotate rightrotate ;; see unsigned-byte-p-of-leftrotate and unsigned-byte-p-of-rightrotate
                    bvif
                    bvshl
                    bvshr))
    (and (consp dargs)
         (let ((width (first dargs)))
           (and (darg-quoted-natp width)
                (make-bv-type (unquote width))))))
   ;; 32-bit operations:
   ;;see unsigned-byte-p-32-of-leftrotate32 and unsigned-byte-p-32-of-rightrotate32:
   ((member-eq fn '(leftrotate32 rightrotate32)) ;eventually drop?
    (make-bv-type 32))
   ;; Slice:
   ((eq fn 'slice)
    (let ((high (unquote-if-possible (first dargs)))
          (low (unquote-if-possible (second dargs))))
      (and (natp high)
           (natp low)
           (<= low high)
           (make-bv-type (+ 1 high (- low))))))
   ;; Bvcat:
   ((eq fn 'bvcat)
    (let ((high-size (unquote-if-possible (first dargs)))
          (low-size (unquote-if-possible (third dargs))))
      (and (natp high-size)
           (natp low-size)
           (make-bv-type (+ high-size low-size)))))
   ;; Unknown function, can't find a BV size:
   (t nil)))

(defthm maybe-get-type-of-bv-function-call-type
  (or (null (maybe-get-type-of-bv-function-call fn dargs))
      (natp (maybe-get-type-of-bv-function-call fn dargs)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable maybe-get-type-of-bv-function-call
                                     <-of-0-and-make-bv-type))))

;; If it's not nil, it's a bv-type.
(defthm bv-typep-of-maybe-get-type-of-bv-function-call
  (implies (maybe-get-type-of-bv-function-call fn dargs)
           (bv-typep (maybe-get-type-of-bv-function-call fn dargs)))
  :hints (("Goal" :in-theory (enable maybe-get-type-of-bv-function-call))))

;; If it's not nil, it's an axe-type.
(defthm axe-typep-of-maybe-get-type-of-bv-function-call
  (implies (maybe-get-type-of-bv-function-call fn dargs)
           (axe-typep (maybe-get-type-of-bv-function-call fn dargs)))
  :hints (("Goal" :in-theory (enable maybe-get-type-of-bv-function-call))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns an alist that binds VARNAME to the size of the nodenum-or-quotep, if it is a bit vector with a statically known size, or nil to indicate failure.
;bozo redo to support different sets of operators <- ??
;todo: can we save adding a quote to the returned size?
;; todo: consider an option to not count constants as BV terms in this sense
(defund bind-bv-size-axe (nodenum-or-quotep quoted-varname dag-array)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (natp nodenum-or-quotep)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))))))
  (if (not (and (myquotep quoted-varname) ;todo: just call consp?
                (symbolp (unquote quoted-varname))))
      (er hard? 'bind-bv-size-axe "Unexpected varname argument: ~x0." quoted-varname)
    (if (consp nodenum-or-quotep) ;test for quotep
        (let ((val (unquote nodenum-or-quotep)))
          (if (natp val)
              (acons (unquote quoted-varname) (list 'quote (integer-length val)) nil)
            ;; failure (may be a constant array or a negative number or something else):
            nil))
      ;;otherwise, it's a nodenum:
      (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
        (if (not (consp expr))
            nil ;failure (it's a variable)
          (let ((fn (ffn-symb expr)))
            (if (eq 'quote fn)
                (let ((val (unquote expr)))
                  (if (natp val)
                      (acons (unquote quoted-varname) (list 'quote (integer-length val)) nil)
                    ;; failure (may be a constant array or a negative or something else):
                    nil))
              (let ((type (maybe-get-type-of-bv-function-call fn (dargs expr))))
                (if type
                    (acons (unquote quoted-varname) (list 'quote (bv-type-width type)) nil) ;could often save this quote since in many operators the size is already quoted
                  ;;failure:
                  nil)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund term-should-be-trimmed-axe-helper (width term operators dag-array)
  (declare (xargs :guard (and (natp width)
                              (member-eq operators '(all non-arithmetic))
                              (or (myquotep term)
                                  (and (natp term)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term)))))))
  (if (consp term) ; check for quotep
      (or (not (natp (unquote term)))
          ;;(< width (integer-length (unquote term)))
          (<= (expt 2 width) (unquote term)) ;this may be faster, since expt may be built in (maybe just a shift)?
          )
    ;; term must be a nodenum, so look it up
    (let ((expr (aref1 'dag-array dag-array term)))
      (and (consp expr)
           (or (member-eq (ffn-symb expr) (if (eq 'all operators) ;TODO: Use :all instead?
                                              *trimmable-operators*
                                            *trimmable-non-arithmetic-operators*))
;trimming a read from a constant array can turn a single read operation into many (one for each bit)
;but do we need the trimming to use the rules that find patterns in array values?
;maybe we should trim iff we are using getbit-of-bv-array-read?

               ;;                    ;fixme this may be a bad idea?
               ;;                    (and (eq 'bv-array-read (ffn-symb expr))
               ;;                         (quotep (darg4 expr)))
               )
           (let ((type (maybe-get-type-of-bv-function-call (ffn-symb expr) (dargs expr))))
             (and type
                  (< width (bv-type-width type))))))))

;OPERATORS should be 'all or 'non-arithmetic
;maybe we should add the option to not trim logical ops?  but that's not as dangerous as trimming arithmetic ops...
(defund term-should-be-trimmed-axe (quoted-width term operators dag-array)
  (declare (xargs :guard (and (or (myquotep quoted-width)
                                  (and (natp quoted-width)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-width))))
                              (or (myquotep term)
                                  (and (natp term)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term))))
                              ;; (member-equal operators '('all 'non-arithmetic)) ;todo: why are these quoted?
                              )))
  (and (if (or (equal operators ''all) ;; todo: can we avoid this?  use one as the default?
               (equal operators ''non-arithmetic))
           t
         (progn$
          ;; (cw "Warning: In term-should-be-trimmed-axe: Unexpected operators: ~x0.)~%" operators)
          nil))
       (if (and (consp quoted-width)          ; test for quotep
                (natp (unquote quoted-width)) ;check natp or posp?
                )
           t
         (progn$ ;; When variable shifts are involved, we may indeed see BV sizes that are not constants:
          ;; (cw "Warning: In term-should-be-trimmed-axe: Unexpected width: ~x0.)~%"
          ;;     (if (consp quoted-width) ; check for quotep
          ;;         quoted-width
          ;;       ;; simplify this?:
          ;;       (if (and (not (myquotep term))
          ;;                (natp quoted-width)
          ;;                (< quoted-width (alen1 'dag-array dag-array)))
          ;;           (aref1 'dag-array dag-array quoted-width)
          ;;         :unknown)))
          nil))
       (let ((width (unquote quoted-width)))
         (term-should-be-trimmed-axe-helper width term (unquote operators) dag-array))))

;adds 1 to QUOTED-WIDTH;
;for (slice 7 0 x) the relevant width to consider is 8, not 7.  likewise for (getbit 7 x).
(defund term-should-be-trimmed-axe-plus-one (quoted-width term operators dag-array)
  (declare (xargs :guard (and (or (myquotep term)
                                  (and (natp term)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term))))
                              ;; (member-equal operators '('all 'non-arithmetic)) ;todo: why are these quoted?
                              )))
  (and (if (or (equal operators ''all) ;; todo: can we avoid this?  use one as the default?
               (equal operators ''non-arithmetic))
           t
         (progn$
          ;; (cw "Warning: In term-should-be-trimmed-axe-plus-one: Unexpected operators: ~x0.)~%" operators)
          nil))
       (if (and (myquotep quoted-width)
                (natp (unquote quoted-width)))
           t
         (progn$ ;; When variable shifts are involved, we may indeed see BV sizes that are not constants:
          ;; (cw "Warning: In term-should-be-trimmed-axe-plus-one: Unexpected width: ~x0.)~%"
          ;;     (if (quotep quoted-width)
          ;;         quoted-width
          ;;       ;; simplify this?:
          ;;       (if (and (not (myquotep term))
          ;;                (natp quoted-width)
          ;;                (< quoted-width (alen1 'dag-array dag-array)))
          ;;           (aref1 'dag-array dag-array quoted-width)
          ;;         :unknown)))
          nil))
       (let ((width (+ 1 (unquote quoted-width)))) ;the plus one is for this version
         (term-should-be-trimmed-axe-helper width term (unquote operators) dag-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;term and nest are nodenums or quoteps?
(defund bv-array-write-nest-ending-inp-axe (term nest dag-array)
  (declare (xargs :guard (or (myquotep nest)
                             (and (natp nest)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                  :measure (nfix nest)))
  (if (quotep nest)
      (equal term nest)
    (let ((expr (aref1 'dag-array dag-array nest)))
      (and (consp expr)
           (eq 'bv-array-write (ffn-symb expr))
           (= 5 (len (dargs expr)))
           (if (quotep (darg5 expr))
               (equal term (darg5 expr))
             (and (natp (darg5 expr))         ;drop somehow?
                  (mbt (natp nest))           ;for termination
                  (mbt (< (darg5 expr) nest)) ;for termination
                  (bv-array-write-nest-ending-inp-axe term
                                                      (darg5 expr)
                                                      dag-array)))))))

;; ;; scheme for getting rid of logext-lists in myif nests

;; ;bozo right now, this only looks for logext-list on a branch <- huh?
;; ;looks for a logext-list with a size >= size.
;; ;bozo might this recheck the same nodes over and over?
;; ;now only storing myif nodes in nodes-checked?
;; ;Returns (mv result nodes-checked).
;; (defun myif-nest-needs-bvchop-list-aux (node size dag-array nodes-checked)
;;   (declare (xargs :guard (and (natp size)
;;                               (integer-listp nodes-checked)
;;                               (or (myquotep node)
;;                                   (and (natp node)
;;                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 node)))))
;;                   :verify-guards nil ;done below
;;     ;                  :normalize nil
;;                   :measure (nfix node)))
;;   (if (or (quotep node)
;;           (not (mbt (natp node))))
;;       (mv nil nodes-checked) ;bozo could check that the constant value is a all-signed-byte-p..
;;     (let* ((expr (aref1 'dag-array dag-array node)))
;;       (if (not (consp expr))
;;           (mv nil (cons node nodes-checked))
;;         (let ((fn (ffn-symb expr)))
;;           (if (eq 'myif fn)
;;               (let ((then-part (darg2 expr))
;;                     (else-part (darg3 expr)))
;;                 ;; The reason this code is so gross is that mv-let blocks ACL2
;;                 ;; from seeing conditionals inside it for termination.
;;                 (if (or (not (eql 3 (len (dargs expr)))) ;drop?
;;                         (not (mbt (or (quotep then-part)
;;                                       (and (natp then-part)
;;                                            (< then-part node)))))
;;                         (not (mbt (or (quotep else-part)
;;                                       (and (natp else-part)
;;                                            (< else-part node))))))
;;                     (mv nil nil)
;;                   (if (or (quotep then-part)
;;                           (member then-part nodes-checked))
;;                       ;; don't look in the then branch:
;;                       (if (or (quotep else-part)
;;                               (member else-part nodes-checked))
;;                           ;; look in neither branch:
;;                           (mv nil (cons node nodes-checked))
;;                         ;; look only in the else branch:
;;                         (myif-nest-needs-bvchop-list-aux else-part size dag-array nodes-checked))
;;                     ;; look in the then branch (and perhaps in the else branch):
;;                     (if (or (quotep else-part)
;;                             (member else-part nodes-checked))
;;                         ;; look only in the then branch:
;;                         (myif-nest-needs-bvchop-list-aux then-part size dag-array nodes-checked)
;;                       ;; look in both branches:
;;                       (mv-let (then-result nodes-checked)
;;                         (myif-nest-needs-bvchop-list-aux then-part size dag-array nodes-checked)
;;                         (if then-result
;;                             (mv t nil) ;nodes checked doesn't matter
;;                           (myif-nest-needs-bvchop-list-aux else-part size dag-array nodes-checked)))))))
;;             (if (and (equal 'logext-list fn)
;;                      (eql 2 (len (dargs expr))))
;;                 (let ((size2 (darg1 expr)))
;;                   (if (and (quotep size2)
;;                            (integerp (unquote size2))
;;                            (<= size (unquote size2)))
;;                       (mv t nil)
;;                     (mv nil nodes-checked)))
;;               ;;it isn't a myif nest or a logext-list
;;               (mv nil (cons node nodes-checked)))))))))

;; (defthm integer-listp-of-mv-nth-1-of-myif-nest-needs-bvchop-list-aux
;;   (implies (integer-listp nodes-checked)
;;            (integer-listp (mv-nth 1 (myif-nest-needs-bvchop-list-aux node size dag-array nodes-checked))))
;;   :hints (("Goal" :in-theory (enable integer-listp))))

;; (verify-guards myif-nest-needs-bvchop-list-aux
;;   :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
;;   )

;; ;fixme do we still use this?
;; (defund myif-nest-needs-bvchop-list (node size dag-array)
;;   (declare (xargs :guard (and (natp size)
;;                               (or (myquotep node)
;;                                   (and (natp node)
;;                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 node)))))))
;;   (if (quotep size)
;;       (mv-let (result nodes-checked)
;;               (myif-nest-needs-bvchop-list-aux node (unquote size) dag-array nil)
;;               (declare (ignore nodes-checked))
;;               result)
;;     nil))

;in case we can't decide which form to prefer
;move
(defthmd car-when-nth-0-constant
  (implies (and (equal (nth 0 x) k)
                (syntaxp (quotep k)))
           (equal (car x)
                  k)))

;BOZO for what other terms is it syntactically evident that they have low zeros?
;termination depends on dag property?
(defund bvcat-nest-with-low-zerosp-axe-aux (term zero-count-needed dag-array)
  (declare (xargs :measure (if (quotep term)
                               0
                             (+ 1 (nfix term)))
;                  :guard (ALISTP DAG-ARRAY)
                  :guard (and (natp zero-count-needed)
                              (or (myquotep term)
                                  (and (natp term)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term)))))
;                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :guard-hints (("Goal" :in-theory (enable cadr-becomes-nth-of-1)))
;:verify-guards nil
                  ))
  (if (or (quotep term)
          (not (mbt (natp term)))) ;for termination
      (equal (unquote term) 0) ;bozo think about when the constant isn't wrapped in any bvcats
    ;;it's a nodenum, so look it up:
    (let* ((expr (aref1 'dag-array dag-array term)))
      (if (atom expr) ;check for variable
          nil
        (if (eq 'quote (car expr))
            (equal (unquote expr) 0) ;bozo think about when the constant isn't wrapped in any bvcats
          (and (true-listp expr)     ;for guards (TODO: use mbt?)
               (eq 'bvcat (ffn-symb expr))
               (= 4 (len (dargs expr)))
               (let ((lowsize (darg3 expr)))
                 (and (quotep lowsize)
                      (natp (unquote lowsize))
                      (let ((lowsize (unquote lowsize)))
                        (and (<= zero-count-needed lowsize) ;keep looking in the low value
                             (eql 4 (len (dargs expr)))
                             (mbt (or (quotep (darg4 expr)) ;for termination
                                      (and (< (darg4 expr) term)
                                           (natp (darg4 expr)))))
                             (bvcat-nest-with-low-zerosp-axe-aux (darg4 expr) zero-count-needed dag-array)))))))))))

;zero-count-needed is quoted
(defund bvcat-nest-with-low-zerosp-axe (term zero-count-needed dag-array)
  (declare (xargs :guard (or (myquotep term)
                             (and (natp term)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term))))))
  (and (myquotep zero-count-needed)
       (natp (unquote zero-count-needed))
       (bvcat-nest-with-low-zerosp-axe-aux term (unquote zero-count-needed) dag-array)))

(defund bv-array-write-nest-with-val-at-indexp-axe-aux (term val index dag-array
                                                        calls-remaining ;ensures termination (todo: drop and use mbt instead)
                                                        )
  (declare (xargs :measure (nfix (+ 1 calls-remaining))
                  :hints (("Goal" :in-theory (enable natp))) ;yuck
                  :guard (and (natp calls-remaining)
                              (natp index)
                              (or (myquotep term)
                                  (and (natp term)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term)))))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
  (if (zp calls-remaining)
      nil
    (if (quotep term)
        (let ((val2 (unquote term)))
          (and (true-listp val2)
               (equal val (nth index val2))))
      ;; term is a nodenum:
      (let ((expr (aref1 'dag-array dag-array term)))
        (if (atom expr)
            nil ;it's a var
          (if (fquotep expr)
              (let ((val2 (unquote expr)))
                (and (true-listp val2)
                     (equal val (nth index val2))))
            (let ((fn (ffn-symb expr)))
              (if (not (eq 'bv-array-write fn))
                  nil
                ;; it's a bv-array-write, check that the index is known not to be INDEX
;fixme what if it is index?!
                (and (eql 5 (len (dargs expr)))
                     (let ((index2 (darg3 expr)))
                       (if (and (quotep index2)
                                (not (equal (unquote index2) index)))
                           (bv-array-write-nest-with-val-at-indexp-axe-aux (darg5 expr) val index dag-array (+ -1 calls-remaining))
                         nil)))))))))))

(defund bv-array-write-nest-with-val-at-indexp-axe (term val index dag-array)
  (declare (xargs :guard (and (or (natp index)
                                  (myquotep index))
                              (or (natp val)
                                  (myquotep val))
                              (or (myquotep term)
                                  (and (natp term)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term)))))))
  (and (quotep val)
       (quotep index)
       (natp (unquote index)) ;new, can prevent loops?
       (bv-array-write-nest-with-val-at-indexp-axe-aux term (unquote val) (unquote index) dag-array
                                                       1000000 ;is term a nodenum?  can we use it here?
                                                       )))

;; (defund bv-term-syntaxp (nodenum-or-quotep dag-array)
;;   (declare (xargs :guard (or (myquotep nodenum-or-quotep)
;;                              (and (natp nodenum-or-quotep)
;;                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))))))
;;   (if (consp nodenum-or-quotep)
;;       (natp (unquote nodenum-or-quotep))
;;     (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
;;       (and (consp expr)
;;            (member-eq (ffn-symb expr)
;;                       *operators-whose-size-we-know*)))))

;; ;bbbozo use this all over the place
;; ;term should be a nodenum or quoted constant (is this always the case for the da-syntaxp fns?)
;; ;restricted to the operators we want to trim...
;; (defun term-is-wider-than (width term dag-array)
;;   (if (not (quotep width))
;;       nil
;;     (if (quotep term)
;;         (< (unquote width) (integer-length (unquote term)))
;;       ;; term must be a nodenum, so look it up
;;       (let ((expr (aref1 'dag-array dag-array term)))
;;         (and (consp expr)
;;              (member-eq (car expr) *operators-whose-size-we-know*)
;;              (< (unquote width) (get-type-of-function-call expr)))))))

;; (skip -proofs (verify-guards term-is-wider-than))

;; ;drop?
;; (defun bitxor-terms-should-be-reordered (term1 term2 dag-array)
;;   (declare (ignore dag-array))
;;   (if (quotep term1)
;;       nil ;if the second is a quote too, they would have been xored already
;;     (if (quotep term2)
;;         t
;;       ;;both are nodenums, and the larger nodenums (!) should come first
;;       (< term1 term2))))

;; Returns an alist binding VARNAME to the length of the array term represented
;; byy nodenum-or-quotep, or nil to indicate failure.
(defund bind-bv-array-length-axe (nodenum-or-quotep quoted-varname dag-array)
  (declare (xargs :guard (and ;; (symbolp varname)
                          (or (myquotep nodenum-or-quotep)
                              (and (natp nodenum-or-quotep)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep)))))))
  (if (not (and (myquotep quoted-varname)
                (symbolp (unquote quoted-varname))))
      (er hard? 'bind-bv-array-length-axe "Unexpected varname argument: ~x0." quoted-varname)
    (if (consp nodenum-or-quotep) ;test for quotep
        (let ((val (unquote nodenum-or-quotep))) ;todo: what if length is 0 (may be handled elsewhere)
          (if (all-natp val)
              (acons (unquote quoted-varname) (list 'quote (len val)) nil)
            ;; failure:
            nil))
      ;;otherwise, it's a nodenum:
      (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
        (if (not (consp expr))
            nil ;failure (it's a variable)
          (let ((fn (ffn-symb expr)))
            (if (eq 'quote fn)
                (let ((val (unquote expr)))
                  (if (all-natp val)
                      (acons (unquote quoted-varname) (list 'quote (len val)) nil)
                    nil))
              (if (eq 'bv-array-write fn)
                  (and (eql 5 (len (dargs expr))) ;speed up?
                       (myquotep (second (dargs expr)))
                       (natp (unquote (second (dargs expr))))
                       (acons (unquote quoted-varname) (second (dargs expr)) nil))
                (if (eq 'bv-array-if fn)
                    (and (eql 5 (len (dargs expr))) ;speed up?
                         (myquotep (second (dargs expr)))
                         (natp (unquote (second (dargs expr))))
                         (acons (unquote quoted-varname) (second (dargs expr)) nil))
                  nil)))))))))

;; Returns an alist binding VARNAME to the element width of the array term represented
;; byy nodenum-or-quotep, or nil to indicate failure.
(defund bind-bv-array-element-size-axe (nodenum-or-quotep quoted-varname dag-array)
  (declare (xargs :guard (and ;;(symbolp varname)
                          (or (myquotep nodenum-or-quotep)
                              (and (natp nodenum-or-quotep)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep)))))))
  (if (not (and (myquotep quoted-varname)
                (symbolp (unquote quoted-varname))))
      (er hard? 'bind-bv-array-element-size-axe "Unexpected varname argument: ~x0." quoted-varname)
    (if (consp nodenum-or-quotep) ;test for quotep
        (let ((val (unquote nodenum-or-quotep))) ;todo: what if length is 0 (may be handled elsewhere)
          ;; constant array:
          (if (all-natp val)
              (acons (unquote quoted-varname) (list 'quote (width-of-widest-int val)) nil)
            nil))
      ;;otherwise, it's a nodenum:
      (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
        (if (not (consp expr))
            nil ;failure (it's a variable)
          (let ((fn (ffn-symb expr)))
            (if (eq 'quote fn)
                (let ((val (unquote expr)))
                  (if (all-natp val)
                      (acons (unquote quoted-varname) (list 'quote (width-of-widest-int val)) nil)
                    nil))
              (if (eq 'bv-array-write fn)
                  (and (eql 5 (len (dargs expr))) ;speed up?
                       (myquotep (first (dargs expr)))
                       (natp (unquote (first (dargs expr))))
                       (acons (unquote quoted-varname) (first (dargs expr)) nil))
                (if (eq 'bv-array-if fn)
                    (and (eql 5 (len (dargs expr))) ;speed up?
                         (myquotep (first (dargs expr)))
                         (natp (unquote (first (dargs expr))))
                         (acons (unquote quoted-varname) (first (dargs expr)) nil))
                  nil)))))))))

;; Tests that DARG points to a call of one of the *functions-convertible-to-bv*
;; but not one of the exclude-fns.  No guard on exclude-fns because the caller
;; cannot easily establish it.
(defund term-should-be-converted-to-bvp (darg exclude-fns dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg)))))))
  (and (not (consp darg)) ; test for nodenum
       (let ((expr (aref1 'dag-array dag-array darg)))
         (and (consp expr)
              (let ((fn (ffn-symb expr)))
                (and (member-eq fn *functions-convertible-to-bv*)
                     (let ((exclude-fns (unquote-if-possible exclude-fns)))
                       (if exclude-fns
                           (and (true-listp exclude-fns) ; for guards
                                (not (member-eq fn exclude-fns)))
                         t))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This can be used to decide which functions to open.
;; But to decide whether we can translate an expression, more checking is needed.
;; todo: add sbvdiv sbvrem bvdiv bvmod ?  also excludes repeatbit
;instead of using this, check the args, etc.?
;fffixme add bvdiv and bvmod and sbvdiv and sbvrem !!
;; todo: add bve and sbvle?
(defconst *bv-and-array-fns-we-can-translate*
  '(not
    booland boolor ;boolxor
    boolif
    bitnot
    bitand bitor bitxor
    bvchop bvnot bvuminus
    getbit
    slice
    bvand bvor bvxor
    bvplus bvminus bvmult
    bvdiv bvmod
    sbvdiv sbvrem
    bvlt bvle
    sbvlt sbvle
    bvcat
    bvsx
    bvif
    leftrotate32
    bv-array-read
    bv-array-write
    equal))
