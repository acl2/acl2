; BV-related syntactic tests
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

;; This book contains bit-vector-related functions that support Axe
;; rules that call axe-syntaxp and axe-bind-free.

(include-book "std/util/bstar" :dir :system)
(include-book "axe-types") ;reduce?  we just need the bv and bv-array stuff
(include-book "dag-arrays")
(include-book "kestrel/bv/bv-syntax" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(local (in-theory (enable car-becomes-nth-of-0
                          integerp-of-nth-when-darg-listp
                          not-cddr-of-nth-when-darg-listp
                          consp-of-cdr-of-nth-when-darg-listp
                          equal-of-quote-and-nth-0-of-nth-when-darg-listp
                          symbolp-of-nth-0-when-dag-exprp
                          dargp-of-nth-when-darg-listp)))

;; Returns a bv-typep, or nil (if we could not determine a type).
;the args are nodenums or quoteps - we don't deref nodenums that may point to quoteps
;what if the number of arguments is wrong?
;; NOTE: Soundness depends on this since it is used in the STP translation.
(defund maybe-get-type-of-bv-function-call (fn dargs)
  (declare (xargs :guard (and (symbolp fn)
                              (darg-listp dargs))))
  (case fn
    ;; Single-bit functions:
    ((getbit bitxor bitand bitor bitnot bool-to-bit)
      ;see unsigned-byte-p-1-of-bitxor, etc.:
     (make-bv-type 1))
    ;; Functions whose type is indicated by the first argument:
    ((bvchop ;$inline
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
      bvshr)
     (and (consp dargs)
          (let ((width (first dargs)))
            (and (darg-quoted-natp width)
                 (make-bv-type (unquote width))))))
    ;; 32-bit operations:
    ((leftrotate32 rightrotate32)  ;eventually drop?
     ;;see unsigned-byte-p-32-of-leftrotate32 and unsigned-byte-p-32-of-rightrotate32:
     (make-bv-type 32))
    ;; (slice high low x):
    (slice
     (let ((high-darg (first dargs))
           (low-darg (second dargs)))
       (and (consp high-darg) ; checks for quoted constant
            (consp low-darg) ; checks for quoted constant
            (let ((high (unquote high-darg))
                  (low (unquote low-darg)))
              (and (natp high)
                   (natp low)
                   (<= low high)
                   (make-bv-type (+ 1 high (- low))))))))
    ;; (bvcat highsize highval lowsize lowval):
    (bvcat
     (let ((high-size-darg (first dargs))
           (low-size-darg (third dargs)))
       (and (consp high-size-darg) ; checks for quoted constant
            (consp low-size-darg) ; checks for quoted constant
            (let ((high-size (unquote high-size-darg))
                  (low-size (unquote low-size-darg)))
              (and (natp high-size)
                   (natp low-size)
                   (make-bv-type (+ high-size low-size)))))))
    ;; Unknown function, can't find a BV size:
    (otherwise nil)))

(defthm maybe-get-type-of-bv-function-call-type
  (or (null (maybe-get-type-of-bv-function-call fn dargs))
      (natp (maybe-get-type-of-bv-function-call fn dargs)))
  :rule-classes :type-prescription
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

;; quoted-varname is a darg, but we expect it to always be a constant (a quoted symbol)
;; Returns an alist with one binding that binds the unquoted varname to VAL.
;; TODO: Use this more.
(defun bind-unquoted-varname (quoted-varname val)
  (declare (xargs :guard (or (myquotep quoted-varname)
                             (natp quoted-varname))))
  (mv-let (erp sym)
    (if (consp quoted-varname) ; checks for quotep
        (let ((sym (unquote quoted-varname)))
          (if (symbolp sym)
              (mv nil sym)
            (mv t nil)))
      (mv t nil))
    (if erp
        (er hard? 'bind-unquoted-varname "Unexpected varname argument: ~x0." quoted-varname)
      (acons sym val nil))))

;returns an alist that binds VARNAME to the size of the nodenum-or-quotep, if it is a bit vector with a statically known size, or nil to indicate failure.
;bozo redo to support different sets of operators <- ??
;todo: can we save adding a quote to the returned size?
;; todo: consider an option to not count constants as BV terms in this sense
(defund bind-bv-size-axe (darg quoted-varname dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (or (myquotep quoted-varname)
                                  (and (natp quoted-varname)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-varname)))))))
  (if (consp darg) ;test for quotep
      (let ((val (unquote darg)))
        (if (natp val)
            (bind-unquoted-varname quoted-varname (list 'quote (integer-length val)))
            ;; failure (may be a constant array or a negative number or something else):
          nil))
    ;; darg is a nodenum:
    (let ((expr (aref1 'dag-array dag-array darg)))
      (if (not (consp expr))
          nil ;; fail (can't tell the bv size of a variable)
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn)
              (let ((val (unquote expr)))
                (if (natp val)
                    (bind-unquoted-varname quoted-varname (list 'quote (integer-length val)))
                  ;; failure (may be a constant array or a negative or something else):
                  nil))
            (let ((type (maybe-get-type-of-bv-function-call fn (dargs expr))))
              (if type
                  (bind-unquoted-varname quoted-varname (list 'quote (bv-type-width type))) ;todo: could often save this quote since in many operators the size is already quoted.  would need a function that can return the quoted type
                ;;failure:
                nil))))))))

;; Sanity check (some rules may rely on the size being a constant):
;; If there is no error, we get a singleton alist that binds the varname to a
;; quoted natural representing the size:
(thm
  (let ((alist (bind-bv-size-axe darg quoted-varname dag-array)))
    (implies alist
             (and (alistp alist)
                  (= 1 (len alist))
                  (eq (unquote quoted-varname) (car (first alist)))
                  (quotep (cdr (first alist)))
                  (natp (unquote (cdr (first alist)))))))
  :hints (("Goal" :in-theory (enable bind-bv-size-axe))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: inline?
(defund term-should-be-trimmed-axe-helper (width darg operators dag-array)
  (declare (xargs :guard (and (natp width)
                              ;; (member-eq operators '(all non-arithmetic)) ; todo: make these keywords
                              (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))))
           (type (integer 0 *) width))
  (if (consp darg) ; checks for quotep
      (let ((val (unquote darg)))
        (or (not (natp val)) ; not a natp (unusual), so we will trim
            ;;(< width (integer-length (unquote darg)))
            (<= (expt 2 width) (the (integer 0 *) val)) ;this may be faster, since expt may be built in (maybe just a shift)?
            ))
    ;; darg must be a nodenum, so look it up
    (let ((expr (aref1 'dag-array dag-array darg)))
      (and (consp expr) ; we don't trim a var
           (let ((fn (ffn-symb expr)))
             (and ;; The operator is one that we can trim:
               (or (member-eq fn (if (equal ''all operators) ;TODO: Use :all instead? ;; todo: combine this member-eq check with the call of maybe-get-type-of-bv-function-call below
                                     *trimmable-operators*
                                   *trimmable-non-arithmetic-operators*))
;trimming a read from a constant array can turn a single read operation into many (one for each bit)
;but do we need the trimming to use the rules that find patterns in array values?
;maybe we should trim iff we are using getbit-of-bv-array-read?

                   ;;                    ;fixme this may be a bad idea?
                   ;;                    (and (eq 'bv-array-read (ffn-symb expr))
                   ;;                         (quotep (darg4 expr)))
                   )
               ;; The width of the term is greater than the desired width:
               (let ((type (maybe-get-type-of-bv-function-call fn (dargs expr))))
                 (and type
                      (< width (the (integer 0 *) (bv-type-width type)))))))))))

;; Decides whether the term indicated by DARG can be trimmed down (by wrapping it with a call of
;; trim) to be a bit-vector of the given WIDTH.
;maybe we should add the option to not trim logical ops?  but that's not as dangerous as trimming arithmetic ops...
;; todo: warn if size-darg is not a quoted natural
(defund term-should-be-trimmed-axe (size-darg
                                    darg
                                    operators ;expected to be a quoted constant in every call, either 'all or 'non-arithmetic
                                    dag-array)
  (declare (xargs :guard (and (or (myquotep size-darg)
                                  (and (natp size-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 size-darg))))
                              (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              ;; (member-equal operators '('all 'non-arithmetic))
                              )))
  (b* (;; ((when (not (member-equal operators '('all 'non-arithmetic)))) ;; todo: can we avoid this?  use one as the default? use keywords?
       ;;  (er hard? 'term-should-be-trimmed-axe "Unexpected operators argument: ~x0.)~%" operators))
       ((when (not (consp size-darg))) ; checks for non-constant size
        ;; can probably happen, if non-constant sizes are around:
        nil
        ;; When variable shifts are involved, we may indeed see BV sizes that are not constants:
        ;; (cw "Warning: In term-should-be-trimmed-axe: Unexpected width: ~x0.)~%"
        ;;     (if (consp size-darg) ; check for quotep
        ;;         size-darg
        ;;       ;; simplify this?:
        ;;       (if (and (not (myquotep darg))
        ;;                (natp size-darg)
        ;;                (< size-darg (alen1 'dag-array dag-array)))
        ;;           (aref1 'dag-array dag-array size-darg)
        ;;         :unknown)))
        )
       (size (unquote size-darg))
       ((when (not (natp size)))
        ;; this case may be quite common (see rules like bvcat-trim-arg2-axe-all, which we saw used with highsize = '-256 !)
        nil
        ;;(er hard? 'term-should-be-trimmed-axe "Unexpected desired width, ~x0, for ~x1.)~%" size-darg darg)
        ))
    (term-should-be-trimmed-axe-helper size darg operators dag-array)))

;for (slice 7 0 x) the relevant width to consider is 8, not 7.  likewise for (getbit 7 x).
;todo: this one takes the high bit, not the width.  rename this function and that param
(defund term-should-be-trimmed-axe-plus-one (top-bit-darg
                                             darg
                                             operators ;expected to be a quoted constant in every call
                                             dag-array)
  (declare (xargs :guard (and (or (myquotep top-bit-darg)
                                  (and (natp top-bit-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 top-bit-darg))))
                              (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              ;; (member-equal operators '('all 'non-arithmetic))
                              )))
  (b* (;; ((when (not (member-equal operators '('all 'non-arithmetic)))) ;; todo: can we avoid this?  use one as the default? use keywords?
       ;;  (er hard? 'term-should-be-trimmed-axe "Unexpected operators argument: ~x0.)~%" operators))
       ((when (not (consp top-bit-darg))) ; checks for quotep
        nil)
       (top-bit (unquote top-bit-darg))
       ((when (not (natp top-bit)))
        ;; may happen?; see comment in term-should-be-trimmed-axe:
        nil)
       (width (+ 1 (the (integer 0 *) top-bit)))) ;the plus one is for this version
    (term-should-be-trimmed-axe-helper width darg operators dag-array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;BOZO for what other terms is it syntactically evident that they have low zeros?
;termination depends on dag property?
(defund bvcat-nest-with-low-zerosp-axe-aux (darg zero-count-needed dag-array)
  (declare (xargs :guard (and (natp zero-count-needed)
                              (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg)))))
                  :measure (if (quotep darg)
                               0
                             (+ 1 (nfix darg)))
;                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :guard-hints (("Goal" :in-theory (enable cadr-becomes-nth-of-1)))))
  (if (or (quotep darg)
          (not (mbt (natp darg)))) ;for termination
      (equal (unquote darg) 0) ;bozo think about when the constant isn't wrapped in any bvcats
    ;;it's a nodenum, so look it up:
    (let* ((expr (aref1 'dag-array dag-array darg)))
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
                                      (and (< (darg4 expr) darg)
                                           (natp (darg4 expr)))))
                             (bvcat-nest-with-low-zerosp-axe-aux (darg4 expr) zero-count-needed dag-array)))))))))))

(defund bvcat-nest-with-low-zerosp-axe (darg quoted-zero-count-needed dag-array)
  (declare (xargs :guard (or (myquotep darg)
                             (and (natp darg)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))))
  (and (myquotep quoted-zero-count-needed)
       (natp (unquote quoted-zero-count-needed))
       (bvcat-nest-with-low-zerosp-axe-aux darg (unquote quoted-zero-count-needed) dag-array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Binds the varname to the size of the low zeros part of the bvcat nest (which
;; we assume is associated to the right), or returns nil to indicate failure.
(defund bind-low-zero-count-in-bvcat-nest (darg quoted-varname dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (or (myquotep quoted-varname)
                                  (and (natp quoted-varname)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-varname)))))
                  :measure (if (quotep darg)
                               0
                             (+ 1 (nfix darg)))
;                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :guard-hints (("Goal" :in-theory (enable cadr-becomes-nth-of-1 acl2-numberp-when-natp)))
                  ))
  (if (or (consp darg) ; checks for quoted constant
          (not (mbt (natp darg)))) ;for termination
      nil ;failed to find a bvcat nest
    ;; darg is a nodenum, so look it up:
    (let* ((expr (aref1 'dag-array dag-array darg)))
      (if (atom expr) ;check for variable
          nil ; failed to find a bvcat nest
        (and (eq 'bvcat (ffn-symb expr)) ; (bvcat highsize highval lowsize lowval)
             (= 4 (len (dargs expr))) ; drop or optimize?
             (let ((lowval (darg4 expr)))
               (if (consp lowval) ; checks for quoted constant
                   (if (not (eql 0 (unquote lowval)))
                       nil ; fail (there's a constant but it's not 0)
                     (let ((lowsize (darg3 expr)))
                       (if (and (consp lowsize) ; checks for quoted constant
                                (posp (unquote lowsize)) ; could allow 0 I guess
                                )
                           ;; we've found the pattern we are looking for:
                           (if (not (and (consp quoted-varname) ; checks for quoted constant
                                         (symbolp (unquote quoted-varname))))
                               (er hard? 'bind-low-zero-count-in-bvcat-nest "Unexpected varname argument: ~x0." quoted-varname)
                             (acons (unquote quoted-varname) lowsize nil))
                         nil ;fail
                         )))
                 ;; lowval is a nodenum, so examine it:
                 (and (mbt (or (quotep lowval) ;for termination
                               (and (< lowval darg)
                                    (natp lowval))))
                      (bind-low-zero-count-in-bvcat-nest lowval quoted-varname dag-array)))))))))

(defthmd symbol-alistp-of-bind-low-zero-count-in-bvcat-nest
  (symbol-alistp (bind-low-zero-count-in-bvcat-nest darg quoted-varname dag-array))
  :hints (("Goal" :in-theory (enable bind-low-zero-count-in-bvcat-nest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *functions-convertible-to-bv-axe*
  ;; Axe does not split IFs, unlike ACL2:
  ;; todo: now get rid of the rules that introduce BVIF
  (cons 'if *functions-convertible-to-bv*))

;; Tests that DARG points to a call of one of the *functions-convertible-to-bv*
;; but not one of the EXCLUDE-FNS.
(defund term-should-be-converted-to-bvp (darg exclude-fns dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (or (myquotep exclude-fns) ; should always be true
                                  (and (natp exclude-fns)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 exclude-fns)))))))
  (and (not (consp darg)) ; test for nodenum
       (let ((expr (aref1 'dag-array dag-array darg)))
         (and (consp expr)
              (let ((fn (ffn-symb expr)))
                (and (member-eq fn *functions-convertible-to-bv*)
                     (if (and (quotep exclude-fns)
                              (symbol-listp (unquote exclude-fns)))
                         (not (member-eq fn (unquote exclude-fns)))
                       (er hard? 'term-should-be-converted-to-bvp "Bad exclude-fns: ~x0." exclude-fns))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This can be used to decide which functions to open.
;; But to decide whether we can translate an expression, more checking is needed.
;; todo: add  repeatbit?
;instead of using this, check the args, etc.?
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
;; (defthmd car-when-nth-0-constant
;;   (implies (and (equal (nth 0 x) k)
;;                 (syntaxp (quotep k)))
;;            (equal (car x)
;;                   k)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bv-array-write-nest-with-val-at-indexp-axe-aux (darg
                                                        val index dag-array
                                                        calls-remaining ;ensures termination (todo: drop and use mbt instead)
                                                        )
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (natp index)
                              (natp calls-remaining))
                  :measure (nfix (+ 1 calls-remaining))
                  :hints (("Goal" :in-theory (enable natp))) ;yuck
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
  (if (zp calls-remaining)
      nil
    (if (quotep darg)
        (let ((val2 (unquote darg)))
          (and (true-listp val2)
               (equal val (nth index val2))))
      ;; darg is a nodenum:
      (let ((expr (aref1 'dag-array dag-array darg)))
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

(defund bv-array-write-nest-with-val-at-indexp-axe (darg val index dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (or (natp val)
                                  (myquotep val))
                              (or (natp index)
                                  (myquotep index)))))
  (and (quotep val)
       (quotep index)
       (natp (unquote index)) ;new, can prevent loops?
       (bv-array-write-nest-with-val-at-indexp-axe-aux darg (unquote val) (unquote index) dag-array
                                                       1000000 ;is darg a nodenum?  can we use it here?
                                                       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;; Returns an alist binding VARNAME to the element width of the array term represented
;; by darg, or nil to indicate failure.
;; We expect quoted-varname to always be a quoted symbol, but we cannot require that in the guard.
(defund bind-bv-array-element-size-axe (darg quoted-varname dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (or (myquotep quoted-varname)
                                  (and (natp quoted-varname)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-varname)))))))
  (if (consp darg) ;test for quotep
      (let ((val (unquote darg))) ;todo: what if length is 0 (may be handled elsewhere)
        ;; constant array:
        (if (nat-listp val)
            (bind-unquoted-varname quoted-varname (list 'quote (width-of-widest-int val)))
          nil))
    ;; otherwise, it's a nodenum:
    (let ((expr (aref1 'dag-array dag-array darg)))
      (if (not (consp expr))
          nil ; failure (it's a variable)
        (let ((fn (ffn-symb expr)))
          (case fn
            (quote (let ((val (unquote expr)))
                     (if (nat-listp val)
                         (bind-unquoted-varname quoted-varname (list 'quote (width-of-widest-int val)))
                       nil)))
            ;; (bv-array-write element-size len index val data)
            ;; (bv-array-if    element-size len test array1 array2)
            ((bv-array-write bv-array-if)
             (let ((element-size-arg (first (dargs expr))))
               (and (consp element-size-arg) ; checks for quotep
                    (natp (unquote element-size-arg))
                    (bind-unquoted-varname quoted-varname element-size-arg))))
            (otherwise nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an alist binding VARNAME to the length of the array term represented
;; by darg, or nil to indicate failure.
;; We expect quoted-varname to always be a quoted symbol, but we cannot require that in the guard.
(defund bind-bv-array-length-axe (darg quoted-varname dag-array)
  (declare (xargs :guard (and (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))
                              (or (myquotep quoted-varname)
                                  (and (natp quoted-varname)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-varname)))))))
  (if (consp darg) ;tests for quotep
      (let ((val (unquote darg))) ;todo: what if length is 0 (may be handled elsewhere)
        (if (nat-listp val)
            (bind-unquoted-varname quoted-varname (list 'quote (len val)))
            ;; failure:
          nil))
      ;;otherwise, it's a nodenum:
    (let ((expr (aref1 'dag-array dag-array darg)))
      (if (not (consp expr))
          nil ;failure (it's a variable)
        (let ((fn (ffn-symb expr)))
          (case fn
            (quote (let ((val (unquote expr)))
                     (if (nat-listp val)
                         (bind-unquoted-varname quoted-varname (list 'quote (len val)))
                       nil)))
            ;; (bv-array-write element-size len index val data)
            ;; (bv-array-if    element-size len test array1 array2)
            ((bv-array-write bv-array-if)
             (let ((len-arg (second (dargs expr))))
               (and (consp len-arg) ; tests for quotep
                    (natp (unquote len-arg))
                    (bind-unquoted-varname quoted-varname len-arg))))
            (otherwise nil)))))))
