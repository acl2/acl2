; Syntactic utilities for bit-vector terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/myquotep" :dir :system) ;reduce?

;;TODO: Add support here for the rotate ops: leftrotate32 rightrotate32 leftrotate rightrotate.

;; Many BV operators, such as BVXOR and BVPLUS, can be trimmed in the sense
;; that if we are chopping their result we can also chop their arguments
;; without affecting the (chopped) result.

;ffixme add binary-+, unary--, myif, etc.?
;todo: what about myif when bv branches?
(defconst *trimmable-non-arithmetic-operators*  ; rename to *trimmable-non-arithmetic-bv-operators* ?
  '(
    ;; getbit ; would we ever need to trim a getbit?
    ;; bitxor bitnot bitand bitor  ;could we really trim a one-bit operator?
    ;; bool-to-bit ;todo: think about this
    bvnot bvand bvor bvxor
    bvif
    bvchop
    slice
    bvcat
    ;;bv-array-read - trimming array reads seemed bad.  a trimmed array read won't have the same value on test cases as the nth of the corresponding arguments (which will be wider).  Also, if we have a lemma about (bv-array-read 32 80 index <some-function>) but the read is trimmed to less than 32 bits the lemma wont fire on the trimmed read (could get around this if we had bind-free-from-rules) - ffixme maybe we do want to trim reads of constant arrays?
    bvsx ;trying
    repeatbit))

;; These are separate because we trim them less often (perhaps because
;; bit-blasting them is less nice, or because slice does not nicely distribute
;; over them):
(defconst *trimmable-arithmetic-operators* ; rename to *trimmable-arithmetic-bv-operators* ?
  '(bvplus bvmult bvminus bvuminus))

(defconst *trimmable-operators*
  (append *trimmable-arithmetic-operators*
          *trimmable-non-arithmetic-operators*))

;; ;these don't have nice trim rules (think more, esp about bvmod)
;; (defconst *non-trimmable-bv-operators*
;;   '(sbvdiv sbvrem
;;     bvdiv bvmod
;;     bv-array-read ;added since we are not trimming reads any more ; todo: this is not even a bv opoerator
;;     ;; todo: add bvshr?
;;     ))

; are these only bv operators?
;rename to *bv-operators* ?
;; todo: this is missing the following: getbit bitor bitand bitxor bitnot leftrotate32
;; (defconst *operators-whose-size-we-know*
;;   (append *trimmable-operators*
;;           *non-trimmable-bv-operators*))

;TODO: Could make a faster version restricted to trimmable terms?
;TODO: Compare to get-type-of-bv-function-call.
;; Returns a natural number, or nil.
(defun bv-term-size (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      nil
    (let ((fn (ffn-symb term)))
      (case fn
        (quote (if (natp (unquote term))
                   (integer-length (unquote term))
                 nil))
        ;; operators that always have size 1:
        ((getbit bitxor bitnot bitand bitor bool-to-bit)
         1)
        ;; normal operators whose size is the first argument:
        ((bvxor bvand bvor bvnot bvif
                bvchop ;$inline
                bvplus bvmult bvminus bvuminus
                bvdiv bvmod
                bv-array-read ;new
                bvsx
                repeatbit
                bvshl
                ;; bvshr ; could uncomment ; not trimmable though
                )
         (let ((size-arg (farg1 term)))
           (if (and (quotep size-arg)
                    (natp (unquote size-arg)))
               (unquote size-arg)
             nil)))
        (slice (if (and (quotep (farg1 term))
                        (quotep (farg2 term))
                        (natp (unquote (farg1 term)))
                        (natp (unquote (farg2 term)))
                        ;; low <= high
                        (<= (unquote (farg2 term))
                            (unquote (farg1 term))))
                   (+ 1
                      (- (unquote (farg1 term))
                         (unquote (farg2 term))))
                 nil))
        (bvcat (if (and (quotep (farg1 term))
                        (quotep (farg3 term))
                        (natp (unquote (farg1 term)))
                        (natp (unquote (farg3 term))))
                   (+ (unquote (farg1 term))
                      (unquote (farg3 term)))
                 nil))
        ;; todo: drop this case?
        (myif (let ((arg2size (bv-term-size (farg2 term)))
                    (arg3size (bv-term-size (farg3 term))))
                (if (equal arg2size arg3size)
                    arg2size
                  nil)))
        (otherwise nil)))))

;; just to check:
(thm
 (or (natp (bv-term-size term))
     (null (bv-term-size term))))

;; Returns an alist binding VAR to the size of TERM, or nil to indicate failure.
(defun bind-var-to-bv-term-size (var term)
  (declare (xargs :guard (pseudo-termp term)))
  (let ((size (bv-term-size term)))
    (if (natp size)
        (acons var
               (list 'quote size) ;todo: don't re-quote here given that bv-term-size unquotes
               nil)
      nil)))

;use this more?
;speed this up?
;todo: make a version restricted to non-arithmetic ops?
(defun bind-var-to-bv-term-size-if-trimmable (var-name term)
  (declare (xargs :guard (and (symbolp var-name)
                              (pseudo-termp term))))
  (if (atom term)
      nil
    (if (or (quotep term)
            (member-eq (ffn-symb term) *trimmable-operators*))
        (bind-var-to-bv-term-size var-name term)
      nil)))

(defund term-should-be-trimmed-helper (width term operators)
  (declare (xargs :guard (and (natp width)
                              (pseudo-termp term)
                              (member-eq operators '(:all :non-arithmetic)))))
  (if (quotep term)
      (or (not (natp (unquote term)))
          ;;(< width (integer-length (unquote term)))
          (<= (expt 2 width) (unquote term)) ;this may be faster, since expt may be built in (maybe just a shift)?
          )
    (and (consp term)
         (or (member-eq (ffn-symb term)
                        (if (eq :all operators)
                            *trimmable-operators*
                          *trimmable-non-arithmetic-operators*))
;trimming a read from a constant array can turn a single read operation into many (one for each bit)
;but do we need the trimming to use the rules that find patterns in array values?
;maybe we should trim iff we are using getbit-of-bv-array-read?
             ;;                    ;fixme this may be a bad idea?
             ;;                    (and (eq 'bv-array-read (ffn-symb term))
             ;;                         (quotep (farg4 term)))
             )
         (let ((size (bv-term-size term)))
           (and (natp size)
                (< width size))))))

;TODO: Does this functionality already exist?
;OPERATORS should be ':all or ':non-arithmetic
;maybe we should add the option to not trim logical ops?  but that's not as dangerous as trimming arithmetic ops...
;; not used much
(defund term-should-be-trimmed (quoted-width term operators)
  (declare (xargs :guard (and (myquotep quoted-width)
                              (natp (unquote quoted-width))
                              (pseudo-termp term)
                              (member-eq operators '(:all :non-arithmetic)))))
  (if (not (quotep quoted-width)) ;check natp or posp?
      nil                         ;; warning or error?
    (let ((width (unquote quoted-width)))
      (term-should-be-trimmed-helper width term operators))))

;; WARNING: Keep this in sync with the rules in convert-to-bv-rules.lisp.
;; TODO: Consider adding IF and then getting rid of the rules that introduce BVIF
(defconst *functions-convertible-to-bv*
  '(binary-logand
    binary-logior
    binary-logxor
    lognot
    ;; logext ; todo: uncomment?
    binary-+
    unary--
    binary-*))
