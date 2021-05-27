; Syntactic utilities for bit-vector terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system) ;reduce?

;;TODO: Add support here for the rotate ops: leftrotate32 rightrotate32 leftrotate rightrotate.  bvnth?

;; Some BV operators, such as BVXOR and BVPLUS, can be trimmed in the sense
;; that if we are chopping their result we can also chop their arguments
;; without affecting the (chopped) result.

;ffixme add binary-+, unary--, myif, etc.?
;todo: what about myif when bv branches?
(defconst *trimmable-non-arithmetic-operators*
  '( ;;
    getbit
    bitxor bitnot bitand bitor  ;could we really trim a one-bit operator?
    bool-to-bit ;todo: think about this
    bvxor bvand bvor bvnot bvif
    bvchop ;$inline
    slice
    bvcat
    ;;bv-array-read - trimming array reads seemed bad.  a trimmed array read won't have the same value on test cases as the nth of the corresponding arguments (which will be wider).  Also, if we have a lemma about (bv-array-read 32 80 index <some-function>) but the read is trimmed to less than 32 bits the lemma wont fire on the trimmed read (could get around this if we had bind-free-from-rules) - ffixme maybe we do want to trim reads of constant arrays?
;bvplus bvminus bvmult ;leaving these off, since the bvchop of blah rules may not always be on...
    bvsx ;trying
    repeatbit))

(defconst *trimmable-arithmetic-operators*
  '(bvplus bvmult bvminus bvuminus))

;TODO: Ensure we have trim rules for all of these
(defconst *trimmable-operators*
  (append *trimmable-arithmetic-operators*
          *trimmable-non-arithmetic-operators*))

;these don't have nice trim rules (think more, esp about bvmod)
(defconst *non-trimmable-bv-operators*
  '( ;;
    sbvdiv sbvrem
    bvdiv bvmod
    bv-array-read ;added since we are not trimming reads any more
    ))

;keep this up-to-date!
;fixme are these only bv operators?
;rename to *bv-operatros*
(defconst *operators-whose-size-we-know*
  (append *trimmable-operators*
          *non-trimmable-bv-operators*))

;BOZO could drop the fixes if we had a better guard (saying all quoted indices
;in RTL terms are integers)
;TODO: Could make a faster version restricted to trimmable terms?
;TODO: Compare to get-type-of-bv-expr-axe.
(defun unsigned-term-size (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;must be a variable
      nil
    (if (quotep term)
        (if (natp (unquote term))
            (integer-length (unquote term))
          nil)
      (if (member-eq (ffn-symb term) '(getbit bitxor bitnot bitand bitor bool-to-bit))
          1
        (if (member-eq (ffn-symb term) '(bvxor bvand bvor bvnot bvif
                                               bvchop ;$inline
                                               bvplus bvmult bvminus bvuminus
                                               bvdiv bvmod
                                               bv-array-read ;new
                                               bvsx
                                               repeatbit
                                               ))
            (if (quotep (farg1 term))
                (unquote (farg1 term))
              nil)
;BOZO move this case down -- or remove it?
          (if (eq (ffn-symb term) 'myif)
              (let ((arg2size (unsigned-term-size (farg2 term)))
                    (arg3size (unsigned-term-size (farg3 term))))
                (if (equal arg2size arg3size)
                    arg2size
                  nil))
            (if (eq (ffn-symb term) 'slice)
                (if (and (quotep (farg1 term))
                         (quotep (farg2 term)))
                    (+ 1
                       (- (fix (unquote (farg1 term)))
                          (fix (unquote (farg2 term)))))
                  nil)
              (if (eq (ffn-symb term) 'bvcat)
                  (if (and (quotep (farg1 term))
                           (quotep (farg3 term)))
                      (+ (fix (unquote (farg1 term)))
                         (fix (unquote (farg3 term))))
                    nil)
                nil))))))))

;todo: rename unsigned-term -> bv
(defun bind-var-to-unsigned-term-size (var term)
  (declare (xargs :guard (pseudo-termp term)))
  (let ((size (unsigned-term-size term)))
    (if (natp size)
        (acons var
               (list 'quote size) ;todo: don't re-quote here given that unsigned-term-size unquotes
               nil)
      nil)))

;fixme use this more?
;speed this up?
;todo: make a version restricted to non-arithmetic ops?
(defun bind-var-to-unsigned-term-size-if-trimmable (var-name term)
  (declare (xargs :guard (and (symbolp var-name)
                              (pseudo-termp term))))
  (if (atom term)
      nil
    (if (or (quotep term)
            (member-eq (ffn-symb term) *trimmable-operators*))
        (bind-var-to-unsigned-term-size var-name term)
      nil)))

(defund term-should-be-trimmed2-helper (width term operators)
  (declare (xargs :guard (and (natp width)
                              (pseudo-termp term)
                              (member-eq operators '(all non-arithmetic)))))
  (if (quotep term)
      (or (not (natp (unquote term)))
          ;;(< width (integer-length (unquote term)))
          (<= (expt 2 width) (unquote term)) ;this may be faster, since expt may be built in (maybe just a shift)?
          )
    ;; term must be a nodenum, so look it up
    (and (consp term)
         (or (member-eq (ffn-symb term)
                        (if (eq 'all operators) ;TODO: Use :all instead?
                            *trimmable-operators*
                          *trimmable-non-arithmetic-operators*))
;trimming a read from a constant array can turn a single read operation into many (one for each bit)
;but do we need the trimming to use the rules that find patterns in array values?
;maybe we should trim iff we are using getbit-of-bv-array-read?

             ;;                    ;fixme this may be a bad idea?
             ;;                    (and (eq 'bv-array-read (ffn-symb term))
             ;;                         (quotep (farg4 term)))
             )
         (let ((size (unsigned-term-size term)))
           (and (natp size)
                (< width size))))))

;TODO: Does this functionality already exist?
;OPERATORS should be 'all or 'non-arithmetic
;maybe we should add the option to not trim logical ops?  but that's not as dangerous as trimming arithmetic ops...
(defund term-should-be-trimmed2 (quoted-width term operators)
  (declare (xargs :guard (and (myquotep quoted-width)
                              (natp (unquote quoted-width))
                              (pseudo-termp term)
                              (member-eq operators '(all non-arithmetic)))))
  (if (not (quotep quoted-width)) ;check natp or posp?
      nil                         ;; warning or error?
    (let ((width (unquote quoted-width)))
      (term-should-be-trimmed2-helper width term operators))))
