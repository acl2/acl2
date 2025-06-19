; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "../definition/lexer")

(include-book "projects/abnf/tree-utilities" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tools to test the ACL2 lexer of Leo.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Our lexing (and parsing) testing tools take inputs that are
; either lists of natural numbers that are Unicode code points,
; or ACL2 strings that represent lists of ISO 8851-1 characters.
; We use the following function
; to convert the latter to the corresponding Unicode code points
; and to leave the former unchanged.
; The purpose is so that we can pass to the testing tools
; either lists of Unicode points or strings:
; the testing tools call this function
; to normalize the input to a list of Unicode code points.

; Note, entering strings in Emacs UTF-8 buffers
; yields char-code values appropriate for UTF-8,
; even though ACL2 prefers to interpret the codes as
; ISO 8851-1 characters.

;; Observation: since a leo source file is UTF-8,
;; the code points will all be scalar values.
;; So it should be correct to use acl2::ustring? to check them.

(define input-to-unicode-points (input)
  :guard (or (stringp input)
             (nat-listp input))
  :returns (nats nat-listp :hyp :guard)
  (b* (((when (acl2::ustring? input))
        input)
       ((when (nat-listp input))
        ;; if a nat is not a unicode scalar value,
        ;; just return a single illegal nat to indicate error
        '(#x110000)))
    (if (stringp input)
        (b* ((octets (string=>nats input))
             ((unless (unsigned-byte-listp 8 octets))
              '(#x110000))
             (codepoints (acl2::utf8=>ustring octets))
             ((unless (acl2::ustring? codepoints))
              '(#x110000))
             ((unless (nat-listp codepoints))
              '(#x110000)))
          codepoints)
      ;; don't know what input is... just return it
      input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that using lex-fn to lex (append input1 input2)
; consumes input1,
; returns a CST with rulename as root,
; and returns input2 as remaining input.

(defmacro test-lex (lex-fn rulename input1 input2)
  `(assert-event
    (b* (;; bind the-input up front so that if a test fails,
         ;; we can see which test it is rather than having it elided
         (the-input ,input1)
         (input1 (input-to-unicode-points the-input))
         (input2 (input-to-unicode-points ,input2))
         (input (append input1 input2))
         ((mv tree rest-input) (,lex-fn input)))
      (and (abnf-tree-with-root-p tree ,rulename)
           (equal (abnf::tree->string tree) input1)
           (equal rest-input input2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that using lex-token to lex (append input1 input2)
; consumes input1,
; returns a CST with "token" as root and rulename as the sub,
; and returns input2 as remaining input.

(defmacro test-lex-token (sub-rulename input1 input2)
  `(assert-event
    (b* (;; bind the-input up front so that if a test fails,
         ;; we can see which test it is rather than having it elided
         (the-input ,input1)
         (input1 (input-to-unicode-points the-input))
         (input2 (input-to-unicode-points ,input2))
         (input (append input1 input2))
         ((mv tree rest-input) (lex-token input)))
      (and (abnf-tree-with-root-p tree "token")
           (equal (abnf::tree->string tree) input1)
           (let ((subtree (abnf::check-tree-nonleaf-1-1 tree "token")))
             (and subtree
                  (abnf-tree-with-root-p subtree ,sub-rulename)
                  (equal (abnf::tree->string subtree) input1)))
           (equal rest-input input2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that lexing whitespace in (append input1 input2)
; consumes input1,
; returns a whitespace CST,
; and returns input2 as remaining input.

(defmacro test-lex-whitespace (input1 input2)
  `(test-lex lex-whitespace "whitespace" ,input1 ,input2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that lexing a comment in (append input1 input2)
; consumes input1,
; returns a comment CST,
; and returns input2 as remaining input.

(defmacro test-lex-comment (input1 input2)
  `(test-lex lex-comment "comment" ,input1 ,input2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lex a construct in full,
; i.e. ensuring that all the input is consumed.
; Return the CST if successful.

(defmacro lex-full (lex-fn input)
  `(b* ((input (input-to-unicode-points ,input))
        (__function__ 'lex-full)
        ((mv tree rest) (,lex-fn input))
        ((when (reserrp tree)) tree)
        ((when rest) (reserrf (list :extra-input rest))))
     tree))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that using lex-fn to lex (append input1 input2)
; consumes input1,
; returns a CST with rulename as root,
; and returns input2 as remaining input.

;; EXPECTED should be either :SUCCEED or :FAIL, depending
;; on whether the string is expected to be lexemizable.
(defmacro test-lexemize-string (input-string-in-utf8 expected)
  `(assert-event
    (b* ((cst (lexemize-leo-from-string ,input-string-in-utf8))
         ((when (eq ,expected :FAIL))
          (reserrp cst))
         ((unless (eq ,expected :SUCCEED))
          (prog2$ (cw "test-lexemize-string 2nd argument must be :FAIL or :SUCCEED~%")
                  nil)))
      (and (not (reserrp cst))
           (abnf::tree-listp cst)
           (equal (abnf::tree-list->string cst)
                  (input-to-unicode-points ,input-string-in-utf8))))))
