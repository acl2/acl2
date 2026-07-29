; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "identifier-syntax")
(include-book "parser")
(include-book "abstract-syntax")

(include-book "kestrel/lists-light/nthcdr" :dir :system)
(include-book "projects/abnf/tree-operations/tree-utilities" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-abstraction
  :parents (abstract-syntax parsing-and-printing)
  :short "Mapping from Futhark IR concrete syntax trees to abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "This layer maps the ABNF concrete syntax trees produced by
     @(see parser) to the FTY abstract syntax in @(see abstract-syntax-trees).")
   (xdoc::p
    "The grammar deliberately uses broad tokens in a few places.  In
     particular, @('word') is used for names, primitive types, array sizes,
     literal-looking words, and miscellaneous IR atoms.  Syntax abstraction is
     where those uses are separated into the corresponding AST fields.")
   (xdoc::p
    "This layer also enforces side conditions that are not expressed directly
     in ABNF, such as rejecting reserved words and literal-looking words as
     names.  String literals are decoded here as well: escape sequences are
     interpreted as Unicode code points, and the resulting content is stored
     in ACL2 strings as UTF-8 bytes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable abnf::treep-when-result-not-error
                    abnf::tree-listp-when-result-not-error
                    abnf::tree-list-listp-when-result-not-error
                    acl2::nat-listp-when-result-not-error
                    abnf::tree-list-tuple2p-when-result-not-error
                    abnf::tree-list-tuple3p-when-result-not-error
                    abnf::tree-list-tuple4p-when-result-not-error
                    abnf::tree-list-tuple5p-when-result-not-error
                    abnf::tree-list-tuple6p-when-result-not-error
                    abnf::tree-list-tuple7p-when-result-not-error
                    abnf::tree-list-tuple8p-when-result-not-error
                    abnf::tree-list-tuple9p-when-result-not-error
                    abnf::tree-list-tuple10p-when-result-not-error
                    fut-typep-when-result-not-error
                    fut-type-listp-when-result-not-error
                    paramp-when-result-not-error
                    param-listp-when-result-not-error
                    exprp-when-result-not-error
                    expr-listp-when-result-not-error
                    stmtp-when-result-not-error
                    stmt-listp-when-result-not-error
                    bodyp-when-result-not-error
                    declp-when-result-not-error
                    decl-listp-when-result-not-error
                    fut-programp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic CST utilities.

(define abs-symbols-to-nats ((syms true-listp))
  :returns (nats nat-listp)
  (cond ((endp syms) nil)
        ((natp (car syms))
         (cons (car syms) (abs-symbols-to-nats (cdr syms))))
        (t (abs-symbols-to-nats (cdr syms)))))

(define tree-text ((tree abnf::treep))
  :returns (text stringp)
  (b* ((text (codepoints=>string
              (abs-symbols-to-nats (abnf::tree->string tree))))
       ((when (reserrp text)) ""))
    text))

(define tree-rulename-p ((tree abnf::treep) (rulename stringp))
  :returns (yes/no booleanp)
  (and (abnf::tree-case tree :nonleaf)
       (equal (abnf::tree-nonleaf->rulename? tree)
              (abnf::rulename rulename))))

(define first-branch ((tree abnf::treep) (rulename stringp))
  :returns (trees abnf::tree-list-resultp)
  (b* (((okf branches)
        (abnf::check-tree-nonleaf tree (str-fix rulename)))
       ((okf branch) (abnf::check-tree-list-list-1 branches)))
    branch))

(define first-direct-rulename ((trees abnf::tree-listp) (rulename stringp))
  :returns (tree abnf::tree-resultp)
  (cond ((endp trees)
         (reserrf (list :missing-direct-child (str-fix rulename))))
        ((tree-rulename-p (car trees) rulename)
         (abnf::tree-fix (car trees)))
        (t (first-direct-rulename (cdr trees) rulename))))

(define optional-first-direct-rulename ((trees abnf::tree-listp)
                                        (rulename stringp))
  :returns (tree? abnf::tree-optionp)
  (b* ((tree (first-direct-rulename trees rulename))
       ((when (reserrp tree)) nil))
    tree))

(local
 (defthm tree-list-count-of-first-branch
   (implies (not (reserrp (first-branch tree rulename)))
            (< (abnf::tree-list-count (first-branch tree rulename))
               (abnf::tree-count tree)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable first-branch)))))

(local
 (defthm tree-count-of-first-direct-rulename
   (implies (not (reserrp (first-direct-rulename trees rulename)))
            (< (abnf::tree-count (first-direct-rulename trees rulename))
               (abnf::tree-list-count trees)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable first-direct-rulename)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Names, literals, and strings.

(define string-lit-content-codepoints ((nats nat-listp))
  :returns (content nat-listp)
  :short "Drop the first and last code point of a string literal fringe."
  :measure (len (nat-list-fix nats))
  :hooks (:fix)
  (b* ((nats (nat-list-fix nats)))
    (cond ((endp nats) nil)
          ((endp (cdr nats)) nil)
          ((endp (cddr nats)) nil)
          (t (cons (cadr nats)
                   (string-lit-content-codepoints (cdr nats)))))))

(define ir-escape-digit-codepointp ((radix natp) (nat natp))
  :returns (yes/no booleanp)
  (b* ((radix (nfix radix))
       (nat (nfix nat)))
    (cond ((eql radix 8)
           (and (<= #x30 nat) (<= nat #x37)))
          ((eql radix 10)
           (and (<= #x30 nat) (<= nat #x39)))
          ((eql radix 16)
           (or (and (<= #x30 nat) (<= nat #x39))
               (and (<= #x41 nat) (<= nat #x46))
               (and (<= #x61 nat) (<= nat #x66))))
          (t nil))))

(define ir-escape-digit-value ((nat natp))
  :returns (value natp)
  (b* ((nat (nfix nat)))
    (cond ((and (<= #x30 nat) (<= nat #x39))
           (- nat #x30))
          ((and (<= #x41 nat) (<= nat #x46))
           (+ 10 (- nat #x41)))
          ((and (<= #x61 nat) (<= nat #x66))
           (+ 10 (- nat #x61)))
          (t 0))))

(define parse-ir-escape-digits-rest ((radix natp)
                                             (input nat-listp)
                                             (acc natp))
  :returns (mv (value natp)
               (rest-input nat-listp))
  :measure (len (nat-list-fix input))
  :hooks nil
  :guard-hints (("Goal" :nonlinearp t))
  (b* ((input (nat-list-fix input))
       ((when (endp input)) (mv (nfix acc) nil))
       (nat (car input))
       ((unless (ir-escape-digit-codepointp radix nat))
        (mv (nfix acc) input))
       (value (nfix (+ (* (nfix radix) (nfix acc))
                       (ir-escape-digit-value nat)))))
    (parse-ir-escape-digits-rest radix (cdr input) value))
  ///

  (defret len-of-parse-ir-escape-digits-rest-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

(define parse-ir-escape-digits ((radix natp) (input nat-listp))
  :returns (mv (matchedp booleanp)
               (value natp)
               (rest-input nat-listp))
  :hooks nil
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv nil 0 nil))
       (nat (car input))
       ((unless (ir-escape-digit-codepointp radix nat))
        (mv nil 0 input))
       ((mv value rest-input)
        (parse-ir-escape-digits-rest
         radix
         (cdr input)
         (ir-escape-digit-value nat))))
    (mv t value rest-input))
  ///

  (defret len-of-parse-ir-escape-digits-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parse-ir-escape-digits)))))

(define match-codepoints ((pattern nat-listp) (input nat-listp))
  :returns (yes/no booleanp)
  (cond ((endp pattern) t)
        ((endp input) nil)
        ((eql (car pattern) (car input))
         (match-codepoints (cdr pattern) (cdr input)))
        (t nil)))

(define decode-ir-ascii-escape ((input nat-listp))
  :returns (mv (matchedp booleanp)
               (code natp)
               (rest-input nat-listp))
  :short "Decode a Haskell-style named ASCII escape after the backslash."
  :hooks (:fix)
  (b* ((input (nat-list-fix input)))
    (cond ((match-codepoints '(#x4E #x55 #x4C) input)
           (mv t #x00 (nthcdr 3 input)))   ; NUL
          ((match-codepoints '(#x53 #x4F #x48) input)
           (mv t #x01 (nthcdr 3 input)))   ; SOH
          ((match-codepoints '(#x53 #x54 #x58) input)
           (mv t #x02 (nthcdr 3 input)))   ; STX
          ((match-codepoints '(#x45 #x54 #x58) input)
           (mv t #x03 (nthcdr 3 input)))   ; ETX
          ((match-codepoints '(#x45 #x4F #x54) input)
           (mv t #x04 (nthcdr 3 input)))   ; EOT
          ((match-codepoints '(#x45 #x4E #x51) input)
           (mv t #x05 (nthcdr 3 input)))   ; ENQ
          ((match-codepoints '(#x41 #x43 #x4B) input)
           (mv t #x06 (nthcdr 3 input)))   ; ACK
          ((match-codepoints '(#x42 #x45 #x4C) input)
           (mv t #x07 (nthcdr 3 input)))   ; BEL
          ((match-codepoints '(#x42 #x53) input)
           (mv t #x08 (nthcdr 2 input)))   ; BS
          ((match-codepoints '(#x48 #x54) input)
           (mv t #x09 (nthcdr 2 input)))   ; HT
          ((match-codepoints '(#x4C #x46) input)
           (mv t #x0A (nthcdr 2 input)))   ; LF
          ((match-codepoints '(#x56 #x54) input)
           (mv t #x0B (nthcdr 2 input)))   ; VT
          ((match-codepoints '(#x46 #x46) input)
           (mv t #x0C (nthcdr 2 input)))   ; FF
          ((match-codepoints '(#x43 #x52) input)
           (mv t #x0D (nthcdr 2 input)))   ; CR
          ((match-codepoints '(#x53 #x4F) input)
           (mv t #x0E (nthcdr 2 input)))   ; SO
          ((match-codepoints '(#x53 #x49) input)
           (mv t #x0F (nthcdr 2 input)))   ; SI
          ((match-codepoints '(#x44 #x4C #x45) input)
           (mv t #x10 (nthcdr 3 input)))   ; DLE
          ((match-codepoints '(#x44 #x43 #x31) input)
           (mv t #x11 (nthcdr 3 input)))   ; DC1
          ((match-codepoints '(#x44 #x43 #x32) input)
           (mv t #x12 (nthcdr 3 input)))   ; DC2
          ((match-codepoints '(#x44 #x43 #x33) input)
           (mv t #x13 (nthcdr 3 input)))   ; DC3
          ((match-codepoints '(#x44 #x43 #x34) input)
           (mv t #x14 (nthcdr 3 input)))   ; DC4
          ((match-codepoints '(#x4E #x41 #x4B) input)
           (mv t #x15 (nthcdr 3 input)))   ; NAK
          ((match-codepoints '(#x53 #x59 #x4E) input)
           (mv t #x16 (nthcdr 3 input)))   ; SYN
          ((match-codepoints '(#x45 #x54 #x42) input)
           (mv t #x17 (nthcdr 3 input)))   ; ETB
          ((match-codepoints '(#x43 #x41 #x4E) input)
           (mv t #x18 (nthcdr 3 input)))   ; CAN
          ((match-codepoints '(#x45 #x53 #x43) input)
           (mv t #x1B (nthcdr 3 input)))   ; ESC
          ((match-codepoints '(#x45 #x4D) input)
           (mv t #x19 (nthcdr 2 input)))   ; EM
          ((match-codepoints '(#x53 #x55 #x42) input)
           (mv t #x1A (nthcdr 3 input)))   ; SUB
          ((match-codepoints '(#x46 #x53) input)
           (mv t #x1C (nthcdr 2 input)))   ; FS
          ((match-codepoints '(#x47 #x53) input)
           (mv t #x1D (nthcdr 2 input)))   ; GS
          ((match-codepoints '(#x52 #x53) input)
           (mv t #x1E (nthcdr 2 input)))   ; RS
          ((match-codepoints '(#x55 #x53) input)
           (mv t #x1F (nthcdr 2 input)))   ; US
          ((match-codepoints '(#x53 #x50) input)
           (mv t #x20 (nthcdr 2 input)))   ; SP
          ((match-codepoints '(#x44 #x45 #x4C) input)
           (mv t #x7F (nthcdr 3 input)))   ; DEL
          (t (mv nil 0 input))))
  ///

  (defret len-of-decode-ir-ascii-escape-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable decode-ir-ascii-escape)))))

(define decode-ir-numeric-escape ((input nat-listp))
  :returns (mv (matchedp booleanp)
               (code natp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((mv decp dec rest) (parse-ir-escape-digits 10 input))
       ((when decp) (mv t dec rest))
       ((when (endp input)) (mv nil 0 nil))
       (nat (car input)))
    (cond ((eql nat #x6F)  ; o
           (b* (((mv matchedp value rest)
                 (parse-ir-escape-digits 8 (cdr input))))
             (mv matchedp value rest)))
          ((eql nat #x78)  ; x
           (b* (((mv matchedp value rest)
                 (parse-ir-escape-digits 16 (cdr input))))
             (mv matchedp value rest)))
          (t (mv nil 0 input))))
  ///

  (defret len-of-decode-ir-numeric-escape-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable decode-ir-numeric-escape)))))

(define decode-ir-string-escape ((input nat-listp))
  :returns (mv (chars acl2::nat-list-resultp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf :unterminated-string-escape) nil))
       ((mv ascii-matchedp ascii-code ascii-rest)
        (decode-ir-ascii-escape input))
       ((when ascii-matchedp)
        (mv (list ascii-code) ascii-rest))
       (nat (car input))
       ((when (eql nat #x26)) (mv nil (cdr input)))    ; \&
       ((when (eql nat #x61)) (mv (list #x07) (cdr input))) ; \a
       ((when (eql nat #x62)) (mv (list #x08) (cdr input))) ; \b
       ((when (eql nat #x66)) (mv (list #x0C) (cdr input))) ; \f
       ((when (eql nat #x6E)) (mv (list #x0A) (cdr input))) ; \n
       ((when (eql nat #x72)) (mv (list #x0D) (cdr input))) ; \r
       ((when (eql nat #x74)) (mv (list #x09) (cdr input))) ; \t
       ((when (eql nat #x76)) (mv (list #x0B) (cdr input))) ; \v
       ((when (eql nat #x5C)) (mv (list #x5C) (cdr input))) ; \\
       ((when (eql nat #x22)) (mv (list #x22) (cdr input))) ; \"
       ((when (eql nat #x27)) (mv (list #x27) (cdr input))) ; \'
       ((when (eql nat #x5E))
        (b* (((when (endp (cdr input)))
              (mv (reserrf :unterminated-caret-escape) input))
             (ctrl (cadr input))
             ((unless (and (<= #x40 ctrl) (<= ctrl #x5F)))
              (mv (reserrf (list :invalid-caret-escape ctrl))
                  input)))
          (mv (list (nfix (- ctrl #x40))) (nthcdr 2 input))))
       ((mv num-matchedp num-code num-rest)
        (decode-ir-numeric-escape input))
       ((when num-matchedp)
        (if (unicode-scalar-codepointp num-code)
            (mv (list num-code) num-rest)
          (mv (reserrf (list :numeric-escape-out-of-range num-code))
              input))))
    (mv (reserrf (list :invalid-string-escape input)) input))
  ///

  (defret len-of-decode-ir-string-escape-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable decode-ir-string-escape)))))

(define decode-ir-string-content ((input nat-listp))
  :returns (codepoints acl2::nat-list-resultp)
  :measure (len (nat-list-fix input))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input)) nil)
       (nat (car input))
       ((when (eql nat #x5C))
        (b* (((mv chars rest-input)
              (decode-ir-string-escape (cdr input)))
             ((when (reserrp chars)) (reserrf-push chars))
             (tail (decode-ir-string-content rest-input))
             ((when (reserrp tail)) (reserrf-push tail)))
          (append chars tail)))
       ((unless (ir-string-char-codepointp nat))
        (reserrf (list :invalid-string-codepoint nat)))
       (tail (decode-ir-string-content (cdr input)))
       ((when (reserrp tail)) (reserrf-push tail)))
    (cons nat tail)))

(define abs-word ((tree abnf::treep))
  :returns (text acl2::string-resultp)
  (b* (((okf &) (abnf::check-tree-nonleaf tree "word")))
    (tree-text tree)))

(define abs-name ((tree abnf::treep))
  :returns (name acl2::string-resultp)
  (b* (((okf &) (abnf::check-tree-nonleaf tree "name"))
       (text (tree-text tree))
       ((unless (ir-name-tokenp text))
        (reserrf (list :invalid-name text))))
    text))

(define abs-literal ((tree abnf::treep))
  :returns (text acl2::string-resultp)
  (b* (((okf &) (abnf::check-tree-nonleaf tree "literal"))
       (text (tree-text tree))
       ((unless (ir-literal-tokenp text))
        (reserrf (list :invalid-literal text))))
    text))

(define abs-string-lit ((tree abnf::treep))
  :returns (text acl2::string-resultp)
  (b* (((okf &) (abnf::check-tree-nonleaf tree "string-lit"))
       (raw (abs-symbols-to-nats (abnf::tree->string tree)))
       ((unless (and (consp raw)
                     (consp (cdr raw))
                     (eql (car raw) #x22)
                     (eql (car (last raw)) #x22)))
        (reserrf (list :invalid-string-literal raw)))
       ((okf content)
        (decode-ir-string-content
         (string-lit-content-codepoints raw))))
    (codepoints=>string content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Types and parameters.

(defines abs-types-and-params

  (define abs-type-list-from-trees ((trees abnf::tree-listp))
    :returns (types fut-type-list-resultp)
    :measure (abnf::tree-list-count trees)
    (b* (((when (endp trees)) nil)
         ((if (tree-rulename-p (car trees) "type"))
          (b* (((okf type) (abs-type (car trees)))
               ((okf rest) (abs-type-list-from-trees (cdr trees))))
            (cons type rest))))
      (abs-type-list-from-trees (cdr trees))))

  (define abs-entry-type-list-from-trees ((trees abnf::tree-listp))
    :returns (types fut-type-list-resultp)
    :measure (abnf::tree-list-count trees)
    (b* (((when (endp trees)) nil)
         ((if (tree-rulename-p (car trees) "entry-type"))
          (b* (((okf type) (abs-entry-type (car trees)))
               ((okf rest) (abs-entry-type-list-from-trees (cdr trees))))
            (cons type rest))))
      (abs-entry-type-list-from-trees (cdr trees))))

  (define abs-param-list-from-trees ((trees abnf::tree-listp))
    :returns (params param-list-resultp)
    :measure (abnf::tree-list-count trees)
    (b* (((when (endp trees)) nil)
         ((if (tree-rulename-p (car trees) "param"))
          (b* (((okf param) (abs-param (car trees)))
               ((okf rest) (abs-param-list-from-trees (cdr trees))))
            (cons param rest))))
      (abs-param-list-from-trees (cdr trees))))

  (define abs-type ((tree abnf::treep))
    :returns (type fut-type-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "prim-type")
             (b* (((okf children) (first-branch inner "prim-type"))
                  ((okf word) (first-direct-rulename children "word"))
                  ((okf name) (abs-word word)))
               (make-fut-type-prim :name name)))
            ((equal rulename? "array-type")
             (b* (((okf children) (first-branch inner "array-type"))
                  (size-tree? (optional-first-direct-rulename children "word"))
                  (size (if size-tree? (tree-text size-tree?) nil))
                  ((okf elem-tree) (first-direct-rulename children "type"))
                  ((okf elem) (abs-type elem-tree)))
               (make-fut-type-array :size size :elem elem)))
            (t (reserrf (list :unexpected-type-child rulename?)))))
    :measure-debug t)

  (define abs-entry-type ((tree abnf::treep))
    :returns (type fut-type-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "entry-type"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "prim-type")
             (b* (((okf children) (first-branch inner "prim-type"))
                  ((okf word) (first-direct-rulename children "word"))
                  ((okf name) (abs-word word)))
               (make-fut-type-prim :name name)))
            ((equal rulename? "entry-array-type")
             (b* (((okf children) (first-branch inner "entry-array-type"))
                  ((okf elem-tree)
                   (first-direct-rulename children "entry-type"))
                  ((okf elem) (abs-entry-type elem-tree)))
               (make-fut-type-array :size nil :elem elem)))
            (t (reserrf (list :unexpected-entry-type-child rulename?))))))

  (define abs-result-types ((tree abnf::treep))
    :returns (types fut-type-list-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "result-types")))
      (abs-type-list-from-trees children)))

  (define abs-entry-result-type-list ((tree abnf::treep))
    :returns (types fut-type-list-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "entry-result-type-list")))
      (abs-entry-type-list-from-trees children)))

  (define abs-entry-result-types ((tree abnf::treep))
    :returns (types fut-type-list-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf child) (abnf::check-tree-nonleaf-1-1 tree "entry-result-types"))
         ((okf rulename?) (abnf::check-tree-nonleaf? child)))
      (cond ((equal rulename? "entry-result-type-list")
             (abs-entry-result-type-list child))
            ((equal rulename? "entry-type")
             (b* (((okf type) (abs-entry-type child)))
               (list type)))
            (t (reserrf (list :unexpected-entry-result-types-child
                              rulename?))))))

  (define abs-param ((tree abnf::treep))
    :returns (param param-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "param"))
         ((okf name-tree) (first-direct-rulename children "name"))
         ((okf type-tree) (first-direct-rulename children "type"))
         ((okf name) (abs-name name-tree))
         ((okf type) (abs-type type-tree)))
      (make-param :name name :type type)))

  (define abs-params ((tree abnf::treep))
    :returns (params param-list-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "params")))
      (abs-param-list-from-trees children)))

  (define abs-pattern ((tree abnf::treep))
    :returns (params param-list-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "pattern")))
      (abs-param-list-from-trees children)))

  :verify-guards nil)

(verify-guards abs-type
  :hints (("Goal"
           :in-theory (enable abs-type-list-from-trees
                              abs-entry-type-list-from-trees
                              abs-param-list-from-trees
                              abs-type
                              abs-entry-type
                              abs-result-types
                              abs-entry-result-type-list
                              abs-entry-result-types
                              abs-param
                              abs-params
                              abs-pattern))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expressions and bodies.

(defines abs-forms

  (define abs-expr-list-from-trees ((trees abnf::tree-listp))
    :returns (exprs expr-list-resultp)
    :measure (abnf::tree-list-count trees)
    (b* (((when (endp trees)) nil)
         ((if (tree-rulename-p (car trees) "exp"))
          (b* (((okf expr) (abs-exp (car trees)))
               ((okf rest) (abs-expr-list-from-trees (cdr trees))))
            (cons expr rest))))
      (abs-expr-list-from-trees (cdr trees))))

  (define abs-stmt-list-from-trees ((trees abnf::tree-listp))
    :returns (stmts stmt-list-resultp)
    :measure (abnf::tree-list-count trees)
    (b* (((when (endp trees)) nil)
         ((if (tree-rulename-p (car trees) "stmt"))
          (b* (((okf stmt) (abs-stmt (car trees)))
               ((okf rest) (abs-stmt-list-from-trees (cdr trees))))
            (cons stmt rest))))
      (abs-stmt-list-from-trees (cdr trees))))

  (define abs-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "exp"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "literal")
             (b* (((okf text) (abs-literal inner)))
               (make-expr-literal :text text)))
            ((equal rulename? "name")
             (b* (((okf name) (abs-name inner)))
               (make-expr-var :name name)))
            ((equal rulename? "array-exp")
             (abs-array-exp inner))
            ((equal rulename? "brace-exp")
             (abs-brace-exp inner))
            ((equal rulename? "apply-exp")
             (abs-apply-exp inner))
            ((equal rulename? "map-exp")
             (abs-map-exp inner))
            ((equal rulename? "call-exp")
             (abs-call-exp inner))
            ((equal rulename? "paren-exp")
             (abs-paren-exp inner))
            ((equal rulename? "lambda-exp")
             (abs-lambda-exp inner))
            (t (reserrf (list :unexpected-exp-child rulename?))))))

  (define abs-array-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "array-exp"))
         ((okf elems) (abs-expr-list-from-trees children))
         ((okf type-tree) (first-direct-rulename children "type"))
         ((okf type) (abs-type type-tree)))
      (make-expr-array :elems elems :type type)))

  (define abs-brace-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "brace-exp"))
         ((okf elems) (abs-expr-list-from-trees children)))
      (make-expr-brace :elems elems)))

  (define abs-apply-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "apply-exp"))
         ((okf name-tree) (first-direct-rulename children "name"))
         ((okf fun) (abs-name name-tree))
         ((okf args) (abs-expr-list-from-trees children))
         ((okf result-types-tree)
          (first-direct-rulename children "result-types"))
         ((okf result-types) (abs-result-types result-types-tree)))
      (make-expr-apply :fun fun
                       :args args
                       :result-types result-types)))

  (define abs-map-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "map-exp"))
         ((okf args) (abs-expr-list-from-trees children)))
      (make-expr-map :args args)))

  (define abs-call-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "call-exp"))
         ((okf name-tree) (first-direct-rulename children "name"))
         ((okf fun) (abs-name name-tree))
         ((okf args) (abs-expr-list-from-trees children)))
      (make-expr-call :fun fun :args args)))

  (define abs-paren-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "paren-exp"))
         ((okf expr-tree) (first-direct-rulename children "exp"))
         ((okf expr) (abs-exp expr-tree)))
      (make-expr-paren :expr expr)))

  (define abs-lambda-exp ((tree abnf::treep))
    :returns (expr expr-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "lambda-exp"))
         ((okf pattern-tree) (first-direct-rulename children "pattern"))
         ((okf result-types-tree)
          (first-direct-rulename children "result-types"))
         ((okf body-tree) (first-direct-rulename children "lambda-body"))
         ((okf params) (abs-pattern pattern-tree))
         ((okf result-types) (abs-result-types result-types-tree))
         ((okf body) (abs-lambda-body body-tree)))
      (make-expr-lambda :params params
                        :result-types result-types
                        :body body)))

  (define abs-result-exps ((tree abnf::treep))
    :returns (exprs expr-list-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "result-exps")))
      (abs-expr-list-from-trees children)))

  (define abs-stmt ((tree abnf::treep))
    :returns (stmt stmt-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "stmt"))
         ((okf pattern-tree) (first-direct-rulename children "pattern"))
         ((okf expr-tree) (first-direct-rulename children "exp"))
         ((okf pattern) (abs-pattern pattern-tree))
         ((okf expr) (abs-exp expr-tree)))
      (make-stmt-let :pattern pattern :expr expr)))

  (define abs-body-core ((tree abnf::treep))
    :returns (body body-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "body-core"))
         ((okf stmts) (abs-stmt-list-from-trees children))
         ((okf results-tree) (first-direct-rulename children "result-exps"))
         ((okf results) (abs-result-exps results-tree)))
      (make-body-block :stmts stmts :results results)))

  (define abs-lambda-body ((tree abnf::treep))
    :returns (body body-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "lambda-body"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "body-core")
             (abs-body-core inner))
            ((equal rulename? "result-exps")
             (b* (((okf results) (abs-result-exps inner)))
               (make-body-block :stmts nil :results results)))
            (t (reserrf (list :unexpected-lambda-body-child rulename?))))))

  (define abs-body ((tree abnf::treep))
    :returns (body body-resultp)
    :measure (abnf::tree-count tree)
    (b* (((okf children) (first-branch tree "body"))
         (body-core-tree (first-direct-rulename children "body-core"))
         (inner
          (if (reserrp body-core-tree)
              (first-direct-rulename children "result-exps")
            body-core-tree))
         ((when (reserrp inner)) inner)
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "body-core")
             (abs-body-core inner))
            ((equal rulename? "result-exps")
             (b* (((okf results) (abs-result-exps inner)))
               (make-body-block :stmts nil :results results)))
            (t (reserrf (list :unexpected-body-child rulename?))))))

  :verify-guards nil)

(verify-guards abs-exp
  :hints (("Goal"
           :in-theory (enable abs-expr-list-from-trees
                              abs-stmt-list-from-trees
                              abs-exp
                              abs-array-exp
                              abs-brace-exp
                              abs-apply-exp
                              abs-map-exp
                              abs-call-exp
                              abs-paren-exp
                              abs-lambda-exp
                              abs-result-exps
                              abs-stmt
                              abs-body-core
                              abs-lambda-body
                              abs-body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Declarations and programs.

(define abs-entry-attr-external-name ((tree abnf::treep))
  :returns (external-name acl2::string-resultp)
  (b* (((okf children) (first-branch tree "entry-attr"))
       ((okf string-tree) (first-direct-rulename children "string-lit"))
       ((okf external-name) (abs-string-lit string-tree)))
    external-name))

(define abs-entry-attr-result-types ((tree abnf::treep))
  :returns (entry-result-types fut-type-list-resultp)
  (b* (((okf children) (first-branch tree "entry-attr"))
       ((okf result-types-tree)
        (first-direct-rulename children "entry-result-types"))
       ((okf entry-result-types) (abs-entry-result-types result-types-tree)))
    entry-result-types))

(define abs-decl ((tree abnf::treep))
  :returns (decl decl-resultp)
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "decl"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond
     ((equal rulename? "fun-decl")
      (b* (((okf children) (first-branch inner "fun-decl"))
           ((okf name-tree) (first-direct-rulename children "name"))
           ((okf params-tree) (first-direct-rulename children "params"))
           ((okf result-types-tree)
            (first-direct-rulename children "result-types"))
           ((okf body-tree) (first-direct-rulename children "body"))
           ((okf name) (abs-name name-tree))
           ((okf params) (abs-params params-tree))
           ((okf result-types) (abs-result-types result-types-tree))
           ((okf body) (abs-body body-tree)))
        (make-decl-fun :name name
                       :params params
                       :result-types result-types
                       :body body)))
     ((equal rulename? "entry-decl")
      (b* (((okf children) (first-branch inner "entry-decl"))
           ((okf attr-tree) (first-direct-rulename children "entry-attr"))
           ((okf external-name) (abs-entry-attr-external-name attr-tree))
           ((okf attr-children) (first-branch attr-tree "entry-attr"))
           (doc-tree? (optional-first-direct-rulename attr-children "entry-doc"))
           ((okf doc)
            (if doc-tree?
                (b* (((okf doc-children) (first-branch doc-tree? "entry-doc"))
                     ((okf string-tree)
                      (first-direct-rulename doc-children "string-lit")))
                  (abs-string-lit string-tree))
              nil))
           ((okf entry-result-types)
            (abs-entry-attr-result-types attr-tree))
           ((okf name-tree) (first-direct-rulename children "name"))
           ((okf params-tree) (first-direct-rulename children "params"))
           ((okf result-types-tree)
            (first-direct-rulename children "result-types"))
           ((okf body-tree) (first-direct-rulename children "body"))
           ((okf name) (abs-name name-tree))
           ((okf params) (abs-params params-tree))
           ((okf result-types) (abs-result-types result-types-tree))
           ((okf body) (abs-body body-tree)))
        (make-decl-entry :external-name external-name
                         :doc doc
                         :entry-result-types entry-result-types
                         :name name
                         :params params
                         :result-types result-types
                         :body body)))
     (t (reserrf (list :unexpected-decl-child rulename?))))))

(define abs-decl-list-from-trees ((trees abnf::tree-listp))
  :returns (decls decl-list-resultp)
  (b* (((when (endp trees)) nil)
       ((if (tree-rulename-p (car trees) "decl"))
        (b* (((okf decl) (abs-decl (car trees)))
             ((okf rest) (abs-decl-list-from-trees (cdr trees))))
          (cons decl rest))))
    (abs-decl-list-from-trees (cdr trees))))

(define abs-program ((tree abnf::treep))
  :returns (program fut-program-resultp)
  (b* (((okf children) (first-branch tree "program"))
       (name-source-tree? (optional-first-direct-rulename children "name-source"))
       ((okf name-source)
        (if name-source-tree?
            (b* (((okf name-children) (first-branch name-source-tree?
                                                    "name-source"))
                 ((okf word-tree) (first-direct-rulename name-children "word")))
              (abs-word word-tree))
          nil))
       ((okf decls) (abs-decl-list-from-trees children)))
    (make-fut-program :name-source name-source :decls decls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
