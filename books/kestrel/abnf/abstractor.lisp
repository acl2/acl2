; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "parser")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-to-abstract-syntax
  :parents (abnf)
  :short "An executable mapping from
          the concrete syntax of ABNF to the abstract syntax of ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF abstract syntax is an abstraction of the concrete syntax.
     That is, there is a mapping
     from the parse trees obtained by parsing sequences of natural numbers
     according to the rules of the concrete syntax of ABNF,
     to the entities of the abstract syntax of ABNF.
     The mapping abstracts away many of the details of the concrete syntax.")
   (xdoc::p
    "This abstraction mapping is defined by a collection of functions.
     These functions explicitly check that the trees
     satisfy certain expected conditions.
     Eventually, these expected conditions
     should be proved to follow from suitable guards."))
  :order-subtopics t)

(define abstract-fail ()
  :returns (nothing null)
  :parents (concrete-to-abstract-syntax)
  :short "Called when abstraction fails."
  :long
  (xdoc::topstring-p
   "The error message does not carry a lot of information,
    but it keeps the abstraction functions simple for now.")
  (hard-error 'abnf "ABNF Grammar Abstraction Error." nil)
  :no-function t)

(define abstract-terminals ((tree treep))
  :returns (nats nat-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('term') parse tree,
          where @('term') is a terminal numeric or character value notation,
          is generally abstracted to its list of natural numbers."
  :long
  (xdoc::topstring-p
   "The parse tree must be a leaf labeled by a list of natural numbers.
    That list of natural numbers is returned.")
  (if (tree-case tree :leafterm)
      (tree-leafterm->get tree)
    (abstract-fail))
  :no-function t)

(define abstract-terminal ((tree treep))
  :returns (nat natp :rule-classes (:rewrite :type-prescription))
  :parents (concrete-to-abstract-syntax)
  :short "A @('term') parse tree,
          where @('term') is a terminal numeric or character value notation
          that denotes a single natural number,
          is sometimes abstracted to its only natural number."
  :long
  (xdoc::topstring-p
   "The parse tree must be a leaf labeled by a list of one natural number.
    That natural number is returned.")
  (b* ((nats (abstract-terminals tree)))
    (if (consp nats)
        (car nats)
      (prog2$ (abstract-fail) 0)))
  :no-function t)

(define abstract-grouped-terminals ((tree treep))
  :returns (nats nat-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('( term1 / ... / termN )') parse tree,
          where @('term1'), ..., @('termN') are
          terminal numeric or character value notations,
          is generally abstracted to its list of natural numbers."
  :long
  (xdoc::topstring-p
   "The parse tree must have a root labeled by no rule name,
    with a single leaf subtree labeled by a list of natural numbers.
    That list of natural numbers is returned.")
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees)))
    (abstract-terminals subtree))
  :no-function t)

(define abstract-grouped-terminal ((tree treep))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('( term1 / ... / termN )') parse tree,
          where @('term1'), ..., @('termN') are
          terminal numeric and character notations
          that all denote single natural numbers,
          is sometimes abstracted to its only natural number."
  :long
  (xdoc::topstring-p
   "The parse tree must have a root labeled by no rule name,
    with a single leaf subtree labeled by a list of one natural number.
    That natural number is returned.")
  (b* ((nats (abstract-grouped-terminals tree)))
    (if (consp nats)
        (car nats)
      (prog2$ (abstract-fail) 0)))
  :no-function t)

(define abstract-*-grouped-terminal ((trees tree-listp))
  :returns (nats nat-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('( term1 / ... / termN )') parse trees,
          where @('term1'), ..., @('termN') are
          terminal numeric or character value notations
          that all denote single natural numbers,
          are abstracted to the list of its natural numbers."
  :long
  (xdoc::topstring-p
   "Each parse tree must have a root labeled by no rule name,
    with a single leaf subtree labeled by a list of one natural number.
    That natural number is returned in correspondence to the parse tree.")
  (b* (((fun (fail)) (prog2$ (abstract-fail) nil))
       ((when (endp trees)) nil)
       ((cons tree trees) trees)
       (nat (abstract-grouped-terminal tree))
       (nats (abstract-*-grouped-terminal trees)))
    (cons nat nats))
  :no-function t)

(define abstract-bit ((tree treep))
  :returns (bit (integer-range-p 0 2 bit))
  :parents (concrete-to-abstract-syntax)
  :short "A @('BIT') parse tree is abstracted to its bit."
  (b* (((fun (fail)) (prog2$ (abstract-fail) 0))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       (nat (abstract-terminal subtree)))
    (if (eql nat (char-code #\0))
        0
      1))
  :no-function t
  ///

  (more-returns
   (bit natp :rule-classes :type-prescription)
   (bit (< bit 2)
        :name abstract-bit-linear
        :rule-classes :linear)))

(define abstract-digit ((tree treep))
  :returns (digit (integer-range-p 0 10 digit))
  :parents (concrete-to-abstract-syntax)
  :short "A @('DIGIT') parse tree is abstracted to its decimal digit."
  (b* (((fun (fail)) (prog2$ (abstract-fail) 0))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       (nat (abstract-terminal subtree))
       ((unless (and (<= (char-code #\0) nat)
                     (<= nat (char-code #\9)))) (fail)))
    (- nat (char-code #\0)))
  :no-function t
  ///

  (more-returns
   (digit natp :rule-classes :type-prescription)
   (digit (< digit 10)
          :name abstract-digit-linear
          :rule-classes :linear)))

(define abstract-hexdig ((tree treep))
  :returns (hexdig (integer-range-p 0 16 hexdig))
  :parents (concrete-to-abstract-syntax)
  :short "A @('HEXDIG') parse tree is abstracted to its hexadecimal digit."
  (b* (((fun (fail)) (prog2$ (abstract-fail) 0))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       ((when (tree-case subtree :nonleaf)) (abstract-digit subtree))
       (nat (abstract-terminal subtree)))
    (cond ((member nat (list (char-code #\A) (char-code #\a))) 10)
          ((member nat (list (char-code #\B) (char-code #\b))) 11)
          ((member nat (list (char-code #\C) (char-code #\c))) 12)
          ((member nat (list (char-code #\D) (char-code #\d))) 13)
          ((member nat (list (char-code #\E) (char-code #\e))) 14)
          (t 15)))
  :no-function t
  ///

  (more-returns
   (hexdig natp :rule-classes :type-prescription)
   (hexdig (< hexdig 16)
           :name abstract-hexdig-linear
           :rule-classes :linear)))

(define abstract-*bit ((trees tree-listp))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('BIT') parse trees is abstracted to
          the big-endian value of its bits."
  (abstract-*bit-aux trees 0)
  :no-function t

  :prepwork
  ((define abstract-*bit-aux ((trees tree-listp) (accumulator natp))
     :returns (nat natp)
     (b* (((when (endp trees)) (nfix accumulator))
          (bit (abstract-bit (car trees))))
       (abstract-*bit-aux (cdr trees)
                          (+ (* 2 accumulator) bit)))
     :no-function t)))

(define abstract-*digit ((trees tree-listp))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('DIGIT') parse trees is abstracted to
          the big-endian value of its decimal digits."
  (abstract-*digit-aux trees 0)
  :no-function t

  :prepwork
  ((define abstract-*digit-aux ((trees tree-listp) (accumulator natp))
     :returns (nat natp)
     (b* (((when (endp trees)) (nfix accumulator))
          (digit (abstract-digit (car trees))))
       (abstract-*digit-aux (cdr trees)
                            (+ (* 10 accumulator) digit)))
     :no-function t)))

(define abstract-*hexdig ((trees tree-listp))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('HEXDIG') parse trees is abstracted to
          the big-endian value of its hexadecimal digits."
  (abstract-*hexdig-aux trees 0)
  :no-function t

  :prepwork
  ((define abstract-*hexdig-aux ((trees tree-listp) (accumulator natp))
     :returns (nat natp)
     (b* (((when (endp trees)) (nfix accumulator))
          (hexdig (abstract-hexdig (car trees))))
       (abstract-*hexdig-aux (cdr trees)
                             (+ (* 16 accumulator) hexdig)))
     :no-function t)))

(define abstract-dot/dash-1*bit ((tree treep))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('(\".\" 1*BIT)') or @('(\"-\" 1*BIT)') parse tree
          is abstracted to the big-endian value of its bits."
  (b* (((fun (fail)) (prog2$ (abstract-fail) 0))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail)))
    (abstract-*bit (cadr treess)))
  :no-function t)

(define abstract-dot/dash-1*digit ((tree treep))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('(\".\" 1*DIGIT)') or @('(\"-\" 1*DIGIT)') parse tree
          is abstracted to the big-endian value of its decimal digits."
  (b* (((fun (fail)) (prog2$ (abstract-fail) 0))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail)))
    (abstract-*digit (cadr treess)))
  :no-function t)

(define abstract-dot/dash-1*hexdig ((tree treep))
  :returns (nat natp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('(\".\" 1*HEXDIG)') or @('(\"-\" 1*HEXDIG)') parse tree
          is abstracted to the big-endian value of its hexadecimal digits."
  (b* (((fun (fail)) (prog2$ (abstract-fail) 0))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail)))
    (abstract-*hexdig (cadr treess)))
  :no-function t)

(define abstract-*-dot-1*bit ((trees tree-listp))
  :returns (nats nat-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('(\".\" 1*BIT)') parse trees
          is abstracted to the list of their corresponding big-endian values."
  (b* (((when (endp trees)) nil)
       (nat (abstract-dot/dash-1*bit (car trees)))
       (nats (abstract-*-dot-1*bit (cdr trees))))
    (cons nat nats))
  :no-function t)

(define abstract-*-dot-1*digit ((trees tree-listp))
  :returns (nats nat-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('(\".\" 1*DIGIT)') parse trees
          is abstracted to the list of their corresponding big-endian values."
  (b* (((when (endp trees)) nil)
       (nat (abstract-dot/dash-1*digit (car trees)))
       (nats (abstract-*-dot-1*digit (cdr trees))))
    (cons nat nats))
  :no-function t)

(define abstract-*-dot-1*hexdig ((trees tree-listp))
  :returns (nats nat-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('(\".\" 1*HEXDIG)') parse trees
          is abstracted to the list of their corresponding big-endian values."
  (b* (((when (endp trees)) nil)
       (nat (abstract-dot/dash-1*hexdig (car trees)))
       (nats (abstract-*-dot-1*hexdig (cdr trees))))
    (cons nat nats))
  :no-function t)

(define abstract-bin/dec/hex-val-rest-dot-p ((tree treep))
  :returns (yes/no booleanp)
  :parents (concrete-to-abstract-syntax)
  :short "Discriminate
          between a @('(\".\" 1*BIT)')
          and a @('(\"-\" 1*BIT)') parse tree,
          or between a @('(\".\" 1*DIGIT)')
          and a @('(\"-\" 1*DIGIT)') parse tree,
          or between a @('(\".\" 1*HEXDIG)')
          and a @('(\"-\" 1*HEXDIG)') parse tree."
  :long
  (xdoc::topstring-p
   "This is used by
    @(tsee abstract-bin-val-rest),
    @(tsee abstract-dec-val-rest), and
    @(tsee abstract-hex-val-rest)
    to distinguish between the two alternatives
    in the definiens of @('bin-val'), @('dec-val'), and @('hex-val').
    For the first alternative, @('t') is returned;
    for the second alternative, @('nil') is returned.")
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees)))
    (equal subtree (tree-leafterm (list (char-code #\.)))))
  :no-function t)

(define abstract-bin-val-rest ((tree treep))
  :returns (result (or (nat-listp result)
                       (natp result)))
  :parents (concrete-to-abstract-syntax)
  :short "A @('[ 1*(\".\" 1*BIT) / (\"-\" 1*BIT) ]') parse tree
          is abstracted to
          either the list of its big-endian values (for the first alternative)
          or its single big-endian value (for the second alternative)."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((when (endp treess)) nil)
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (1st-subtree (car trees)))
    (if (abstract-bin/dec/hex-val-rest-dot-p 1st-subtree)
        (abstract-*-dot-1*bit trees)
      (abstract-dot/dash-1*bit 1st-subtree)))
  :no-function t)

(define abstract-dec-val-rest ((tree treep))
  :returns (result (or (nat-listp result)
                       (natp result)))
  :parents (concrete-to-abstract-syntax)
  :short "A @('[ 1*(\".\" 1*DIGIT) / (\"-\" 1*DIGIT) ]') parse tree
          is abstracted to
          either the list of its big-endian values (for the first alternative)
          or its single big-endian value (for the second alternative)."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((when (endp treess)) nil)
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (1st-subtree (car trees)))
    (if (abstract-bin/dec/hex-val-rest-dot-p 1st-subtree)
        (abstract-*-dot-1*digit trees)
      (abstract-dot/dash-1*digit 1st-subtree)))
  :no-function t)

(define abstract-hex-val-rest ((tree treep))
  :returns (result (or (nat-listp result)
                       (natp result)))
  :parents (concrete-to-abstract-syntax)
  :short "A @('[ 1*(\".\" 1*HEXDIG) / (\"-\" 1*HEXDIG) ]') parse tree
          is abstracted to
          either the list of its big-endian values (for the first alternative)
          or its single big-endian value (for the second alternative)."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((when (endp treess)) nil)
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (1st-subtree (car trees)))
    (if (abstract-bin/dec/hex-val-rest-dot-p 1st-subtree)
        (abstract-*-dot-1*hexdig trees)
      (abstract-dot/dash-1*hexdig 1st-subtree)))
  :no-function t)

(define abstract-bin-val ((tree treep))
  :returns (num-val num-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('bin-val') parse tree is abstracted to
          its corresponding numeric value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (num-val-direct nil)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees-1st-num (cadr treess))
       (1st-num (abstract-*bit trees-1st-num))
       (trees-rest (caddr treess))
       ((unless (consp trees-rest)) (fail))
       (tree-rest (car trees-rest))
       (rest (abstract-bin-val-rest tree-rest)))
    (if (nat-listp rest)
        (num-val-direct (cons 1st-num rest))
      (num-val-range 1st-num rest)))
  :guard-hints (("Goal"
                 :use (:instance
                       return-type-of-abstract-bin-val-rest
                       (tree (car (caddr (tree-nonleaf->branches tree)))))))
  :no-function t)

(define abstract-dec-val ((tree treep))
  :returns (num-val num-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('dec-val') parse tree is abstracted to
          its corresponding numeric value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (num-val-direct nil)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees-1st-num (cadr treess))
       (1st-num (abstract-*digit trees-1st-num))
       (trees-rest (caddr treess))
       ((unless (consp trees-rest)) (fail))
       (tree-rest (car trees-rest))
       (rest (abstract-dec-val-rest tree-rest)))
    (if (nat-listp rest)
        (num-val-direct (cons 1st-num rest))
      (num-val-range 1st-num rest)))
  :guard-hints (("Goal"
                 :use (:instance
                       return-type-of-abstract-dec-val-rest
                       (tree (car (caddr (tree-nonleaf->branches tree)))))))
  :no-function t)

(define abstract-hex-val ((tree treep))
  :returns (num-val num-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('hex-val') parse tree is abstracted to
          its corresponding numeric value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (num-val-direct nil)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees-1st-num (cadr treess))
       (1st-num (abstract-*hexdig trees-1st-num))
       (trees-rest (caddr treess))
       ((unless (consp trees-rest)) (fail))
       (tree-rest (car trees-rest))
       (rest (abstract-hex-val-rest tree-rest)))
    (if (nat-listp rest)
        (num-val-direct (cons 1st-num rest))
      (num-val-range 1st-num rest)))
  :guard-hints (("Goal"
                 :use (:instance
                       return-type-of-abstract-hex-val-rest
                       (tree (car (caddr (tree-nonleaf->branches tree)))))))
  :no-function t)

(define abstract-bin/dec/hex-val ((tree treep))
  :returns (num-val num-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('(bin-val / dec-val / hex-val )') parse tree is abstracted to
          its corresponding numeric value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (num-val-direct nil)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       ((unless (tree-case subtree :nonleaf)) (fail))
       (rulename (tree-nonleaf->rulename? subtree)))
    (cond ((equal rulename *bin-val*) (abstract-bin-val subtree))
          ((equal rulename *dec-val*) (abstract-dec-val subtree))
          (t (abstract-hex-val subtree))))
  :no-function t)

(define abstract-num-val ((tree treep))
  :returns (num-val num-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('num-val') parse tree is abstracted to
          its corresponding numeric value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (num-val-direct nil)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail))
       (trees (cadr treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees)))
    (abstract-bin/dec/hex-val subtree))
  :no-function t)

(define abstract-quoted-string ((tree treep))
  :returns (charstring acl2::stringp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('quoted-string') parse tree is abstracted to
          its character string."
  (b* (((fun (fail)) (prog2$ (abstract-fail) ""))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees (cadr treess))
       (nats (abstract-*-grouped-terminal trees))
       ((unless (unsigned-byte-listp 8 nats)) (fail)))
    (nats=>string nats))
  :no-function t)

(define abstract-case-sensitive/insensitive-string ((tree treep))
  :returns (charstring acl2::stringp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('case-sensitive') or @('case-insensitive') parse tree
          is abstracted to its character string."
  (b* (((fun (fail)) (prog2$ (abstract-fail) ""))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail))
       (trees (cadr treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees)))
    (abstract-quoted-string subtree))
  :no-function t)

(define abstract-char-val ((tree treep))
  :returns (char-val char-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('char-val') parse tree is abstracted to
          its corresponding character value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (char-val-sensitive "")))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       ((unless (tree-case subtree :nonleaf)) (fail))
       (rulename (tree-nonleaf->rulename? subtree))
       (charstring
        (abstract-case-sensitive/insensitive-string subtree)))
    (if (equal rulename *case-sensitive-string*)
        (char-val-sensitive charstring)
      (char-val-insensitive charstring)))
  :no-function t)

(define abstract-prose-val ((tree treep))
  :returns (prose-val prose-val-p)
  :parents (concrete-to-abstract-syntax)
  :short "A @('prose-val') parse tree is abstracted to
          its corresponding prose value notation."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (prose-val "")))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees (cadr treess))
       (nats (abstract-*-grouped-terminal trees))
       ((unless (unsigned-byte-listp 8 nats)) (fail)))
    (prose-val (nats=>string nats)))
  :no-function t)

(define abstract-alpha ((tree treep))
  :returns (letter characterp)
  :parents (concrete-to-abstract-syntax)
  :short "An @('ALPHA') parse tree is abstracted to its corresponding letter."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (code-char 0)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       (nat (abstract-terminal subtree))
       ((unless (< nat 256)) (fail)))
    (code-char nat))
  :no-function t)

(define abstract-alpha/digit/dash ((tree treep))
  :returns (char characterp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('(ALPHA / DIGIT / \"-\")') parse tree
          is abstracted to its corresponding character."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (code-char 0)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       ((when (equal subtree (tree-leafterm (list (char-code #\-))))) #\-)
       ((unless (tree-case subtree :nonleaf)) (fail))
       (rulename? (tree-nonleaf->rulename? subtree))
       ((when (equal rulename? *alpha*)) (abstract-alpha subtree))
       (digit (abstract-digit subtree))
       ((unless (< digit 10)) (fail)))
    (code-char (+ (char-code #\0) digit)))
  :no-function t)

(define abstract-*-alpha/digit/dash ((trees tree-listp))
  :returns (chars character-listp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('(ALPHA / DIGIT / \"-\")') parse trees
          is abstracted to its corresponding list of characters."
  (b* (((when (endp trees)) nil)
       ((cons tree trees) trees)
       (char (abstract-alpha/digit/dash tree))
       (chars (abstract-*-alpha/digit/dash trees)))
    (cons char chars))
  :no-function t)

(define abstract-rulename ((tree treep))
  :returns (rulename rulenamep)
  :parents (concrete-to-abstract-syntax)
  :short "A @('rulename') parse tree is abstracted to
          its corresponding rule name."
  :long
  (xdoc::topstring-p
   "The characters are converted to lowercase,
    according to the normalized representation
    required by @(tsee rulename-wfp).")
  (b* (((fun (fail)) (prog2$ (abstract-fail) (rulename "")))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail))
       (trees-alpha (car treess))
       (trees-alpha/digit/dash (cadr treess))
       ((unless (consp trees-alpha)) (fail))
       (tree-alpha (car trees-alpha))
       (char (abstract-alpha tree-alpha))
       (chars (abstract-*-alpha/digit/dash trees-alpha/digit/dash))
       (charstring (implode (downcase-charlist (cons char chars)))))
    (rulename charstring))
  :no-function t)

(define abstract-*digit-star-*digit ((tree treep))
  :returns (mv (min natp) (max natip))
  :parents (concrete-to-abstract-syntax)
  :short "A @('(*DIGIT \"*\" *DIGIT)') parse tree is abstracted to
          (i) the big-endian value of its first @('*DIGIT') and
          (ii) either the big-endian value of its second @('*DIGIT')
          (if non-empty)
          or infinity
          (if empty)."
  (b* (((fun (fail)) (prog2$ (abstract-fail) (mv 0 (nati-finite 0))))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees-min (car treess))
       (trees-max (caddr treess))
       (min (abstract-*digit trees-min))
       (max (if (consp trees-max)
                (nati-finite (abstract-*digit trees-max))
              (nati-infinity))))
    (mv min max))
  :no-function t)

(define abstract-repeat ((tree treep))
  :returns (range repeat-rangep)
  :parents (concrete-to-abstract-syntax)
  :short "A @('repeat') parse tree is abstracted to
          its correspoding repetition range."
  :long
  (xdoc::topstring-p
   "The two alternatives of the @('repeat') rule
    both consist of singleton concatenations,
    so a @('repeat') parse tree must have a list of one list of trees.
    For the first alternative, the list of trees
    must consist of one or more @('DIGIT') parse trees;
    for the second alternative, the list of trees
    must consist of a single @('(*DIGIT \"*\" *DIGIT)') parse tree.
    The latter kind of parse tree is distinguished from the former kind
    by having a @('nil') rule for the @('(*DIGIT \"*\" *DIGIT)') group.")
  (b* (((fun (fail)) (prog2$ (abstract-fail)
                             (repeat-range 0 (nati-finite 0))))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (1st-subtree (car trees))
       ((unless (tree-case 1st-subtree :nonleaf)) (fail)))
    (if (tree-nonleaf->rulename? 1st-subtree)
        (b* ((num (abstract-*digit trees)))
          (make-repeat-range :min num :max (nati-finite num)))
      (b* (((mv min max) (abstract-*digit-star-*digit 1st-subtree)))
        (make-repeat-range :min min :max max))))
  :no-function t)

(define abstract-?repeat ((tree treep))
  :returns (range repeat-rangep)
  :parents (concrete-to-abstract-syntax)
  :short "A @('[repeat]') parse tree is abstracted to
          its corresponding repetition range."
  :long
  (xdoc::topstring-p
   "When the @('repeat') subtree is absent,
    the tree is abstracted to the range from 1 to 1.")
  (b* (((fun (fail)) (prog2$ (abstract-fail)
                             (repeat-range 0 (nati-finite 0))))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((when (endp treess)) (repeat-range 1 (nati-finite 1)))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees)))
    (abstract-repeat subtree))
  :no-function t)

(defines abstract-alt/conc/rep/elem/group/option
  :verify-guards nil ; done below

  (define abstract-alternation ((tree treep))
    :returns (alternation alternationp)
    :parents (concrete-to-abstract-syntax)
    :short "An @('alternation') parse tree is abstracted to
            its corresponding alternation."
    :long "@(def abstract-alternation)"
    (b* (((fun (fail)) (abstract-fail))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (and (consp treess)
                       (consp (cdr treess)))) (fail))
         (trees-concatenation (car treess))
         (trees-concatenations (cadr treess))
         ((unless (consp trees-concatenation)) (fail))
         (tree-concatenation (car trees-concatenation))
         (concatenation (abstract-concatenation tree-concatenation))
         (concatenations (abstract-alt-rest trees-concatenations)))
      (cons concatenation concatenations))
    :measure (tree-count tree)
    :no-function t)

  (define abstract-concatenation ((tree treep))
    :returns (concatenation concatenationp)
    :parents (concrete-to-abstract-syntax)
    :short "A @('concatenation') parse tree is abstracted to
            its corresponding concatenation."
    :long "@(def abstract-concatenation)"
    (b* (((fun (fail)) (abstract-fail))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (and (consp treess)
                       (consp (cdr treess)))) (fail))
         (trees-repetition (car treess))
         (trees-repetitions (cadr treess))
         ((unless (consp trees-repetition)) (fail))
         (tree-repetition (car trees-repetition))
         (repetition (abstract-repetition tree-repetition))
         (repetitions (abstract-conc-rest trees-repetitions)))
      (cons repetition repetitions))
    :measure (tree-count tree)
    :no-function t)

  (define abstract-repetition ((tree treep))
    :returns (repetition repetitionp)
    :parents (concrete-to-abstract-syntax)
    :short "A @('repetition') parse tree is abstracted to
            its corresponding repetition."
    :long "@(def abstract-repetition)"
    (b* (((fun (fail)) (prog2$ (abstract-fail)
                               (repetition (repeat-range 0 (nati-finite 0))
                                           (element-group nil))))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (and (consp treess)
                       (consp (cdr treess)))) (fail))
         (trees-repeat (car treess))
         (trees-element (cadr treess))
         ((unless (consp trees-repeat)) (fail))
         (tree-repeat (car trees-repeat))
         (range (abstract-?repeat tree-repeat))
         ((unless (consp trees-element)) (fail))
         (tree-element (car trees-element))
         (element (abstract-element tree-element)))
      (make-repetition :range range :element element))
    :measure (tree-count tree)
    :no-function t)

  (define abstract-element ((tree treep))
    :returns (element elementp)
    :parents (concrete-to-abstract-syntax)
    :short "An @('element') parse tree is abstracted to
            its corresponding element."
    :long "@(def abstract-element)"
    (b* (((fun (fail)) (prog2$ (abstract-fail) (element-group nil)))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (consp treess)) (fail))
         (trees (car treess))
         ((unless (consp trees)) (fail))
         (tree (car trees))
         ((unless (tree-case tree :nonleaf)) (fail))
         (rulename (tree-nonleaf->rulename? tree)))
      (cond ((equal rulename *rulename*)
             (element-rulename (abstract-rulename tree)))
            ((equal rulename *group*)
             (element-group (abstract-group/option tree)))
            ((equal rulename *option*)
             (element-option (abstract-group/option tree)))
            ((equal rulename *char-val*)
             (element-char-val (abstract-char-val tree)))
            ((equal rulename *num-val*)
             (element-num-val (abstract-num-val tree)))
            (t (element-prose-val (abstract-prose-val tree)))))
    :measure (tree-count tree)
    :no-function t)

  (define abstract-group/option ((tree treep))
    :returns (alternation alternationp)
    :parents (concrete-to-abstract-syntax)
    :short "A @('group') or @('option') parse tree is abstracted to
            its alternation inside the group or option."
    :long "@(def abstract-group/option)"
    (b* (((fun (fail)) (abstract-fail))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (and (consp treess)
                       (consp (cdr treess))
                       (consp (cddr treess)))) (fail))
         (trees (caddr treess))
         ((unless (consp trees)) (fail))
         (tree (car trees)))
      (abstract-alternation tree))
    :measure (tree-count tree)
    :no-function t)

  (define abstract-alt-rest ((trees tree-listp))
    :returns (concatenations alternationp)
    :parents (concrete-to-abstract-syntax)
    :short "A list of zero or more
            @('(*c-wsp \"/\" *c-wsp concatenation)') parse trees
            is abstracted to the list of its concatenations
            (i.e. an alternation)."
    :long "@(def abstract-alt-rest)"
    (b* (((fun (fail)) (abstract-fail))
         ((when (endp trees)) nil)
         ((cons tree trees) trees)
         ((unless (tree-case tree :nonleaf)) (fail))
         (concatenation (abstract-alt-rest-comp tree))
         (concatenations (abstract-alt-rest trees)))
      (cons concatenation concatenations))
    :measure (tree-list-count trees)
    :no-function t)

  (define abstract-alt-rest-comp ((tree treep))
    :returns (concatenation concatenationp)
    :parents (concrete-to-abstract-syntax)
    :short "A @('(*c-wsp \"/\" *c-wsp concatenation)') parse tree
            is abstracted to its concatenation."
    :long "@(def abstract-alt-rest-comp)"
    (b* (((fun (fail)) (abstract-fail))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (and (consp treess)
                       (consp (cdr treess))
                       (consp (cddr treess))
                       (consp (cdddr treess)))) (fail))
         (trees (cadddr treess))
         ((unless (consp trees)) (fail))
         (tree (car trees)))
      (abstract-concatenation tree))
    :measure (tree-count tree)
    :no-function t)

  (define abstract-conc-rest ((trees tree-listp))
    :returns (repetitions concatenationp)
    :parents (concrete-to-abstract-syntax)
    :short "A list of zero or more
            @('(1*c-wsp repetition)') parse trees
            is abstracted to the list of its repetitions
            (i.e. a concatenation)."
    :long "@(def abstract-conc-rest)"
    (b* (((fun (fail)) (abstract-fail))
         ((when (endp trees)) nil)
         ((cons tree trees) trees)
         ((unless (tree-case tree :nonleaf)) (fail))
         (repetition (abstract-conc-rest-comp tree))
         (repetitions (abstract-conc-rest trees)))
      (cons repetition repetitions))
    :measure (tree-list-count trees)
    :no-function t)

  (define abstract-conc-rest-comp ((tree treep))
    :returns (repetition repetitionp)
    :parents (concrete-to-abstract-syntax)
    :short "A @('(1*c-wsp repetition)') parse tree
            is abstracted to its repetition."
    :long "@(def abstract-conc-rest-comp)"
    (b* (((fun (fail)) (prog2$ (abstract-fail)
                               (repetition (repeat-range 0 (nati-finite 0))
                                           (element-group nil))))
         ((unless (tree-case tree :nonleaf)) (fail))
         (treess (tree-nonleaf->branches tree))
         ((unless (and (consp treess)
                       (consp (cdr treess)))) (fail))
         (trees (cadr treess))
         ((unless (consp trees)) (fail))
         (tree (car trees)))
      (abstract-repetition tree))
    :measure (tree-count tree)
    :no-function t)

  ///

  (verify-guards abstract-alternation))

(define abstract-defined-as ((tree treep))
  :returns (incremental booleanp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('defined-as') parse tree is abstracted to
          the boolean indicating whether the rule is incremental or not."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess)))) (fail))
       (trees (cadr treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       (nats (abstract-grouped-terminals subtree)))
    (not (equal nats (list (char-code #\=)))))
  :no-function t)

(define abstract-elements ((tree treep))
  :returns (alternation alternationp)
  :parents (concrete-to-abstract-syntax)
  :short "An @('elements') parse tree is abstracted to its alternation."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (tree (car trees)))
    (abstract-alternation tree))
  :no-function t)

(define abstract-rule ((tree treep))
  :returns (rule rulep)
  :parents (concrete-to-abstract-syntax)
  :short "A @('rule') parse tree is abstracted to its corresponding rule."
  (b* (((fun (fail)) (prog2$ (abstract-fail)
                             (rule (rulename "") nil nil)))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (consp (cdr treess))
                     (consp (cddr treess)))) (fail))
       (trees-rulename (car treess))
       (trees-defined-as (cadr treess))
       (trees-elements (caddr treess))
       ((unless (consp trees-rulename)) (fail))
       (tree-rulename (car trees-rulename))
       ((unless (consp trees-defined-as)) (fail))
       (tree-defined-as (car trees-defined-as))
       ((unless (consp trees-elements)) (fail))
       (tree-elements (car trees-elements))
       (rulename (abstract-rulename tree-rulename))
       (incremental (abstract-defined-as tree-defined-as))
       (alternation (abstract-elements tree-elements)))
    (make-rule :name rulename
               :incremental incremental
               :definiens alternation))
  :no-function t)

(define abstract-rule-/-*cwsp-cnl ((tree treep))
  :returns (rule? maybe-rulep)
  :parents (concrete-to-abstract-syntax)
  :short "A @('( rule / (*c-wsp c-nl) )') parse tree is abstracted to
          either its rule (for the first alternative)
          or nothing (for the second alternative)."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess))
       ((unless (consp trees)) (fail))
       (subtree (car trees))
       ((unless (tree-case subtree :nonleaf)) (fail)))
    (if (equal (tree-nonleaf->rulename? subtree) *rule*)
        (abstract-rule subtree)
      nil))
  :no-function t)

(define abstract-*-rule-/-*cwsp-cnl ((trees tree-listp))
  :returns (rules rulelistp)
  :parents (concrete-to-abstract-syntax)
  :short "A list of zero or more @('( rule / (*c-wsp c-nl) )') parse trees
          is abstracted to the list of its corresponding rules."
  (b* (((fun (fail)) (abstract-fail))
       ((when (endp trees)) nil)
       ((cons tree trees) trees)
       (rule? (abstract-rule-/-*cwsp-cnl tree))
       (rules (abstract-*-rule-/-*cwsp-cnl trees)))
    (if rule?
        (cons rule? rules)
      rules))
  :no-function t)

(define abstract-rulelist ((tree treep))
  :returns (rules rulelistp)
  :parents (concrete-to-abstract-syntax)
  :short "A @('rulelist') parse tree is abstracted to
          its corresponding list of rules."
  (b* (((fun (fail)) (abstract-fail))
       ((unless (tree-case tree :nonleaf)) (fail))
       (treess (tree-nonleaf->branches tree))
       ((unless (consp treess)) (fail))
       (trees (car treess)))
    (abstract-*-rule-/-*cwsp-cnl trees))
  :no-function t)
