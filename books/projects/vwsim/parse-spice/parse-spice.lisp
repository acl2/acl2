
; parse-spice.lisp

; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; Modified by Vivek Ramanathan & Warren A. Hunt, Jr.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; See file ``README'' for additional information.

; Preliminary Spice Parser

; Note: This is written for clarity.  There are surely ways to make it more
; efficient.  For example instead of breaking into lines before parsing each
; line, one could save a list of line-break positions first, or maybe just
; create each line by tokenizing from the full string until finding a newline.
; Another example is repeated traversal by parse-line-1 when there are nested
; parentheses.

(in-package "ACL2")

(program)
(set-state-ok t)
(include-book "std/util/bstar" :dir :system)
(include-book "projects/apply/top" :dir :system) ; for loop$ in next-line-etc

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Summary, including issues and possible future work
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section has the following subsections:

;;; Documentation
;;; Outline
;;; Assumptions and Limitations
;;; Other notes

;;; --------------------
;;; Documentation
;;; --------------------

; At this time there is very little documentation!  Here is the minimal
; documentation.  More can be learned by browsing output files *.parsed and
; reading code and comments below.  I can write more on request.

; We define a macro (parse-spice filename &optional outfile) that converts a
; ".cir" file to an output file that contains the parser result.  If outfile is
; omitted, then the parse is printed to the terminal.  Note that the intended
; input file is expected to have extension ".cir" but the input parameter,
; filename, does not include that extension.

; The macro (parse-spice-lst lst in-dir out-dir) takes a list of such
; extension-free filenames.  Each of these, say F, represents a file named
; F.cir in the given input directory, in-dir.  This macro writes corresponding
; results foo.parsed to the given output directory, out-dir.  Both in-dir and
; out-dir must avoid including a final "/" character.

;;; --------------------
;;; Outline
;;; --------------------

; This file is divided into the following sections.

;;; Summary, including issues and possible future work
;     The current section, which outlines the problem and code and discusses
;     simplifying assumptions, possible future work, and so on.

;;; Lex Spice lines
;     A line from Spice input file, represented as a string, is converted to a
;     list of tokens.

;;; Parse Spice values
;     An individual token is converted to a number if possible.

;;; Parse Spice tokens
;     A list of patterns, which represents the expected parse structure, is
;     matched against a list of tokens, resulting in corresponding parser
;     output: a list of parsed tokens.

;;; Parse Spice lines
;     Each line starts with a token that determines the expected structure of
;     that line.  We use the web document
;     http://www.ecircuitcenter.com/SPICEsummary.htm
;     which we have saved in an accompanying text file, SPICEsummary.txt.
;     as a guide, but it does not exactly match our 14 examples.  Deviations
;     are discussed below.

;;; Parse Spice files
;     The steps above are put together to define macros
;     parse-spice and parse-spice-lst.

;;; --------------------
;;; Assumptions and Limitations
;;; --------------------

; The following statement types are not handled, but the parser could
; presumably be extended to do so.  The effort required may vary considerably;
; some will be relatively trivial while others will require major
; reorganization and extension of the parsing algorithm.

; - POLY
; - PULSE (e.g., in I device)
; - Many "STATEMENTS"; e.g. .IC and .NODESET (would require handling of
;   node=value; currently we only handle literal=value)
; - INPUT SOURCES
; - ANALOG BEHAVIORAL MODELING
; - Parenthesized variable names such as V(3) or v(6,7)

; We made some reasonable decisions on classification.

; - Numbers begin with a digit except that this may be preceded by an optional
;   minus sign.  If the first subsequent non-digit character other than a
;   decimal point is e or E followed by one or more digits, those digits are
;   the exponent of 10 (representing scientific notation).

; - As per the spec, the first character of a device name indicates the type of
;   device (capacitor, diode, etc.).  We ignore case when determining that
;   type.

; Here are some simplifications made (not a complete list), all based on the
; assumption that inputs are all legal.

;   - We don't enforce any syntactic restrictions on the equalities for a T
;     device (beyond the usual restrictions).

;   - Each "controlled source" device (e.g., "E device - Voltage Controlled
;     Voltage Source") is handled just like the other devices.

; The function parse-line-2 generally follows the specification for each type
; of line given at http://www.ecircuitcenter.com/SPICEsummary.htm (file
; SPICEsummary.txt).  Some types weren't covered by that spec, so we guessed
; based on examples; see the definition of parse-line-2 below.  We also made
; changes where necessary.  In particular, the following example exemplifies
; the grammar followed in all our examples for I and V devices: a name followed
; by three identifiers and then a list of values.  So we used that grammer and
; ignored the specification for I and V devices, which didn't seem to fit.
;
;   Vvramp net@28 gnd pwl (0 0 1p 1.75V)

; The spec has generally driven how we represent tokens in the parse, with the
; result that there are several kinds of identifiers; see parse-line-2, where
; one finds :NAME, :MODEL, :SUBCIRCUIT-NAME, and so on.  Perhaps these should
; all just be :IDENTIFIER.

; The spec doesn't specify which tokens may represent numbers (possibly with
; units).  We take a guess, based on examples in the spec and other examples we
; have; see *numeric-keywords*.  But we are only guessing; for example, we are
; guessing that area is a number (with possible unit).  We do not insist that
; those are numbers; in particular, while the spec seems to suggest (based on
; its examples) that nodes are numbers.  That was often not the case in our
; other examples.  So when we think that a token may represent a number, we
; attempt to parse it as a number but parse it as a name when that doesn't fit.
; See the function parse-spice-value.

; We assume that the right-hand side of an equality is either an identifier or
; else is the sum of two identifiers.  See function parse-expr.  This might be
; pretty easy to extend, but it sufficient for the examples we have so we have
; kept it simple so far.

; We make the following assumptions in function pair-patterns-rec.  Perhaps we
; should check these assumptions.  If these assumed restrictions are relaxed
; then we may consiider changing pair-patterns-rec so that it needn't match the
; entire line, in which case the remainder of the line (that which hasn't yet
; been parsed) is returned -- but I haven't thought this through.

; - When a pattern includes an optional equality, (:? :EQUAL), it is not
;   followed by another pattern that can match an equality.

; - When a pattern list includes (:LIST pat), which indicates zero or more
;   matches of pat against the list of tokens, then (:LIST pat) much be the
;   last in that pattern list.

;;; --------------------
;;; Other notes
;;; --------------------

; A note on debugging: Error messages typically print the line L that can't be
; parsed, so one can submit (parse-line "L" 1) and then trace relevant
; functions to see what might be going wrong, e.g., (trace$ parse-number
; parse-expr pair-pattern pair-patterns-rec).  The second argument of
; parse-line is a line number, which should appear in the error message.
; (It is 1 in the example just above for no particular reason!)

; Most of this file is in :program mode, only because it didn't seem worthwhile
; yet to take the time to prove termination (which might be easy) and verify
; guards (which might not be easy, but might matter for performance if
; functions are in :logic mode).

; Parse-spice-lst will create the output directory (given by argument out-dir)
; if it doesn't already exist, at least in CCL.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Errors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro parse-er (ctx str &rest args)
  `(er hard ,ctx
       "[Line ~x0] ~@1"
       lineno
       (msg ,str ,@args)))

(defmacro parse-er? (ctx str &rest args)
  `(er hard? ,ctx
       "[Line ~x0] ~@1"
       lineno
       (msg ,str ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lex Spice lines
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *newline-string*
  (string #\Newline))

(defun scan-to-token-end (line pos end)

; Line is a string without newline characters.  Pos is less than end.  We
; return the first position p in line with p >= pos such that (char line p)
; terminates the token starting at position pos -- unless there is no such
; terminator, in which case, we return end.

  (cond ((int= pos end) end)
        ((member-eq (char line pos)

; The following are the token terminators.  This list might be updated as we
; either discover new ones.

                    '(#\Space #\Tab #\( #\) #\, #\=))
         pos)
        (t (scan-to-token-end line (1+ pos) end))))

(defun next-token (line pos end)

; Return the token starting at position pos in the given string, line, which
; has no newline character and ends at position end.

  (let ((pos (scan-past-whitespace line pos end)))
    (cond ((int= pos end) (mv nil end))
          (t (let ((ch (char line pos)))
               (case ch
                 (#\( (mv :left-paren (1+ pos)))
                 (#\) (mv :right-paren (1+ pos)))
                 (#\= (mv := (1+ pos)))
                 (#\+ (mv :+ (1+ pos)))
                 (otherwise
                  (let ((token-end (scan-to-token-end line (1+ pos) end)))
                    (cond ((int= token-end end)
                           (mv (subseq line pos end) end))
                          (t (mv (subseq line pos token-end)
                                 token-end)))))))))))

(defun tokenize-line-1 (line pos end acc)

; Accumulate into acc all tokens in the given string, line (which has no
; newline characters), finally reversing that accumulator.

  (cond ((int= pos end) (reverse acc))
        (t (mv-let (token new-pos)
             (next-token line pos end)
             (cond (token (tokenize-line-1 line new-pos end
                                           (cons token acc)))
                   (t (reverse acc)))))))

(defun tokenize-line (line)

; Return the list of tokens in line (which has no newline characters).
; A special case is that when the first token starts with character *, then we
; view this as a comment line and return (list :comment line).

  (let ((len (length line)))
    (mv-let (token pos)
      (next-token line 0 len)
      (assert$
       (not (equal token ""))
       (cond
        ((eql (char token 0) #\*)
         (list :comment line))
        (t (cons token (tokenize-line-1 line pos len nil))))))))

(defun tline-type (tline lineno)

; Tline is the list of all tokens from a given line.

  (assert$
   (consp tline)
   (let ((token (car tline)))
     (cond
      ((eq token :comment) :COMMENT)
      ((equal token "")
       (parse-er
        'tline-type
        "Implementation error: Unexpected empty token at beginning of tline ~
         ~x0."
        tline))
      ((eql (char token 0) #\.)
       (list :STATEMENT
             (intern$ (string-upcase (subseq token 1 (length token)))
                      "KEYWORD")))
      (t
       (list :DEVICE 
             (intern$ (string (char token 0))
                      "KEYWORD")))))))

(defun split-at-right-paren (lst cur-paren-level orig-paren-level lineno acc)

; We are searching for a :right-paren token that matches an implicit
; :left-paren token, and we return the corresponding (mv pre post), where lst
; is (append pre (list :right-paren) post).  Formally: no initial subsequence
; of pre has one more :right-paren token than it has :left-paren tokens.

  (cond ((endp lst) (mv (parse-er
                         'split-at-right-paren
                         "Missing right parenthesis at level ~x0!"
                         cur-paren-level)
                        nil))
        ((eq (car lst) :right-paren)
         (if (eql cur-paren-level orig-paren-level)
             (mv (reverse acc) (cdr lst))
           (assert$ (< orig-paren-level cur-paren-level)
                    (split-at-right-paren (cdr lst)
                                          (1- cur-paren-level)
                                          orig-paren-level
                                          lineno
                                          (cons (car lst) acc)))))
        (t (split-at-right-paren (cdr lst)
                                 cur-paren-level
                                 orig-paren-level
                                 lineno
                                 (cons (car lst) acc)))))

(defun parse-line-1 (tokens paren-level lineno acc)

; We modify the given list of tokens by matching parentheses into a single
; list, (:LIST ...).  Also, we throw away comma tokens (",") that are within a
; list.  Example:

; (parse-line-1 
;   '("ab" "c" :LEFT-PAREN "de" "," "f" := "gh" :RIGHT-PAREN "i") 0 1 nil)
; =
; ("ab" "c" (:LIST "de" "f" := "gh") "i")

  (cond ((endp tokens) (reverse acc))
        ((eq (car tokens) :left-paren)
         (mv-let (pre post)
           (split-at-right-paren (cdr tokens) paren-level paren-level lineno
                                 nil)
           (parse-line-1 post paren-level
                         lineno
                         (cons (cons :list
                                     (parse-line-1 pre (1+ paren-level) lineno
                                                   nil))
                               acc))))
        ((eq (car tokens) :right-paren)
         (parse-er
          'parse-line-1
          "Excess right parenthesis at level ~x0!"
          paren-level))
        ((and (equal (car tokens) ",")
              (< 0 paren-level))
         (parse-line-1 (cdr tokens) paren-level lineno acc))
        (t (parse-line-1 (cdr tokens) paren-level lineno
                         (cons (car tokens) acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Parse Spice values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(logic) ; This section is mostly in :logic mode.

(defconst *char-code-0*
  (char-code #\0))

(defun digits-to-nat-rec (s i bound acc)

; Given i <= bound, characters s[i] through s[bound-1] should be base-10
; digits.  Acc is a natural number.  We return x + acc*10^(bound-i).

  (declare (xargs :measure (nfix (- bound i))
                  :guard (and (stringp s)
                              (natp i)
                              (natp bound)
                              (<= i bound)
                              (<= bound (length s))
                              (natp acc))))
  (cond ((mbe :logic (or (not (natp i))
                         (not (natp bound))
                         (<= bound i))
              :exec (int= i bound))
         (mv acc i))
        (t (let ((c (char s i)))
             (cond ((digit-char-p c)
                    (digits-to-nat-rec s (1+ i) bound
                                       (+ (- (char-code c) *char-code-0*)
                                          (* 10 acc))))
                   (t (mv acc i)))))))

(defthm natp-digits-to-nat-rec
  (implies (force (natp acc))
           (natp (car (digits-to-nat-rec s i bound acc))))
  :rule-classes :type-prescription)

(defun digits-to-nat (s i len sign-okp)

; S is a string, i is an index into s, and len is the length of s.  Sign-okp is
; nil when we disallow a minus sign at character i; otherwise that minus sign
; is allowed.  We return (mv signp n pos), where either n is nil, meaning that
; we didn't parse a number starting at position i in string, in which case pos
; = i, or else n is natural number obtained by reading the characters in s from
; i up to, but not including, pos.  Note that the resturned signp is t exactly
; when the number is negative.

  (declare (xargs :mode :logic
                  :guard (and (stringp s)
                              (eql len (length s))
                              (natp i)
                              (< i len))
                  :guard-hints (("Goal" :in-theory (disable nth)))))
  (b* (((mv signp i0)
        (if (and sign-okp
                 (eql (char s i) #\-)
                 (not (int= (1+ i) len)))
            (mv t (1+ i))
          (mv nil i)))
       ((when (not (digit-char-p (char s i0))))
        (mv nil nil i))
       ((mv n pos)
        (digits-to-nat-rec s i0 len 0)))
    (mv signp n pos)))

(defun parse-spice-value (s lineno)

; S is a string.  We return (mv x s1), where either x is nil (this is the case
; where we aren't finding number at the front of s) and s1 is s; or else
; (normal case) x is the parsed number and s1 is a tail of s starting just
; after the initial substring that was parsed into x, the exception being that
; s1 may be nil if that tail is "".

  (declare (xargs :guard (and (stringp s)
                              (not (equal s "")))

; We could specify :mode :logic, but then for efficiency we would want to
; verify guards, which would take some effort that doesn't seem worthwhile at
; the moment.

                  :mode :program))
  (b* ((len (length s))
       (init-dec-pos
        (cond ((and (< 0 len)
                    (eql (char s 0) #\.))
               0)
              ((and (< 1 len)
                    (eql (char s 0) #\-)
                    (eql (char s 1) #\.))
               1)
              (t nil)))
       ((mv sign1 n1 p1)
; Here n1 is the integer part of the result and p1 is the first position not
; yet consumed.
        (cond ((eql init-dec-pos 0)
               (mv nil 0 0))
              ((eql init-dec-pos 1)
               (mv t 0 1))
              (t (digits-to-nat s 0 len t))))
       ((when (null n1)) ; didn't parse a number, and p1 = 0
        (mv nil s))
       ((when (int= p1 len))
        (mv (if sign1 (- n1) n1) nil))
       (dec-p (eql (char s p1) #\.)) ; there is a decimal point
       (p1 (if dec-p (1+ p1) p1))
       ((when (int= p1 len)) ; optimization
        (if init-dec-pos ; started with "." or "-."
            (mv nil s)
          (mv (if sign1 (- n1) n1) nil)))
; Now read the decimal part of the number, if any.
       ((mv sign2 n2 p2)
        (cond (dec-p (digits-to-nat s p1 len nil))
              (t (mv nil nil p1))))
       (- (or (null sign2)
              (parse-er?
               'parse-spice-value
               "Implementation error: sign was disallowed!")))
       ((when (and (null n2)
                   init-dec-pos)) ; so, no number before or after the "."
; For example, neither .a nor -.a gives us any number.
        (mv nil s))
       (num0
        (cond ((or (null n2)
                   (int= n2 0))
               n1)
              (t (assert$
                  (<= 0 n1)
                  (+ n1
                     (/ n2 (expt 10 (- p2 p1))))))))
       (num (if sign1 (- num0) num0))
; Num is the number we wanted, except possibly for the exponent.  Now compute
; the exponent, if any, and also the second value returned, i.e., the tail of s
; (or nil).
       ((when (int= p2 len))
        (mv num nil))
       ((when (or (not (char-equal (char s p2) #\e)) ; next char is not e
                  (int= (1+ p2) len)))               ; ends in e
        (mv num (subseq s p2 len)))
       ((mv sign3 exp0 p3)
        (digits-to-nat s (1+ p2) len t))
       ((when (null exp0))
        (mv num (subseq s p2 len)))
       (exp (if sign3 (- exp0) exp0)))
    (mv (* (expt 10 exp) num)
        (and (not (int= p3 len))
             (subseq s p3 len)))))

(assert-event
 (and
  (equal (mv-list 2 (parse-spice-value "3.p" 1)) '(3 "p"))
  (equal (mv-list 2 (parse-spice-value "0.p" 1)) '(0 "p"))
  (equal (mv-list 2 (parse-spice-value "0." 1)) '(0 NIL))
  (equal (mv-list 2 (parse-spice-value "3." 1)) '(3 NIL))
  (equal (mv-list 2 (parse-spice-value "-3." 1)) '(-3 NIL))
  (equal (mv-list 2 (parse-spice-value "-3" 1)) '(-3 NIL))
  (equal (mv-list 2 (parse-spice-value "-0." 1)) '(0 NIL))
  (equal (mv-list 2 (parse-spice-value "-.3" 1)) '(-3/10 NIL))
  (equal (mv-list 2 (parse-spice-value "-.3p" 1)) '(-3/10 "p"))
  (equal (mv-list 2 (parse-spice-value "-.0p" 1)) '(0 "p"))
  (equal (mv-list 2 (parse-spice-value "-.p" 1)) '(NIL "-.p"))
  (equal (mv-list 2 (parse-spice-value ".p" 1)) '(NIL ".p"))
  (equal (mv-list 2 (parse-spice-value "-." 1)) '(NIL "-."))
  (equal (mv-list 2 (parse-spice-value ".-" 1)) '(NIL ".-"))
  (equal (mv-list 2 (parse-spice-value "0.-" 1)) '(0 "-"))))

(program) ; back to :program mode for the rest of the book

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Parse Spice tokens
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun parse-number (s lineno)
  (declare (xargs :guard (and (stringp s)
                              (not (equal s "")))))
  (mv-let (num units)
    (parse-spice-value s lineno)
    (cond ((null num) (list :NAME s))
          (t (list :NUMBER num units)))))

(defconst *numeric-keywords*

; These keyword patterns are the ones that we believe might represent numbers.

  '(:node :+node :-node :value
          :area
          :mag :phase
          :d :g :s
          :c :b :e
          :coupling
          :sub :subs
          :+control :-control
          :a+ :a- :b+ :b-
          :gain
          :points :start :end :incr
          :freq))

(defun pair-pattern (pat tok lineno)

; See pair-patterns-rec.  Pair-pattern does much of the single-step processing
; for that function.

  (cond ((stringp pat)
         (cond ((equal pat tok) (mv t (list :LITERAL tok)))
               (t (mv nil nil))))
        ((keywordp pat)
         (let ((x (if (member-eq pat *numeric-keywords*)
                      (parse-number tok lineno)
                    tok)))
           (mv t (list pat x))))
        ((atom pat)
         (mv nil nil))
        ((eq (car pat) :NAME) ; (:NAME c)
         (cond ((and (stringp tok)
                     (not (equal tok ""))
                     (char-equal (char tok 0) (cadr pat)))
                (mv t (list :NAME tok)))
               (t (mv nil nil))))
        ((eq (car pat) :MODEL) ; distinguish from number
         (let ((x (cadr pat)))
           (cond ((equal x "") (mv nil nil))
                 (t (let ((flg (not (digit-char-p (char x 0)))))
                      (cond (flg (mv flg (list :MODEL tok)))
                            (t (mv nil nil))))))))
        (t
         (mv (parse-er
              'pair-pattern
              "Implementation error: unexpected pattern, ~x0"
              pat)
             nil))))

(defun parse-expr (line lineno)

; We return (mv flg parse rest-line), where flg is nil if the parse of an
; expression from line fails (in which case the other return values are
; ignored), and otherwise parse is the expression parse corresponding to an
; initial subsequence of line and rest-line is the unparsed remainder of the
; line.

; Warning.  This is a very limited parser for expressions!  If we find
; expressions other than values (including identifiers) or sums of two
; expressions then we may have to extend this function or modify our approach
; to parsing expressions or even to parsing in general.

  (cond ((eq (cadr line) :+)
         (b* (((mv flg val)
               (pair-pattern :VALUE (car line) lineno))
              ((when (or (null flg) (null (cddr line))))
               (mv nil nil nil))
              ((mv flg2 val2)
               (pair-pattern :VALUE (caddr line) lineno))
              ((when (null flg2)) (mv nil nil nil)))
           (mv t (list :EXPR (list :PLUS val val2)) (cdddr line))))
        (t
         (b* (((mv flg val)
               (pair-pattern :VALUE (car line) lineno)))
           (mv flg (list :EXPR val) (cdr line))))))

(defun pair-patterns-rec (pats line lineno acc)

; Line is the output of parse-line-1: thus, it may include (:list ...), but
; only at the end.  It may also includ <var> := <expr>.  We accumulate the
; parse of line into acc.  If successful we return (mv t val), where val is the
; reverse of the accumulator.  If not, we return (mv nil nil).

; Pats is a normally a list of "patterns" (but see below for :LIST case), each
; of which has one of the following forms.

; - :kwd
;   a keyword; matches anything other than (:EQUAL .. ..), but certain keywords
;   are associated with numeric values (see parse-number)
; - "..."
;   a string; must match exactly
; - :=
;   should follow a token and precede an expression
; - :+
;   in an expression <expr1> :+ <expr2>
; - (:NAME c)
;   where c is a character; matches a string whose first character is c,
;   case-insensitive
; - (:LIST pat)
;   where pat is a pattern, representing a list of instances of that pattern;
;   must be the last member, and pat must not be :LIST or :?
; - (:? pat)
;   where pat is a pattern other than (:LIST ...) or (:? ...)

; A special case, however, is that pats is (:REPEAT . pat).  In that case we
; continue to process pat until line is empty.

  (cond
   ((endp pats)
    (cond
     ((null line) (mv t (reverse acc)))
     (t (mv nil nil))))
   (t (let* ((pat0 (car pats))
             (repeat-p (eq pat0 :REPEAT))
             (pat (if repeat-p (cdr pats) pat0))
             (rest-pats (if repeat-p pats (cdr pats))))
        (cond
         ((and repeat-p (null line))
          (mv t (reverse acc)))
         ((eq pat :EQUAL) ; line is: name := expr ...
          (cond ((or (null (cddr line))
                     (not (eq (cadr line) :=)))
                 (mv nil nil))
                (t (b* (((mv flg val)
                         (pair-pattern :NAME (car line) lineno))
                        ((when (null flg)) (mv nil nil))
                        ((mv flg2 val2 tokens)
                         (parse-expr (cddr line) lineno))
                        ((when (null flg2)) (mv nil nil)))
                     (pair-patterns-rec rest-pats
                                        tokens
                                        lineno
                                        (cons (list :EQUAL val val2) acc))))))
         ((or (atom pat)
              (eq (car pat) :NAME))
          (cond
           ((null line) (mv nil nil))
           (t (b* (((mv flg val)
                    (pair-pattern pat (car line) lineno))
                   ((when (null flg))
                    (mv nil nil)))
                (pair-patterns-rec rest-pats (cdr line) lineno
                                   (cons val acc))))))
         (t (assert$
             (and (member-eq (car pat) '(:? :LIST))
                  (true-listp pat)
                  (int= (length pat) 2))
             (cond
              ((eq (car pat) :?)
               (cond ((null line)
                      (mv t (reverse acc)))
                     ((eq (cadr pat) :EQUAL)
                      (cond ((eq (cadr line) :=)

; In this case we have found an equality, so we remove the surrounding :? as
; though the pattern was required.

; Here we assume that (:? :EQUAL) is not followed by another pattern that
; can match an equality.

                             (pair-patterns-rec (cons :EQUAL rest-pats)
                                                line lineno acc))
                            (t (pair-patterns-rec rest-pats line lineno acc))))
                     (t (b* (((mv flg val)
                              (pair-pattern (cadr pat) (car line) lineno))
                             ((when (null flg))
                              (pair-patterns-rec rest-pats line lineno acc))
                             ((mv flg2 ans)
                              (pair-patterns-rec rest-pats (cdr line) lineno
                                                 (cons val acc)))
                             ((when (null flg2))
                              (pair-patterns-rec rest-pats line lineno acc)))
                          (mv t ans)))))
              (t (assert$
                  (and (eq (car pat) :LIST)
                       (null rest-pats))
                  (b* ((list-p (and (consp (car line))
                                    (eq (caar line) :LIST)))
                       (tokens (if list-p (cdar line) line))
                       ((when (and list-p

; In this case we require the line to end with a list in order to match a
; pattern that ends with a list.

                                   (cdr line)))
                        (mv nil nil))
                       ((mv flg x)
                        (pair-patterns-rec (cons :REPEAT (cadr pat))
                                           tokens lineno nil))
                       ((when (null flg))
                        (mv nil nil)))
                    (mv t (revappend acc (list (cons :LIST x)))))))))))))))

(defun bad-pat (pats)

; Do simple syntactic check on the given list of patterns.  At this point we
; check only that none but the last can be a :LIST pattern.  When the check
; fails we return the bad :LIST pattern.

  (cond ((null (cdr pats))
         nil)
        (t (let ((pat (car pats)))
             (cond ((and (consp pat)
                         (eq (car pat) :LIST))
                    (car pat))
                   (t (bad-pat (cdr pats))))))))

(defun pair-patterns (pats line lineno)

; See pair-patterns-rec.

  (prog2$ (let ((pat (bad-pat pats)))
            (and pat
                 (parse-er
                  'pair-patterns
                  "Implementation error: Found :LIST pattern, ~x0, not at the ~
                   end of the patterns list, ~x1."
                  pat pats)))
          (pair-patterns-rec pats line  lineno nil)))

(defun pair-patterns+ (pats line lineno)
  (pair-patterns (cons :NAME pats) line lineno))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Parse Spice lines
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun parse-line-2 (typ line lineno)

; Line is the output of parse-line-1: thus, it may include a form (:list ...)
; at the end and subsequences <var> := <expr>.  It does not include the parse
; of the leading token (which is incorporated into typ).  We complete the parse
; of line.

; This is based primarily on the document
; http://www.ecircuitcenter.com/SPICEsummary.htm
; and the order below is based on that document.

  (case (car typ)
    (:DEVICE
     (case (cadr typ)
       (:C (pair-patterns+ '(:+NODE :-NODE (:? :MODEL) :VALUE (:? :EQUAL))
                           line lineno))
       (:D (pair-patterns+ '(:+NODE :-NODE :MODEL (:? :AREA))
                           line lineno))
       (:I
; Not like web document, e.g.:
; II1  vj1 GND pwl
;      (0 0 1p 0 2p 50uA 3p 50uA 4p 100uA 5p 100uA 6p 150uA 7p 150uA 10p 0)
        (pair-patterns+ '(:+NODE :-NODE :NAME (:LIST :VALUE))
                        line lineno))
       (:J (pair-patterns+ '(:D :G :S :MODEL (:? :AREA))
                           line lineno))
       (:K (let ((x (butlast line 1))
                 (num ; coupling
                  (parse-number (car (last line)) lineno)))
             (cond ((null num) (mv nil nil))
                   (t (b* (((mv flg y)
                            (pair-patterns+ '((:NAME #\L) (:NAME #\L))
                                            x lineno))
                           ((when (null flg))
                            (mv nil nil)))
                        (mv t (append y (list num))))))))
       (:L (pair-patterns+ '(:+NODE :-NODE (:? :MODEL) :VALUE (:? :EQUAL))
                           line lineno))
       (:M (pair-patterns+ '(:D :G :S :SUB :MODEL (:LIST :EQUAL))
                           line lineno))
       (:Q (pair-patterns+ '(:C :B :E (:? :SUBS) :MODEL (:? :AREA))
                           line lineno))
       (:R (pair-patterns+ '(:+NODE :-NODE (:? :MODEL) :VALUE)
                           line lineno))
       (:S (pair-patterns+ '(:+NODE :-NODE :+CONTROL :-CONTROL :MODEL)
                           line lineno))
       (:T (pair-patterns+ '(:A+ :A- :B+ :B- (:LIST :EQUAL))
                           line lineno))
       (:V ; not like web document, e.g., Vvramp net@28 gnd pwl (0 0 1p 1.75V)
        (pair-patterns+ '(:+NODE :-NODE :NAME (:LIST :VALUE))
                        line lineno))
       (:P ; phase source
        (pair-patterns+ '(:+NODE :-NODE :NAME (:LIST :VALUE))
                        line lineno))
       (:X
; The spec is as follows.
;   X{name} [{node}]* {subcircuit name}
; We remove {subcircuit name} so that the list is last (as we require);
; then put that back.
        (b* (((mv flg x)
              (pair-patterns+ '((:LIST :NODE))
                              (butlast line 1) lineno))
             ((when (null flg))
              (mv nil nil))
             ((mv flg2 y)
              (pair-pattern :SUBCIRCUIT-NAME (car (last line)) lineno))
             ((when (null flg2))
              (mv nil nil)))
          (mv t (append x (list y)))))
       (:E (pair-patterns+ '(:+NODE :-NODE :+CONTROL :-CONTROL :GAIN)
                           line lineno))
       (:F (pair-patterns+ '(:+NODE :-NODE :VSOURCE-NAME :GAIN)
                           line lineno))
       (:G (pair-patterns+ '(:+NODE :-NODE :+CONTROL :-CONTROL :GAIN)
                           line lineno))
       (:H (pair-patterns+ '(:+NODE :-NODE :VSOURCE-NAME :GAIN)
                           line lineno))
       (:B ; not mentioned in web document; surmise from examples
        (pair-patterns+ '(:+NODE :-NODE :NAME (:? :EQUAL))
                        line lineno))
       (otherwise (mv (parse-er
                       'parse-line-2
                       "Implementation error: device type not yet handled, ~x0"
                       typ)
                      nil))))
    (:STATEMENT
     (let ((cdr-line (cdr line))) ; strip off .model etc.
       (case (cadr typ)
         (:MODEL (pair-patterns '(:NAME :TYPE (:LIST :EQUAL))
                                cdr-line lineno))
         (:PRINT (pair-patterns
; We treat ann output variable as a name, for simplicity.
                  '(:TYPE :NAME)
                  ;; OR the print statement looks like
                  ;; '((:LIST :NAME))
                  cdr-line lineno))
         (:SUBCKT
; The values after the sub-circuit name are all identifiers, not numbers, in
; contrast to the web document.  For example:
;   SUBCKT basicComp__currentSource-uAmp_175 gnd iOut
; So we use the following from josim-template.cir
;   .subckt <name> <io-nodes>
          (pair-patterns '(:NAME (:LIST :IO-NODE))
                         cdr-line lineno))
         (:END ; not mentioned in web document; surmise from examples
          (pair-patterns nil cdr-line lineno))
         (:ENDS ; not mentioned in web document; surmise from examples
          (pair-patterns '((:? :NAME)) cdr-line lineno))
         (:GLOBAL ; not mentioned in web document; surmise from examples
          (pair-patterns '((:LIST :NODE)) cdr-line lineno))
         (:PARAM ; not mentioned in web document; surmise from examples
          (pair-patterns '(:EQUAL) cdr-line lineno))
         (:TRAN
; Simplifying a bit: treat all values as :VALUE and assume that final UIC is
; not present.
          (pair-patterns '((:LIST :VALUE)) cdr-line lineno))
         (otherwise (mv (parse-er
                         'parse-line-2
                         "Implementation error: statement type not yet ~
                          handled, ~x0"
                         typ)
                        nil)))))
    (otherwise (mv (parse-er
                    'parse-line-2
                    "Implementation error: Unknown type, ~x0"
                    typ)
                   nil))))

(defun parse-line (line lineno)

; Parse a line.

  (let* ((tline (tokenize-line line))
         (typ (tline-type tline lineno)))
    (cond ((eq typ :COMMENT) tline)
          (t (b* ((line-1 (parse-line-1 tline 0 lineno nil))
                  ((mv flg line-1)
                   (parse-line-2 typ line-1 lineno)))
               (and flg
                    (cons typ line-1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Parse Spice files
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun next-line-etc (pos str lineno end)

; Returns (mv line next-pos next-line-no), where next-pos is nil (and
; equivalently next-line-no is nil) when there is no newline at or after pos.

  (loop$ with newline-pos     ; basically local to a single iteration
         with start-pos = pos ; basically local to a single iteration
         with next-pos = pos  ; position at start of next iteration
         with next-lineno = lineno ; line number at start of next iteration
         with line = ""       ; line evolving at each iteration
; Comment-p is true when we are continuing after reading a comment line.
         with comment-p = nil
         do
         :values (nil nil nil)
         :measure (nfix (- end next-pos))
         (cond
          ((= next-pos end)
           (return (mv line nil nil)))
          ((and comment-p
                (not (member (char str next-pos) '(#\+ #\*))))
; We have just read a comment line, so we are done accumulating the current line.
           (return (mv line next-pos next-lineno)))
          (t
           (progn
             (setq comment-p (eql (char str next-pos) #\*))
             (setq newline-pos (search *newline-string* str :start2 next-pos))
             (setq start-pos next-pos)
             (cond
              (newline-pos
               (progn (setq next-pos (1+ newline-pos))
                      (setq next-lineno (1+ next-lineno))
                      (cond
                       (comment-p ; then just keep going
                        (progn))
                       (t
                        (progn (setq line
                                     (let ((s1 (subseq str
                                                       start-pos
                                                       newline-pos)))
                                       (if (equal line "") ; optimization
                                           s1
                                         (concatenate 'string line s1))))
                               (cond ((= next-pos end)
                                      (return (mv line nil nil)))
                                     ((eql (char str next-pos) #\+)
                                      (setq next-pos (1+ next-pos)))
                                     ((eql (char str next-pos) #\*)
                                      (progn))
                                     (t (return (mv line
                                                    next-pos
                                                    next-lineno)))))))))
              (t (return (mv (if comment-p
                                 line
                               (let ((s1 (subseq str start-pos end)))
                                 (if line
                                     (concatenate 'string line s1)
                                   s1)))
                             nil
                             nil)))))))))

(defun whitespacep (s)
  (let ((len (length s)))
    (= (scan-past-whitespace s 0 len) len)))

(defun parse-spice-from-string (str pos end lineno acc)

; Accumulate into acc the parsed lines from str, skipping blank lines, and then
; reverse the result.

  (cond
   ((eql pos end) ; equivalently, (>= pos end)
    (mv nil (reverse acc)))
   (t (mv-let (line next-pos next-lineno)
        (next-line-etc pos str lineno end)
        (cond
         (next-pos
          (cond
           ((whitespacep line)
            (parse-spice-from-string str next-pos end next-lineno acc))
           (t (let ((x (parse-line line lineno)))
                (cond (x (parse-spice-from-string str next-pos end next-lineno
                                                  (cons x acc)))
                      (t (mv t line)))))))
         ((equal line "") (mv nil (reverse acc)))
         (t (let ((x (parse-line line lineno)))
              (cond (x (mv nil (reverse (cons x acc))))
                    (t (mv t line))))))))))

(defun read-file-into-string-error-triple (filename state)

; This is based on the logical version of read-file-into-string; see
; read-file-into-string2-logical.  But there are two differences: below, we
; have removed the non-exec wrapper present in read-file-into-string2-logical,
; and also we now return state.  At some point it would be nice for ACL2 to
; make this functionality available.

  (let ((start 0)
        (bytes nil))
    (mv-let (erp val state)
      (mv-let (chan state)
        (open-input-channel filename :character state)
        (cond
         ((or (null chan)
; The following is to simplify guard verification.
              (not (state-p state)))
          (mv nil nil state))
         (t (mv-let (val state)
              (read-file-into-string1 chan state nil
                                      *read-file-into-string-bound*)
              (pprogn
               (ec-call ; guard verification here seems unimportant
                (close-input-channel chan state))
               (mv nil val state))))))
      (declare (ignore erp))
      (value
       (and (stringp val)

; If the following conjunct is false, then raw Lisp would cause an error; so
; there is no harm in adding it (and, it helps with guard verification).

            (<= start (length val))
            (subseq val
                    start
                    (if bytes
                        (min (+ start bytes)
                             (length val))
                      (length val))))))))

(defun parse-spice-result (filename state)

; Return the parse of the given file.

  (b* (((er str) (read-file-into-string-error-triple filename state))
       ((when (null str))
        (er soft 'parse-spice
            "Unable to read file (perhaps does not exist): ~x0"
            filename))
       ((mv erp result) ; when erp is true then result is a line
        (parse-spice-from-string str 0 (length str) 1 nil)))
    (cond (erp (er soft 'parse-spice
                   "Parse failed for line~|~x0~|in file~|~x1."
                   result filename))
          (t (value result)))))

(defun pprint-on-separate-lines (lst chan state)

; Print each element of lst on a separate line.

  (cond ((endp lst) (newline chan state))
        (t (pprogn (fms! "~x0" (list (cons #\0 (car lst))) chan state nil)
                   (pprint-on-separate-lines (cdr lst) chan state)))))

(defun parse-spice-fn (filename outfile state)

; See parse-spice.

  (b* (((er result)
        (parse-spice-result filename state))
       ((when (null outfile))
        (value result))
       ((mv chan state)
        (open-output-channel outfile :object state))
       ((when (null chan))
        (er soft 'parse-spice
            "Unable to open file ~x0 for output."
            outfile)))
    (state-global-let*
     ((fmt-hard-right-margin 10000 set-fmt-hard-right-margin)
      (fmt-soft-right-margin 10000 set-fmt-soft-right-margin))
     (pprogn (pprint-on-separate-lines result chan state)
             (close-output-channel chan state)
             (value outfile)))))

(defmacro parse-spice (filename &optional outfile)

; We compute the parse of filename, x.  Thus, x is a list of parsed lines,
; where each parsed line is a list of tokens.  Suppose there is no error.  If
; outfile is nil, return (mv nil x state).  Otherwise print each element of x
; to the given output file.

  `(parse-spice-fn ,filename ,outfile state))

(defun parse-spice-lst-fn (lst in-dir out-dir failures verbose state)

; See parse-spice-lst.

  (cond ((endp lst) (if failures
                        (er soft 'parse-spice-lst
                            "Failure~#0~[~/s~]: ~x0"
                            failures)
                      (value :success)))
        ((and (stringp in-dir)
              (stringp out-dir)
              (not (equal in-dir ""))
              (not (eql (char in-dir (1- (length in-dir))) #\/))
              (not (equal out-dir ""))
              (not (eql (char out-dir (1- (length out-dir))) #\/)))
         (b* ((infile (concatenate 'string in-dir "/" (car lst) ".cir"))
              (outfile (concatenate 'string out-dir "/" (car lst) ".parsed"))
              (state (if verbose
                         (fms "Parsing ~x0 into ~x1.~|"
                              (list (cons #\0 infile) (cons #\1 outfile))
                              (standard-co state) state nil)
                       state))
              ((mv erp ?val state)
               (parse-spice-fn infile outfile state)))
           (parse-spice-lst-fn (cdr lst) in-dir out-dir
                               (if erp (cons (car lst) failures) failures)
                               verbose
                               state)))
        (t (er soft 'parse-spice-lst-fn
               "Illegal arguments to parse-spice-lst-fn!"))))

(defmacro parse-spice-lst (lst in-dir out-dir &key verbose)

; Lst is a list of filenames without their .cir extensions.  Those files should
; exist in the given input directory.  Parse results are written to
; corresponding .parsed files in the given output directory.

; Arguments are NOT evaluated, so lst should not be quoted.

  (declare (xargs :guard
                  (and (string-listp lst)
                       (stringp in-dir)
                       (not (equal in-dir ""))
                       (not (eql (char in-dir (1- (length in-dir))) #\/))
                       (stringp out-dir)
                       (not (equal out-dir ""))
                       (not (eql (char out-dir (1- (length out-dir))) #\/)))))
  `(parse-spice-lst-fn ',lst ,in-dir ,out-dir nil ,verbose state))

; Initial Comments from Matt concerning the Spice parser...

; A preliminary Spice parser
; Matt Kaufmann
; Nov. 15, 2020

; A preliminary Spice parser may be found in the certifiable book
; parse-spice.lisp.  Whoever works with this may wish to recertify the
; book so that it has the user pathnames in the .cert file.

; This book successfully parses all 14 files
; ~/Sync/sf/Hunt/vwsim/Testing/*.cir, but it would be good for someone
; to do further spot-checking of the resulting files, which are in
; subdirectory results/ of the current directory.

; Some basic documentation and notes on that parser are included near
; the top of that book.

; I'd be happy for others to modify this book and then add their names
; on the second line.

; Here is a log showing both certification and runs of the utilities
; parse-spice-lst and parse-spice.  (Linebreaks were added in the include-book
; forms to avoid confusing the dependency analysis.)  Notice the two parsing
; failures.

#|
~/Dropbox/projects/vwsim/vwsim-2.8.2/parse-spice$ ~/acl2/acl2-git-scratch/sbcl-saved_acl2
This is SBCL 2.2.2, an implementation of ANSI Common Lisp.
More information about SBCL is available at <http://www.sbcl.org/>.

SBCL is free software, provided as is, with absolutely no warranty.
It is mostly in the public domain; some portions are provided under
BSD-style licenses.  See the CREDITS and COPYING files in the
distribution for more information.

 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 + ACL2 Version 8.4+ (a development snapshot based on ACL2 Version 8.4) +
 +   built April 18, 2022  03:19:05.                                    +
 +   (Git commit hash: 8ae4c5ce61d6f5e0ede4f77332f6a3a4ccee458c)        +
 + Copyright (C) 2022, Regents of the University of Texas.              +
 + ACL2 comes with ABSOLUTELY NO WARRANTY.  This is free software and   +
 + you are welcome to redistribute it under certain conditions.  For    +
 + details, see the LICENSE file distributed with ACL2.                 +
 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

System books directory "/Users/kaufmann/acl2/acl2-git-scratch/books/".
Type :help for help.
Type (quit) to quit completely out of ACL2.

ACL2 !>(include-book
 "parse-spice")

Summary
Form:  ( INCLUDE-BOOK
 "parse-spice" ...)
Rules: NIL
Time:  0.64 seconds (prove: 0.00, print: 0.00, other: 0.64)
 "/Users/kaufmann/Dropbox/projects/vwsim/vwsim-2.8.2/parse-spice/parse-spice.lisp"
ACL2 !>(time$ (parse-spice-lst ("convTest"
				"convTestNew"
				"countTest"
				"dualRailTest"
				"latchTest"
				"latchTestBB"
				"pulse-test"
				"pwl-bad-syntax-test"
				"pwl-test"
				"rc-circuit"
				"sideBoth"
				;; "sideDRsim-edit"
				"sideDRsim"
				"sin-test"
				;; "tapSide"
				"testJTLPhase"
				"testMerge"
				"transmission")
                               "~/Dropbox/projects/vwsim/vwsim-2.8.2/Testing/test-circuits/cirs" ; input directory
                               "./results-new" ; output directory
			       :verbose nil ; default
                               ))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 0.05 seconds realtime, 0.05 seconds runtime
; (11,392,432 bytes allocated).
 :SUCCESS
ACL2 !>(parse-spice "~/Sync/sf/Hunt//vwsim-1.1/Testing/flatJTLtwo.cir")
 ((:COMMENT "*** SPICE deck for cell flatJTLtwo{sch} from library flatJTL")
  (:COMMENT "*** Created on Sat Oct 12, 2019 14:57:50")
  (:COMMENT "*** Last revised on Sun Mar 01, 2020 12:35:25")
  (:COMMENT
   "*** Written on Sun Sep 13, 2020 15:52:41 by Electric VLSI Design System, version 9.08b")
  (:COMMENT "*** Layout tech: josephson, foundry NONE")
  (:COMMENT "*** UC SPICE *** , MIN_RESIST 0.0, MIN_CAPAC 0.0FF")
  ((:STATEMENT :MODEL)
   (:NAME "jmitll")
   (:TYPE "jj")
   (:LIST (:EQUAL (:NAME "rtype")
                  (:EXPR (:VALUE (:NUMBER 1 NIL))))
          (:EQUAL (:NAME "vg")
                  (:EXPR (:VALUE (:NUMBER 14/5 "mV"))))
          (:EQUAL (:NAME "cap")
                  (:EXPR (:VALUE (:NUMBER 7/100 "pF"))))
          (:EQUAL (:NAME "r0")
                  (:EXPR (:VALUE (:NUMBER 160 NIL))))
          (:EQUAL (:NAME "rN")
                  (:EXPR (:VALUE (:NUMBER 16 NIL))))
          (:EQUAL (:NAME "icrit")
                  (:EXPR (:VALUE (:NUMBER 1/10 "mA"))))))
  (:COMMENT
   "*** SUBCIRCUIT basicComp__currentSource-uAmp_175 FROM CELL basicComp:currentSource{sch}")
  ((:STATEMENT :SUBCKT)
   (:NAME "basicComp__currentSource-uAmp_175")
   (:LIST (:IO-NODE "gnd")
          (:IO-NODE "iOut")))
  ((:DEVICE :R)
   (:NAME "RR1")
   (:+NODE (:NAME "iOut"))
   (:-NODE (:NAME "net@28"))
   (:VALUE (:NUMBER 10 "k")))
  ((:DEVICE :V)
   (:NAME "Vvramp")
   (:+NODE (:NAME "net@28"))
   (:-NODE (:NAME "gnd"))
   (:NAME "pwl")
   (:LIST (:VALUE (:NUMBER 0 NIL))
          (:VALUE (:NUMBER 0 NIL))
          (:VALUE (:NUMBER 1 "p"))
          (:VALUE (:NUMBER 7/4 "V"))))
  ((:STATEMENT :ENDS)
   (:NAME "basicComp__currentSource-uAmp_175"))
  (:COMMENT "*** TOP LEVEL CELL: flatJTL:flatJTLtwo{sch}")
  ((:DEVICE :L)
   (:NAME "LL1")
   (:+NODE (:NAME "A"))
   (:-NODE (:NAME "net@3"))
   (:VALUE (:NUMBER 4 "p")))
  ((:DEVICE :L)
   (:NAME "LL2")
   (:+NODE (:NAME "net@3"))
   (:-NODE (:NAME "net@83"))
   (:VALUE (:NUMBER 2 "p")))
  ((:DEVICE :L)
   (:NAME "LL3")
   (:+NODE (:NAME "net@83"))
   (:-NODE (:NAME "B"))
   (:VALUE (:NUMBER 2 "p")))
  ((:DEVICE :R)
   (:NAME "RRP1")
   (:+NODE (:NAME "net@3"))
   (:-NODE (:NAME "gnd"))
   (:VALUE (:NUMBER 12/5 NIL)))
  ((:DEVICE :R)
   (:NAME "RRP2")
   (:+NODE (:NAME "B"))
   (:-NODE (:NAME "gnd"))
   (:VALUE (:NUMBER 12/5 NIL)))
  ((:DEVICE :X)
   (:NAME "XCS1")
   (:LIST (:NODE (:NAME "gnd"))
          (:NODE (:NAME "net@3")))
   (:SUBCIRCUIT-NAME "basicComp__currentSource-uAmp_175"))
  ((:DEVICE :X)
   (:NAME "XCS2")
   (:LIST (:NODE (:NAME "gnd"))
          (:NODE (:NAME "B")))
   (:SUBCIRCUIT-NAME "basicComp__currentSource-uAmp_175"))
  ((:DEVICE :B)
   (:NAME "BJJ1")
   (:+NODE (:NAME "net@3"))
   (:-NODE (:NAME "gnd"))
   (:NAME "jmitll")
   (:EQUAL (:NAME "area")
           (:EXPR (:VALUE (:NUMBER 5/2 NIL)))))
  ((:DEVICE :B)
   (:NAME "BJJ2")
   (:+NODE (:NAME "B"))
   (:-NODE (:NAME "gnd"))
   (:NAME "jmitll")
   (:EQUAL (:NAME "area")
           (:EXPR (:VALUE (:NUMBER 5/2 NIL)))))
  (:COMMENT
   "* Trailer cards copied from file: /Users/vivek/RSFQ/theBest01mar20-Original/aTests/Atrailer.txt")
  (:COMMENT "*** viewing stuff for vrAltMergeBothFixes")
  (:COMMENT "*** vr 6 May 2020")
  (:COMMENT "*** josim -c 1 -g -V -o Aoutput.csv vrRC-Circuit.cir")
  ((:STATEMENT :TRAN)
   (:LIST (:VALUE (:NUMBER 1/10 NIL))
          (:VALUE (:NUMBER 2 NIL))
          (:VALUE (:NUMBER 0 NIL))
          (:VALUE (:NUMBER 1/4 "p"))))
  ((:STATEMENT :PRINT)
   (:TYPE "DEVV")
   (:NAME "RR1"))
  ((:STATEMENT :PRINT)
   (:TYPE "DEVV")
   (:NAME "CC1"))
  ((:STATEMENT :PRINT)
   (:TYPE "DEVV")
   (:NAME "VVS1"))
  ((:STATEMENT :PRINT)
   (:TYPE "DEVI")
   (:NAME "RR1"))
  ((:STATEMENT :PRINT)
   (:TYPE "DEVI")
   (:NAME "CC1"))
  ((:STATEMENT :PRINT)
   (:TYPE "DEVI")
   (:NAME "VVS1"))
  (:COMMENT
   "* End of Trailer cards copied from file: /Users/vivek/RSFQ/theBest01mar20-Original/aTests/Atrailer.txt")
  ((:STATEMENT :END)))
ACL2 !>(parse-spice "../Testing/test-circuits/cirs/sideDRsim-edit.cir")


HARD ACL2 ERROR in SPLIT-AT-RIGHT-PAREN:  [Line 347] Missing right
parenthesis at level 0!



ACL2 Error in TOP-LEVEL:  Evaluation aborted.  To debug see :DOC print-
gv, see :DOC trace, and see :DOC wet.

ACL2 !>(parse-spice "../Testing/test-circuits/cirs/tapSide.cir")


HARD ACL2 ERROR in PARSE-LINE-2:  [Line 8] Implementation error: statement
type not yet handled, (:STATEMENT :OPTIONS)



ACL2 Error in TOP-LEVEL:  Evaluation aborted.  To debug see :DOC print-
gv, see :DOC trace, and see :DOC wet.

ACL2 !>(parse-spice "~/Sync/sf/Hunt/vwsim-2.8.1/Testing/test-circuits/cirs/test_ljPP4x4wave_throughput_46ps.cir")
 ((:COMMENT
   "*** SPICE deck for cell test_ljPP4x4wave_throughput{sch} from library marlyTest")
  .... finishes!
|#
