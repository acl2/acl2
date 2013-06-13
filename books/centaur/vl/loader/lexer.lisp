; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "lexer-tokens")
(include-book "lexer-utils")
(include-book "../util/warnings")
(include-book "../util/commentmap")
(local (include-book "../util/arithmetic"))



(defxdoc lexer
  :parents (loader)
  :short "Verilog Lexer."

  :long "<p>We implement a lexer for Verilog based on the IEEE 1364-2005
standard.  Our lexer is believed to be complete and should understand all
Verilog tokens.  This contrasts with our @(see preprocessor) and @(see parser),
which are not similarly complete.</p>

<p>Lexers are traditionally implemented as a @('get-token') routine, the idea
being that, at the parser's request, the lexer should read just enough from the
input stream to provide the next token.</p>

<p>In contrast, our lexer processes the whole list of input characters that are
produced by the @(see preprocessor), and generates a whole list of tokens (see
@(see vl-token-p)) as output.  These tokens will then be given to the @(see
parser).</p>

<p>Our approach is obviously inefficient.  On the other hand, memory is
abundant and lexing is almost intrinsically @('O(n)'), so we think performance
is not very important.  Our approach allows our parser to be state-free, with
arbitrary lookahead, and also gives us the convenience of list-based (rather
than file-based) debugging and unit testing throughout the whole process.</p>")


(defmacro def-token/remainder-thms (fn &key
                                       (formals '(echars))
                                       (extra-tokenhyp 't)
                                       (extra-appendhyp 't)
                                       (extra-strongcounthyp 't)
                                       (token-n '0)
                                       (remainder-n '1))
  (let ((mksym-package-symbol 'vl))
    `(encapsulate
      ()
      (local (in-theory (enable ,fn)))

      (defthm ,(mksym 'vl-token-p-of- fn)
        (implies (and (force (vl-echarlist-p echars))
                      ,extra-tokenhyp)
                 (equal (vl-token-p (mv-nth ,token-n (,fn . ,formals)))
                        (if (mv-nth ,token-n (,fn . ,formals))
                            t
                          nil))))

      (defthm ,(mksym 'true-listp-of- fn)
        (equal (true-listp (mv-nth ,remainder-n (,fn . ,formals)))
               (true-listp echars))
        :rule-classes ((:rewrite)
                       (:type-prescription
                        :corollary
                        (implies (true-listp echars)
                                 (true-listp (mv-nth ,remainder-n (,fn . ,formals))))))
        :hints(("Goal" :in-theory (disable (force)))))

      (defthm ,(mksym 'vl-echarlist-p-of- fn)
        (implies (force (vl-echarlist-p echars))
                 (equal (vl-echarlist-p (mv-nth ,remainder-n (,fn . ,formals)))
                        t)))

      (defthm ,(mksym 'append-of- fn)
        (implies (and (mv-nth ,token-n (,fn . ,formals))
                      (force (vl-echarlist-p echars))
                      ,extra-appendhyp)
                 (equal (append (vl-token->etext (mv-nth ,token-n (,fn . ,formals)))
                                (mv-nth ,remainder-n (,fn . ,formals)))
                        echars)))

      (defthm ,(mksym 'no-change-loser-of- fn)
        (implies (not (mv-nth ,token-n (,fn . ,formals)))
                 (equal (mv-nth ,remainder-n (,fn . ,formals))
                        echars)))

      (defthm ,(mksym 'acl2-count-of- fn '-weak)
        (<= (acl2-count (mv-nth ,remainder-n (,fn . ,formals)))
            (acl2-count echars))
        :rule-classes ((:rewrite) (:linear))
        :hints(("Goal" :in-theory (disable (force)))))

      (defthm ,(mksym 'acl2-count-of- fn '-strong)
        (implies (and (mv-nth ,token-n (,fn . ,formals))
                      ,extra-strongcounthyp)
                 (< (acl2-count (mv-nth ,remainder-n (,fn . ,formals)))
                    (acl2-count echars)))
        :rule-classes ((:rewrite) (:linear))
        :hints(("Goal" :in-theory (disable (force))))))))




;                         WHITESPACE AND COMMENTS
;
; From the Verilog grammar:
;
;    white_space ::= space | tab | newline | eof
;
; But Section 3.2 says whitespace also includes form feeds, and Cadence
; tolerates them.  We they have been accidentally left out of the grammar, and
; so we permit them.
;
; We do not consider EOF a character.  Instead, it the condition encountered
; when the list we are processing runs out of characters.  The only place this
; seems to matter is in our handling of escaped identifiers, where we believe
; we account for it appropriately.

(defsection whitespace

  ;; We optimize the recognition of whitespace by basically using a bitset.
  ;; This is probably silly and not worth the effort.

  (defun-inline vertical-tab-char () (code-char 11))
  (defmacro carriage-return-char () (code-char 13))

  (defmacro whitespace-mask ()
    ;; To generate this mask:
    ;; (include-book "centaur/bitops/bitsets" :dir :system)
    ;; (acl2::bitset-list (char-code #\Space)
    ;;                    (char-code #\Tab)
    ;;                    (char-code #\Page)
    ;;                    (char-code #\Newline)
    ;;                    (char-code (vertical-tab-char))
    ;;                    (char-code (carriage-return-char)))
    4294983168)

  (local (in-theory (disable logbitp)))

  ;; It isn't clear to me whether these ought to be part of the whitespace
  ;; definition, but it's probably sensible to include at least the
  ;; carriage-return character.

  (local (defun test (n)
           (and (equal (logbitp n (whitespace-mask))
                       (let ((x (code-char n)))
                         (or (eql x #\Space)
                             (eql x #\Tab)
                             (eql x #\Page)
                             (eql x #\Newline)
                             (eql x (vertical-tab-char))
                             (eql x (carriage-return-char)))))
                (or (zp n)
                    (test (- n 1))))))

  (local (defthm test-lemma
           (implies (and (test n)
                         (natp i)
                         (natp n)
                         (<= i n))
                    (equal (logbitp i (whitespace-mask))
                           (let ((x (code-char i)))
                             (or (eql x #\Space)
                                 (eql x #\Tab)
                                 (eql x #\Page)
                                 (eql x #\Newline)
                                 (eql x (vertical-tab-char))
                                 (eql x (carriage-return-char))))))
           :hints(("Goal" :induct (test n)))))

  (local (defthm test-consequence
           (implies (characterp x)
                    (equal (logbitp (char-code x) (whitespace-mask))
                           (or (eql x #\Space)
                               (eql x #\Tab)
                               (eql x #\Page)
                               (eql x #\Newline)
                               (eql x (vertical-tab-char))
                               (eql x (carriage-return-char)))))
           :hints(("Goal" :use ((:instance test-lemma
                                           (n 255)
                                           (i (char-code x))))))))

  (defchar whitespace
    (mbe :logic (or (eql x #\Space)
                    (eql x #\Tab)
                    (eql x #\Page) ;; "form feed"
                    (eql x #\Newline)
                    (eql x (vertical-tab-char))
                    (eql x (carriage-return-char)))
         :exec (logbitp (char-code x) (whitespace-mask)))))

(defchar not-whitespace
  (not (vl-whitespace-p x)))




(defund vl-lex-oneline-comment (echars)
  "Returns (MV TOKEN/NIL REMAINDER)"
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (b* (((unless (vl-matches-string-p "//" echars))
        (mv nil echars))
       ((mv & prefix remainder)
        (vl-read-through-literal *nls* (cddr echars)))
       (etext
        (list* (first echars) (second echars) prefix))
       (token (make-vl-plaintoken :etext etext :type :vl-comment)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-oneline-comment)



(defund vl-lex-block-comment (echars)
  "Returns (MV TOKEN/NIL REMAINDER)"
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (b* (((unless (vl-matches-string-p "/*" echars))
        (mv nil echars))
       ((mv successp prefix remainder)
        (vl-read-through-literal "*/" (cddr echars)))
       ((unless successp)
        (mv (cw "Lexer error (~s0): block comment is never closed.~%"
                (vl-location-string (vl-echar->loc (car echars))))
            echars))
       (etext
        (list* (first echars) (second echars) prefix))
       (token (make-vl-plaintoken :etext etext :type :vl-comment)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-block-comment)





;                             IDENTIFIERS
;
;  simple_identifier ::= [ a-zA-Z_ ] { [a-zA-Z0-9_$ ] }
;
;  escaped_identifier ::= \ { any non-whitespace character } white_space
;
;  identifier ::= simple_identifier
;               | escaped_identifier
;
;  system_function_identifier ::= $[ a-zA-Z0-9_$ ] { [ a-zA-Z0-9_$ ] }
;  system_task_identifier     ::= $[ a-zA-Z0-9_$ ] { [ a-zA-Z0-9_$ ] }


; REGARING HONS-COPY IN IDENTIFIER LEXING.  The use of hons-copy below is
; subtle.  One reason it's a good idea is that identifiers are often repeated
; many times, so making the actual string part a hons lets us use only one copy
; of the string.  The other big reason is that identifier names are often used
; in fast-alist lookups, and if the string isn't a hons, then HONS-GET will
; have to hons it first.  So, we potentially avoid a lot of repeated, redundant
; honsing later on by just honsing now.


(defmacro explicit-char-code (x)
  (declare (xargs :Guard (characterp x)))
  (char-code x))

(defchar simple-id-head

  ;; Original definition.
  ;; (or (and (char<= #\a x) (char<= x #\z))
  ;;     (and (char<= #\A x) (char<= x #\Z))
  ;;     (eql x #\_))

  ;; New definition is about 15% faster according to simple tests.
  ;; We take advantage of the ASCII ordering.  We know uppercase
  ;; comes before lowercase, and underscore is between upper and
  ;; lowercase.

  ;; (time$
  ;;  ;; 4.68 seconds with original definition,
  ;;  ;; 4.01 seconds with new definition.
  ;;  (loop for i fixnum from 1 to 1000000000 do
  ;;        (vl::vl-simple-id-head-p #\m)
  ;;        (vl::vl-simple-id-head-p #\M)
  ;;        (vl::vl-simple-id-head-p #\Space)))


  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (and (<= (explicit-char-code #\A) code)
         (<= code (explicit-char-code #\z))
         (or (<= (explicit-char-code #\a) code) ;; lower-case
             (<= code (explicit-char-code #\Z)) ;; upper-case
             (= code (explicit-char-code #\_))  ;; underscore
             ))))

(defchar simple-id-tail

  ;; Original definition.
  ;; (or (and (char<= #\a x) (char<= x #\z))
  ;;     (and (char<= #\A x) (char<= x #\Z))
  ;;     (and (char<= #\0 x) (char<= x #\9))
  ;;     (eql x #\_)
  ;;     (eql x #\$))

  ;; New definition is almost twice as fast according to simple tests.  We take
  ;; advantage of ASCII ordering.  Uppercase comes before lowercase, and
  ;; underscore is in between.  Numbers are before uppercase, and dollar is
  ;; before numbers.  We first check against upper-case A.  If it's greater, it
  ;; must be a letter or underscore.  Otherwise, it must be a number or dollar.

  ;; (time$
  ;;  ;; 7.698 seconds with original definition
  ;;  ;; 4.690 seconds with alt definition
  ;;  (loop for i fixnum from 1 to 1000000000 do
  ;;        (vl::vl-simple-id-tail-p #\m)
  ;;        (vl::vl-simple-id-tail-p #\M)
  ;;        (vl::vl-simple-id-tail-p #\Space)))

  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (if (<= (explicit-char-code #\A) code)
        ;; Must be a letter or underscore.
        (and (<= code (explicit-char-code #\z))
             (or (<= (explicit-char-code #\a) code)   ;; lowercase
                 (<= code (explicit-char-code #\Z))   ;; uppercase
                 (= code (explicit-char-code #\_))))  ;; underscore
      ;; Must be a number or dollar.
      (if (<= (explicit-char-code #\0) code)
          (<= code (explicit-char-code #\9))
        (= code (explicit-char-code #\$))))))


;; (loop for i from 0 to 255 do
;;       (let ((char (code-char i)))
;;         (format t "okp(~a) = ~a~%" i
;;                 (equal (vl::vl-simple-id-tail-p char)
;;                        (vl::vl-simple-id-tail-alt char)))))

(defthm vl-simple-id-tail-p-when-vl-simple-id-head-p
  (implies (vl-simple-id-head-p x)
           (vl-simple-id-tail-p x))
  :hints(("Goal" :in-theory (enable vl-simple-id-head-p
                                    vl-simple-id-tail-p))))




(defsection vl-read-simple-identifier

  (defund vl-read-simple-identifier (echars)
    "Returns (MV PREFIX REMAINDER)"
    (declare (xargs :guard (vl-echarlist-p echars)))
    (if (or (not (consp echars))
            (not (vl-simple-id-head-echar-p (car echars))))
        (mv nil echars)
      (vl-read-while-simple-id-tail echars)))

  (local (in-theory (enable vl-read-simple-identifier)))

  (local (defthm lemma
           (implies (vl-simple-id-head-p (vl-echar->char (first echars)))
                    (mv-nth 0 (vl-read-while-simple-id-tail echars)))
           :hints(("Goal" :in-theory (enable vl-read-while-simple-id-tail)))))

  (defthm vl-read-simple-identifier-when-vl-simple-id-head-p
    (implies (vl-simple-id-head-p (vl-echar->char (first echars)))
             (mv-nth 0 (vl-read-simple-identifier echars)))
    :hints(("Goal"
            :in-theory (e/d (vl-simple-id-head-p)
                            ((force))))))

  (def-prefix/remainder-thms vl-read-simple-identifier))




(defsection vl-read-escaped-identifier

  (defund vl-read-escaped-identifier (echars)
    "Returns (MV NAME PREFIX REMAINDER)"
    (declare (xargs :guard (vl-echarlist-p echars)))

; NAME is an ACL2 stringp on success, or nil otherwise.

; An escaped identifier includes the whitespace character which terminates it,
; but this character (and the initial backslash) are to be excluded from the
; name of the identifier.  That is, "\foo<space>", "\foo<tab>", and "foo" are
; three ways to refer to the same identifier.  Note also that the Verilog
; grammar treats EOF as a whitespace, so we allow an escaped identifier to be
; closed with EOF -- there just isn't a whitespace character at the end of the
; PREFIX in that case.

; Perhaps a reason for including this whitespace is found on page 351.  A macro
; with arguments is introduced like "`define max(a,b) ..." with no whitespace
; between its name (an identifier) and the first paren of the argument list.
; So if you wanted to have an escaped identifier as the name of a macro with
; arguments, how would you know when the identifier ended and the argument list
; began?  Making the escaped identifier include a whitespace seems like a dirty
; trick to accomplish this.  In any event, we don't support macros with
; arguments anyway, but we go ahead and include the whitespace in case such
; support is ever added.

; I have not found anything in the spec which explicitly prohibits the empty
; escaped identifier, i.e., "\<whitespace>", from being used.  Nevertheless, I
; exclude it on the grounds that is suspicious and Cadence does not permit it
; either.  Allowing it would make end-of-define even more complicated to
; properly support.

    (if (or (not (consp echars))
            (not (eql (vl-echar->char (car echars)) #\\)))
        (mv nil nil echars)
      (b* (((mv tail remainder) (vl-read-while-not-whitespace (cdr echars))))
          (cond ((not tail)
                 ;; Attempt to use the empty identifier?
                 (mv nil nil echars))

                ((not (consp remainder))
                 ;; EOF-terminated identifier
                 (mv (hons-copy (vl-echarlist->string tail)) ;; see "regarding hons-copy"
                     (cons (car echars) tail)
                     remainder))
                (t
                 ;; Regular whitespace-terminated identifier
                 (mv (hons-copy (vl-echarlist->string tail)) ;; see "regarding hons-copy"
                     (cons (car echars) (append tail (list (car remainder))))
                     (cdr remainder)))))))

  (encapsulate
   ()
   (local (defthm crock
            (implies (consp x)
                     (equal (true-listp (cdr x))
                            (true-listp x)))))

   (def-prefix/remainder-thms vl-read-escaped-identifier
     :prefix-n 1
     :remainder-n 2))

  (local (in-theory (enable vl-read-escaped-identifier)))

  (defthm stringp-of-vl-read-escaped-identifier
    (implies (force (vl-echarlist-p echars))
             (equal (stringp (mv-nth 0 (vl-read-escaped-identifier echars)))
                    (if (mv-nth 0 (vl-read-escaped-identifier echars))
                        t
                      nil))))

  (defthm vl-read-escaped-identifier-under-iff
    (iff (mv-nth 1 (vl-read-escaped-identifier echars))
         (mv-nth 0 (vl-read-escaped-identifier echars)))))



(defsection vl-read-identifier

  (defund vl-read-identifier (echars)
    "Returns (MV NAME PREFIX REMAINDER)"
    (declare (xargs :guard (vl-echarlist-p echars)))

; NAME is an ACL2 stringp which is the interpreted name of this identifier on
; success, or nil otherwise.

    (mv-let (prefix remainder)
            (vl-read-simple-identifier echars)
            (if prefix
                (mv (hons-copy (vl-echarlist->string prefix)) prefix remainder)
              (vl-read-escaped-identifier echars))))

  (def-prefix/remainder-thms vl-read-identifier
    :prefix-n 1
    :remainder-n 2)

  (local (in-theory (enable vl-read-identifier)))

  (defthm stringp-of-vl-read-identifier
    (implies (force (vl-echarlist-p echars))
             (equal (stringp (mv-nth 0 (vl-read-identifier echars)))
                    (if (mv-nth 0 (vl-read-identifier echars))
                        t
                      nil))))

  (defthm vl-read-identifier-under-iff
    (iff (mv-nth 1 (vl-read-identifier echars))
         (mv-nth 0 (vl-read-identifier echars)))))




(defund vl-lex-simple-identifier-or-keyword (echars)
  "Returns (MV TOKEN/NIL REMAINDER)"
  (declare (xargs :guard (vl-echarlist-p echars)))
  (b* (((unless (and (consp echars)
                     (vl-simple-id-head-echar-p (car echars))))
        (mv nil echars))
       ((mv prefix remainder)
        (vl-read-simple-identifier echars))
       (str     (hons-copy (vl-echarlist->string prefix)))
       (lookup  (vl-keyword-lookup str))
       (token   (if lookup
                    (make-vl-plaintoken :etext prefix :type lookup)
                  (make-vl-idtoken :etext prefix :name str))))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-simple-identifier-or-keyword)



(defund vl-lex-escaped-identifier (echars)
  "Returns (MV TOKEN/NIL REMAINDER)"
  (declare (xargs :guard (vl-echarlist-p echars)))

; Per 3.7.2, escaped identifiers cannot be keywords.  So we do not need to
; consult the keyword table.

  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\\)))
        (mv nil echars))
       ((mv name prefix remainder)
        (vl-read-escaped-identifier echars))
       ((unless name)
        (mv (cw "Lexer error (~s0): stray backslash?~%"
                (vl-location-string (vl-echar->loc (car echars))))
            echars))
       (token (make-vl-idtoken :etext prefix :name name)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-escaped-identifier)



(defund vl-lex-system-identifier (echars)
  "Returns (MV TOKEN/NIL REMAINDER)"
  (declare (xargs :guard (vl-echarlist-p echars)))
  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\$)))
        (mv nil echars))
       ((mv tail remainder)
        (vl-read-while-simple-id-tail (cdr echars)))
       ((unless tail)
        (mv (cw "Lexer error (~s0): stray dollar sign?~%"
                (vl-location-string (vl-echar->loc (car echars))))
            echars))
       (etext (cons (car echars) tail))
       (name  (hons-copy (vl-echarlist->string etext)))
       (token (make-vl-sysidtoken :etext etext :name name)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-system-identifier)






;                            STRING LITERALS
;
; Strings literals in Verilog are enclosed in "double quotes" and cannot span
; multiple lines.  They may contain the following escape sequences, outlined in
; Section 3.6.
;
;   \n          Newline
;   \t          Tab
;   \\          Backslash
;   \"          Quote
;   \ddd        Character by octal code of 1-3 digits
;
; The characters referenced by the \ddd format must be between 0 and 377, since
; 377 is octal for 255.  Any larger values are an error since they do not refer
; to a valid ASCII character.

(defsection vl-read-string-escape-sequence

  (local (defthm vl-echar-digit-value-upper-bound
           (implies (force (vl-echar-p echar))
                    (< (vl-echar-digit-value echar 8)
                       8))
           :rule-classes :linear
           :hints(("Goal" :in-theory (enable vl-echar-digit-value)))))

  (local (in-theory (enable vl-echarlist-unsigned-value
                            vl-echarlist-unsigned-value-aux)))

  (defund vl-read-string-escape-sequence (echars)
    "Returns (MV CHAR/NIL PREFIX REMAINDER)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (consp echars)
                                (equal (vl-echar->char (car echars)) #\\))))

; We assume we are reading a string literal from ECHARS and have just found a
; backslash at (CAR ECHARS).  We try to read and interpret the escape sequence
; which follows.  The CHAR we return is the ACL2 characterp indicated by this
; escape sequence on success, or nil otherwise.

    (if (not (consp (cdr echars)))
        (mv nil nil echars)
      (let ((echar1 (first echars))
            (echar2 (second echars)))
        (case (vl-echar->char echar2)
          (#\n (mv #\Newline (list echar1 echar2) (cddr echars)))
          (#\t (mv #\Tab     (list echar1 echar2) (cddr echars)))
          (#\\ (mv #\\       (list echar1 echar2) (cddr echars)))
          (#\" (mv #\"       (list echar1 echar2) (cddr echars)))
          (t
           (let ((echar3 (and (consp (cddr echars))
                              (third echars)))
                 (echar4 (and (consp (cddr echars))
                              (consp (cdddr echars))
                              (fourth echars))))
             (cond
              ((not (vl-echar-digit-value echar2 8))
               (mv (cw "Lexer error (~s0): invalid escape sequence: ~s1.~%"
                       (vl-location-string (vl-echar->loc (car echars)))
                       (vl-echarlist->string (list echar1 echar2)))
                   nil echars))
              ((or (not echar3) (not (vl-echar-digit-value echar3 8)))
               ;; One octal digit.  Cannot overflow.
               (mv (code-char (vl-echar-digit-value echar2 8))
                   (list echar1 echar2)
                   (cddr echars)))
              ((or (not echar4) (not (vl-echar-digit-value echar4 8)))
               ;; Two octal digits.  Cannot overflow.
               (mv (code-char (vl-echarlist-unsigned-value (list echar2 echar3) 8))
                   (list echar1 echar2 echar3)
                   (cdddr echars)))
              (t
               ;; Three octal digits.  We must check for overflow.
               (let ((value (vl-echarlist-unsigned-value (list echar2 echar3 echar4) 8)))
                 (if (< 255 value)
                     (mv (cw "Lexer error (~s0): invalid escape sequence: ~s1.~%"
                             (vl-location-string (vl-echar->loc (car echars)))
                             (vl-echarlist->string (list echar1 echar2 echar3 echar4)))
                         nil echars)
                   (mv (code-char value)
                       (list echar1 echar2 echar3 echar4)
                       (cddddr echars))))))))))))

  (def-prefix/remainder-thms vl-read-string-escape-sequence
    :prefix-n 1
    :remainder-n 2)

  (local (in-theory (enable vl-read-string-escape-sequence)))

  (defthm characterp-of-vl-read-string-escape-sequence
    (equal (characterp (mv-nth 0 (vl-read-string-escape-sequence echars)))
           (if (mv-nth 0 (vl-read-string-escape-sequence echars))
               t
             nil)))

  (defthm second-of-vl-read-string-escape-sequence-under-iff
    (iff (mv-nth 1 (vl-read-string-escape-sequence echars))
         (mv-nth 0 (vl-read-string-escape-sequence echars)))))



(defsection vl-read-string-aux

  (defund vl-read-string-aux (echars eacc vacc)
    "Returns (MV ERROR EACC VACC REMAINDER)"
    (declare (xargs :guard (vl-echarlist-p echars)))

; This is our main loop for reading string literals.  We accumulate the actual
; echars we read into EACC, and simultaneously accumulate their interpretations
; (as regular ACL2 characterp's) into VACC.  ERROR is nil on success, or a
; string that describes the failure reason otherwise.

    (if (not (consp echars))
        (mv "the file ends before the string is closed." eacc vacc echars)
      (let* ((echar1 (first echars))
             (char1  (vl-echar->char echar1)))
        (case char1
          (#\Newline
           (mv "the line ends before the string is closed." eacc vacc echars))
          (#\"
           (mv nil (cons echar1 eacc) vacc (rest echars)))
          (#\\
           (mv-let (char prefix remainder)
                   (vl-read-string-escape-sequence echars)
                   (if (not char)
                       (mv "the string contains an invalid escape sequence."
                           eacc vacc echars)
                     (vl-read-string-aux remainder
                                         (revappend prefix eacc)
                                         (cons char vacc)))))
          (t
           (vl-read-string-aux (cdr echars)
                               (cons echar1 eacc)
                               (cons char1 vacc)))))))

  (local (in-theory (enable vl-read-string-aux)))

  (defthm stringp-of-vl-read-string-aux
    (equal (stringp (mv-nth 0 (vl-read-string-aux echars eacc vacc)))
           (if (mv-nth 0 (vl-read-string-aux echars eacc vacc))
               t
             nil)))

  (defthm vl-echarlist-p-of-vl-read-string-aux
    (implies (and (force (vl-echarlist-p echars))
                  (force (vl-echarlist-p eacc)))
             (vl-echarlist-p (mv-nth 1 (vl-read-string-aux echars eacc vacc)))))

  (defthm true-listp-of-vl-read-string-aux-vacc
    (equal (true-listp (mv-nth 1 (vl-read-string-aux echars eacc vacc)))
           (true-listp eacc)))

  (defthm character-listp-of-vl-read-string-aux-eacc
    (implies (and (force (vl-echarlist-p echars))
                  (force (character-listp vacc)))
             (character-listp (mv-nth 2 (vl-read-string-aux echars eacc vacc)))))

  (defthm vl-echarlist-p-of-vl-read-string-aux-remadiner
    (implies (force (vl-echarlist-p echars))
             (vl-echarlist-p (mv-nth 3 (vl-read-string-aux echars eacc vacc)))))

  (defthm true-listp-of-vl-read-string-aux-remainder
    (equal (true-listp (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
           (true-listp echars)))

  (defthm revappend-of-vl-read-string-aux
    (equal (append (rev (mv-nth 1 (vl-read-string-aux echars eacc vacc)))
                   (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
           (append (rev eacc)
                   echars)))

  (defthm acl2-count-of-vl-read-string-aux-weak
    (<= (acl2-count (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-vl-read-string-aux-strong
    (implies (not (mv-nth 0 (vl-read-string-aux echars eacc vacc)))
             (< (acl2-count (mv-nth 3 (vl-read-string-aux echars eacc vacc)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable (force))))))




(defsection vl-read-string

  (defund vl-read-string (echars)
    "Returns (MV STRING/NIL PREFIX REMAINDER)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (consp echars)
                                (equal (vl-echar->char (car echars)) #\"))))

; We assume ECHARS begins with a double-quote character that starts a string
; literal.  STRING is an ACL2 stringp object which holds the expansion of this
; string's characters (that is, STRING will contain #\Newline instead of the
; sequence \n, etc.) on success, or nil otherwise.

    (mv-let (err eacc vacc remainder)
            (vl-read-string-aux (cdr echars) nil nil)
            (if err
                (mv (cw "Lexer error (~s0) while reading string: ~s1.~%"
                        (vl-location-string (vl-echar->loc (car echars)))
                        err)
                    nil echars)
              (mv (str::rchars-to-string vacc)
                  (cons (car echars) (reverse eacc))
                  remainder))))

  (encapsulate
   ()
   (local (in-theory (disable character-listp-of-vl-read-string-aux-eacc)))
   (def-prefix/remainder-thms vl-read-string
     :prefix-n 1
     :remainder-n 2))

  (local (in-theory (enable vl-read-string)))

  (defthm stringp-of-vl-read-string
    (equal (stringp (mv-nth 0 (vl-read-string echars)))
           (if (mv-nth 0 (vl-read-string echars))
               t
             nil)))

  (defthm second-of-vl-read-string-under-iff
    (iff (mv-nth 1 (vl-read-string echars))
         (mv-nth 0 (vl-read-string echars)))))



(defund vl-lex-string (echars)
  "Returns (MV TOKEN/NIL REMAINDER)"
  (declare (xargs :guard (vl-echarlist-p echars)))
  (b* (((unless (and (consp echars)
                     (eql (vl-echar->char (car echars)) #\")))
        (mv nil echars))
       ((mv string prefix remainder)
        (vl-read-string echars))
       ((unless string)
        (mv nil echars))
       (token (make-vl-stringtoken :etext prefix :expansion string)))
      (mv token remainder)))

(def-token/remainder-thms vl-lex-string)





;                              NUMBERS
;
; Verilog's numbers are quite complicated.  We begin working through the
; grammar for them "from the bottom up."
;
; z_digit ::= z | Z | ?
;
; x_digit ::= x | X
;
; hex_digit ::=
;     x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
;   | a | b | c | d | e | f | A | B | C | D | E | F
;
; octal_digit ::= x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
;
; binary_digit ::= x_digit | z_digit | 0 | 1
;
; decimal_digit ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
;
; non_zero_decimal_digit ::= 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9

(defchar z-digit
  (or (eql x #\z)
      (eql x #\Z)
      (eql x #\?)))

(defchar x-digit
  (or (eql x #\x)
      (eql x #\X)))

(defchar hex-digit
  ;; Original definition.
  ;; (or (vl-x-digit-p x)
  ;;     (vl-z-digit-p x)
  ;;     (and (char<= #\0 x) (char<= x #\9))
  ;;     (and (char<= #\a x) (char<= x #\f))
  ;;    (and (char<= #\A x) (char<= x #\F)))

  ;; New definition takes advantage of the fact that in ASCII, the digits
  ;; come before ? or letters, and tries to optimize for numbers.
  (if (char<= x #\9)
      (char<= #\0 x)
    (or (and (char<= #\a x) (char<= x #\f))
        (and (char<= #\A x) (char<= x #\F))
        (vl-x-digit-p x)
        (vl-z-digit-p x))))

(defchar octal-digit
  ;; Original definition.
  ;; (or (vl-x-digit-p x)
  ;;     (vl-z-digit-p x)
  ;;     (and (char<= #\0 x) (char<= x #\7)))
  ;;
  ;; New definition takes advantage of the fact that in ASCII, the digits come
  ;; before ? or letters.
  (if (char<= x #\7)
      (char<= #\0 x)
    (or (vl-x-digit-p x)
        (vl-z-digit-p x))))

(defchar binary-digit
  (or (eql x #\0)
      (eql x #\1)
      (vl-x-digit-p x)
      (vl-z-digit-p x)))

(defchar decimal-digit
  (and (char<= #\0 x)
       (char<= x #\9)))

(defchar non-zero-decimal-digit
  (and (char<= #\1 x)
       (char<= x #\9)))




; Embedded spaces are prohibited in the following productions.
;
; hex_base ::= '[s|S]h | '[s|S]H
;
; octal_base ::= '[s|S]o | '[s|S]O
;
; binary_base ::= '[s|S]b | '[s|S]B
;
; decimal_base ::= '[s|S]d | '[s|S]D

(definlined vl-read-hex-base (echars)
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (vl-read-some-literal (list "'h" "'H" "'sh" "'sH" "'Sh" "'SH") echars))

(def-prefix/remainder-thms vl-read-hex-base)


(definlined vl-read-octal-base (echars)
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (vl-read-some-literal (list "'o" "'O" "'so" "'sO" "'So" "'SO") echars))

(def-prefix/remainder-thms vl-read-octal-base)


(definlined vl-read-binary-base (echars)
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (vl-read-some-literal (list "'b" "'B" "'sb" "'sB" "'Sb" "'SB") echars))

(def-prefix/remainder-thms vl-read-binary-base)


(definlined vl-read-decimal-base (echars)
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (vl-read-some-literal (list "'d" "'D" "'sd" "'sD" "'Sd" "'SD") echars))

(def-prefix/remainder-thms vl-read-decimal-base)


(definlined vl-read-any-base (echars)
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (vl-orcar-mv2s (vl-read-hex-base echars)
                 (vl-read-octal-base echars)
                 (vl-read-binary-base echars)
                 (vl-read-decimal-base echars)))

(def-prefix/remainder-thms vl-read-any-base)





; Embedded spaces are also prohibited in the following productions.
;
; hex_value ::= hex_digit { _ | hex_digit }
;
; octal_value ::= octal_digit { _ | octal_digit }
;
; binary_value ::= binary_digit { _ | binary_digit }
;
; unsigned_number ::= decimal_digit { _ | decimal_digit }
;
; non_zero_unsigned_number ::= non_zero_decimal_digit { _ | decimal_digit }

(defchar underscore-or-hex-digit
  (or (vl-hex-digit-p x)
      (eql x #\_)))

(defchar underscore-or-octal-digit
  (or (vl-octal-digit-p x)
      (eql x #\_)))

(defchar underscore-or-binary-digit
  (or (vl-binary-digit-p x)
      (eql x #\_)))

(defchar underscore-or-decimal-digit
  (or (vl-decimal-digit-p x)
      (eql x #\_)))


(definlined vl-read-hex-value (echars)
  (declare (xargs :guard (vl-echarlist-p echars)))
  (if (or (not (consp echars))
          (not (vl-hex-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-hex-digit echars)))

(def-prefix/remainder-thms vl-read-hex-value)


(definlined vl-read-octal-value (echars)
  (declare (xargs :guard (vl-echarlist-p echars)))
  (if (or (not (consp echars))
          (not (vl-octal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-octal-digit echars)))

(def-prefix/remainder-thms vl-read-octal-value)


(definlined vl-read-binary-value (echars)
  (declare (xargs :guard (vl-echarlist-p echars)))
  (if (or (not (consp echars))
          (not (vl-binary-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-binary-digit echars)))

(def-prefix/remainder-thms vl-read-binary-value)


(definlined vl-read-unsigned-number (echars)
  (declare (xargs :guard (vl-echarlist-p echars)))
  (if (or (not (consp echars))
          (not (vl-decimal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-decimal-digit echars)))

(def-prefix/remainder-thms vl-read-unsigned-number)


(definlined vl-read-non-zero-unsigned-number (echars)
  (declare (xargs :guard (vl-echarlist-p echars)))
  (if (or (not (consp echars))
          (not (vl-non-zero-decimal-digit-echar-p (car echars))))
      (mv nil echars)
    (vl-read-while-underscore-or-decimal-digit echars)))

(def-prefix/remainder-thms vl-read-non-zero-unsigned-number)





; Embedded spaces are not permitted in real numbers, either.
;
;   sign ::= + | -
;
;   exp ::= e | E
;
;   real_number ::=
;      unsigned_number . unsigned_number
;    | unsigned_number [ . unsigned_number ] exp [ sign ] unsigned_number

(defund vl-read-real-number (echars)
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars))))
  (b* (((mv prefix-intpart   rem1) (vl-read-unsigned-number echars))
       ((mv prefix-dot       rem1) (vl-read-literal "." rem1))
       ((mv prefix-fracpart  rem1) (vl-read-unsigned-number rem1))
       ((mv prefix-exp       rem2) (vl-read-some-literal '("e" "E") rem1))
       ((mv prefix-sign      rem2) (vl-read-some-literal '("+" "-") rem2))
       ((mv prefix-exppart   rem2) (vl-read-unsigned-number rem2)))
      (cond ((and prefix-intpart
                  prefix-dot
                  prefix-fracpart
                  (not prefix-exp))
             ;; Production 1.
             (mv (append prefix-intpart prefix-dot prefix-fracpart)
                 rem1))
            ((and prefix-intpart
                  prefix-exp
                  prefix-exppart)
             ;; Production 2.
             (mv (append prefix-intpart prefix-dot  prefix-fracpart
                         prefix-exp     prefix-sign prefix-exppart)
                 rem2))
            (t
             (mv nil echars)))))

(def-prefix/remainder-thms vl-read-real-number)




; Note that spaces are permitted between the sizes, bases, and values of the
; following productions.
;
; size ::= non_zero_unsigned_number
;
; hex_number ::= [size] hex_base hex_value
;
; octal_number ::= [size] octal_base octal_value
;
; binary_number ::= [size] binary_base binary_value
;
; decimal_number ::=
;       unsigned_number
;     | [size] decimal_base unsigned_number
;     | [size] decimal_base x_digit { _ }
;     | [size] decimal_base z_digit { _ }
;
; number ::=
;       decimal_number
;     | octal_number
;     | binary_number
;     | hex_number
;     | real_number

(defchar underscore
  (eql x #\_))



(defund vl-read-decimal-value (echars)
  "Returns (MV PREFIX REMAINDER)"
  (declare (xargs :guard (vl-echarlist-p echars)))

; This is not part of the Verilog grammar.  But we think of introducing
; decimal_value as follows:
;
;   decimal_value ::= unsigned_number
;                   | x_digit { _ }
;                   | z_digit { _ }
;
; In other words, this is anything that can follow a decimal_base in the
; decimal_number production.

  (cond ((not (consp echars))
         (mv nil echars))
        ((or (vl-x-digit-echar-p (car echars))
             (vl-z-digit-echar-p (car echars)))
         (mv-let (prefix remainder)
                 (vl-read-while-underscore (cdr echars))
                 (mv (cons (car echars) prefix) remainder)))
        (t
         (vl-read-unsigned-number echars))))

(def-prefix/remainder-thms vl-read-decimal-value)



(defund vl-binary-digits-to-bitlist (digits)
  "MSB-First Binary Digits --> MSB-First Bitlist"
  (declare (xargs :guard (character-listp digits)))
  (if (consp digits)
      (cons (case (car digits)
              (#\0           :vl-0val)
              (#\1           :vl-1val)
              ((#\x #\X)     :vl-xval)
              ((#\z #\Z #\?) :vl-zval)
              (otherwise
               (prog2$ (er hard? 'vl-binary-digits-to-bitlist
                           "Not a binary digit: ~x0.~%" (car digits))
                       :vl-0val)))
            (vl-binary-digits-to-bitlist (cdr digits)))
    nil))

(defund vl-octal-digits-to-bitlist (digits)
  "MSB-First Octal Digits --> MSB-First Bitlist"
  (declare (xargs :guard (character-listp digits)))
  (if (consp digits)
      (append (case (car digits)
                (#\0           (list :vl-0val :vl-0val :vl-0val))
                (#\1           (list :vl-0val :vl-0val :vl-1val))
                (#\2           (list :vl-0val :vl-1val :vl-0val))
                (#\3           (list :vl-0val :vl-1val :vl-1val))
                (#\4           (list :vl-1val :vl-0val :vl-0val))
                (#\5           (list :vl-1val :vl-0val :vl-1val))
                (#\6           (list :vl-1val :vl-1val :vl-0val))
                (#\7           (list :vl-1val :vl-1val :vl-1val))
                ((#\x #\X)     (list :vl-xval :vl-xval :vl-xval))
                ((#\z #\Z #\?) (list :vl-zval :vl-zval :vl-zval))
                (otherwise
                 (prog2$ (er hard? 'vl-octal-digits-to-bitlist
                             "Not an octal digit: ~x0.~%" (car digits))
                         (list :vl-0val :vl-0val :vl-0val))))
              (vl-octal-digits-to-bitlist (cdr digits)))
    nil))

(defund vl-decimal-digits-to-bitlist (digits)
  (declare (xargs :guard (character-listp digits)))
  ;; The only time this should be called is if digits is a singleton list
  ;; containing exactly the digit x or z.
  (cond ((member-equal digits (list '(#\x)
                                    '(#\X)))
         (list :vl-xval))
        ((member-equal digits (list '(#\z)
                                    '(#\Z)
                                    '(#\?)))
         (list :vl-zval))
        (t
         (prog2$
          (er hard? 'vl-decimal-digits-to-bitlist "Programming error")
          (list :vl-xval)))))

(defund vl-hex-digits-to-bitlist (digits)
  "MSB-First Digits --> MSB-First Bitlist"
  (declare (xargs :guard (character-listp digits)))
  (if (consp digits)
      (append (case (car digits)
                (#\0           (list :vl-0val :vl-0val :vl-0val :vl-0val))
                (#\1           (list :vl-0val :vl-0val :vl-0val :vl-1val))
                (#\2           (list :vl-0val :vl-0val :vl-1val :vl-0val))
                (#\3           (list :vl-0val :vl-0val :vl-1val :vl-1val))
                (#\4           (list :vl-0val :vl-1val :vl-0val :vl-0val))
                (#\5           (list :vl-0val :vl-1val :vl-0val :vl-1val))
                (#\6           (list :vl-0val :vl-1val :vl-1val :vl-0val))
                (#\7           (list :vl-0val :vl-1val :vl-1val :vl-1val))
                (#\8           (list :vl-1val :vl-0val :vl-0val :vl-0val))
                (#\9           (list :vl-1val :vl-0val :vl-0val :vl-1val))
                ((#\A #\a)     (list :vl-1val :vl-0val :vl-1val :vl-0val))
                ((#\B #\b)     (list :vl-1val :vl-0val :vl-1val :vl-1val))
                ((#\C #\c)     (list :vl-1val :vl-1val :vl-0val :vl-0val))
                ((#\D #\d)     (list :vl-1val :vl-1val :vl-0val :vl-1val))
                ((#\E #\e)     (list :vl-1val :vl-1val :vl-1val :vl-0val))
                ((#\F #\f)     (list :vl-1val :vl-1val :vl-1val :vl-1val))
                ((#\x #\X)     (list :vl-xval :vl-xval :vl-xval :vl-xval))
                ((#\z #\Z #\?) (list :vl-zval :vl-zval :vl-zval :vl-zval))
                (otherwise
                 (prog2$ (er hard? 'vl-hex-digits-to-bitlist
                             "Not a hex digit: ~x0.~%" (car digits))
                         (list :vl-0val :vl-0val :vl-0val :vl-0val))))
              (vl-hex-digits-to-bitlist (cdr digits)))
    nil))

(defthm vl-bitlist-p-of-vl-binary-digits-to-bitlist
  (implies (force (character-listp digits))
           (vl-bitlist-p (vl-binary-digits-to-bitlist digits)))
  :hints(("Goal" :in-theory (enable vl-binary-digits-to-bitlist))))

(defthm vl-bitlist-p-of-vl-octal-digits-to-bitlist
  (implies (force (character-listp digits))
           (vl-bitlist-p (vl-octal-digits-to-bitlist digits)))
  :hints(("Goal" :in-theory (enable vl-octal-digits-to-bitlist))))

(defthm vl-bitlist-p-of-vl-decimal-digits-to-bitlist
  (implies (force (character-listp digits))
           (vl-bitlist-p (vl-decimal-digits-to-bitlist digits)))
  :hints(("Goal" :in-theory (enable vl-decimal-digits-to-bitlist))))

(defthm vl-bitlist-p-of-vl-hex-digits-to-bitlist
  (implies (force (character-listp digits))
           (vl-bitlist-p (vl-hex-digits-to-bitlist digits)))
  :hints(("Goal" :in-theory (enable vl-hex-digits-to-bitlist))))

(defthm len-of-vl-binary-digits-to-bitlist
  (equal (len (vl-binary-digits-to-bitlist x))
         (len x))
  :hints(("Goal" :in-theory (enable vl-binary-digits-to-bitlist))))

(defthm len-of-vl-octal-digits-to-bitlist
  (equal (len (vl-octal-digits-to-bitlist x))
         (* 3 (len x)))
  :hints(("Goal" :in-theory (enable vl-octal-digits-to-bitlist))))

(defthm len-of-vl-decimal-digits-to-bitlist
  (equal (len (vl-decimal-digits-to-bitlist x))
         1)
  :hints(("Goal" :in-theory (enable vl-decimal-digits-to-bitlist))))

(defthm len-of-vl-hex-digits-to-bitlist
  (equal (len (vl-hex-digits-to-bitlist x))
         (* 4 (len x)))
  :hints(("Goal" :in-theory (enable vl-hex-digits-to-bitlist))))



(defsection vl-correct-bitlist
  :parents (lexer)
  :short "Extend (or truncate) a bit-list to match the size specifier for an
integer token."

  :long "<p><b>Signature:</b> @(call vl-correct-bitlist) returns @('(mv
warnings' bits')').</p>

<p>@('bits') is a bitlist which might be shorter or longer than @('width'),
which is the size specified for this integer or is @('nil') if no size was
specified.  For instance, the user may have written @('3'bx') instead of
@('3'bxxx').</p>

<p>Our goal is to produce a new list of bits that has the desired width.  Note
that we emulate a 32-bit Verilog implementation and treat unsized numbers as
having width 32.</p>

<p>The rules for extending or truncating are given in 3.5.1:</p>

<ul>

<li>If bits is shorter than width, we are usually supposed to zero-extend them.
However, when the most significant bit is X or Z, we are instead supposed to
X-extend or Z-extend, respectively.  (The specification notes that in
Verilog-1995, unsized constants whose high-order bit was X or Z were only
extended to 32 bits, so we detect and warn about this case.)</li>

<li>If bits is longer than width, we are to truncate it from the left, keeping
the least significant width-many bits.  We produce a truncation warning in this
case.</li>

</ul>"

  (defund vl-correct-bitlist (loc bits width warnings)
    "Returns (MV WARNINGS' BITS')"
    (declare (xargs :guard (and (vl-location-p loc)
                                (vl-bitlist-p bits)
                                (vl-maybe-posp width))))
    (b* ((actual-len  (len bits))
         (unsizedp    (not width))
         (desired-len (if width
                          (lnfix width)
                        32))

         ((when (= actual-len 0))
          ;; BOZO could probably prove this never happens
          (er hard? 'vl-maybe-widen-bitlist "Expected at least one bit.")
          (mv warnings (repeat :vl-0val desired-len)))

         (pad-bit (case (car bits)
                    (:vl-zval :vl-zval)
                    (:vl-xval :vl-xval)
                    (otherwise :vl-0val)))

         (warnings (if (and unsizedp
                            (or (eq pad-bit :vl-xval)
                                (eq pad-bit :vl-zval)))
                       (cons (make-vl-warning
                              :type :vl-warn-incompatible
                              :msg "~l0: unsized numbers with leading X or Z ~
                                    bit have a different interpretation in ~
                                    Verilog-1995 than in Verilog-2001 and ~
                                    beyond.  You may wish to use an explicit ~
                                    size specifier on this number."
                              :args (list loc)
                              :fn 'vl-correct-bitlist)
                             warnings)
                     warnings))

         ((when (= desired-len actual-len))
          ;; Nothing to do
          (mv warnings bits))

         ((when (< desired-len actual-len))
          (b* ((msg "~l0: implicitly truncating ~s1 from ~x2 to ~x3 bits.")
               (msg (if unsizedp
                        (cat msg "  Note that this truncation emulates a ~
                                  32-bit Verilog implementation, and that on ~
                                  a 64-bit system a different value could be ~
                                  produced.  We strongly recommend adding an ~
                                  explicit size specifier.")
                      msg))
               (bitstr (vl-bitlist->string bits))
               (w (make-vl-warning
                   :type :vl-warn-overflow
                   :msg msg
                   :args (list loc bitstr actual-len desired-len)
                   :fn 'vl-correct-bitlist))
               (bits-prime (nthcdr (- actual-len desired-len)
                                   (redundant-list-fix bits)))
               (warnings
                (if (all-equalp :vl-xval bits)
                    ;; We suppress the truncation warning when all of the bits
                    ;; are X, because we often run into 29'h XXXX_XXXX or similar,
                    ;; and while perhaps {29{1'bX}} would be a better way to write
                    ;; it, the XXXX_XXXX form seems pretty legitimate, too.
                    warnings
                  (cons w warnings))))
            (mv warnings bits-prime)))

         ;; Else, desired-len > actual-len
         (pad        (repeat pad-bit (- desired-len actual-len)))
         (bits-prime (append pad bits)))

      (mv warnings bits-prime)))

  (defthm vl-bitlist-p-of-vl-correct-bitlist
    (implies (force (vl-bitlist-p bits))
             (vl-bitlist-p (mv-nth 1 (vl-correct-bitlist loc bits width warnings))))
    :hints(("Goal" :in-theory (enable vl-correct-bitlist))))

  (defthm len-of-vl-correct-bitlist
    (equal (len (mv-nth 1 (vl-correct-bitlist loc bits width warnings)))
           (if width
               (nfix width)
             32))
    :hints(("Goal" :in-theory (enable vl-correct-bitlist))))

  (defthm vl-warninglist-p-of-vl-correct-bitlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-correct-bitlist loc bits width warnings))))
    :hints(("Goal" :in-theory (enable vl-correct-bitlist))))

  (local
   (encapsulate
     ()

     ;; Basic extension test with a fixed width
     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "0111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "00000111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "1111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "00001111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "x111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "XXXXX111"))))

     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "z111"))
                                        8
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits) "ZZZZZ111"))))


     (assert! (b* (((mv warn bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "110111"))
                                        4
                                        nil)))
                (and (consp warn)
                     (equal (vl-bitlist->string bits) "0111"))))

     (assert! (b* (((mv warn ?bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "0111"))
                                        nil
                                        nil)))
                (and (not warn)
                     (equal (vl-bitlist->string bits)
                            (implode (append (repeat #\0 29)
                                             (repeat #\1 3)))))))

     (assert! (b* (((mv warn ?bits)
                    (vl-correct-bitlist *vl-fakeloc*
                                        (vl-binary-digits-to-bitlist (explode "Z111"))
                                        nil
                                        nil)))
                (and (consp warn)
                     (equal (vl-bitlist->string bits)
                            (implode (append (repeat #\Z 29)
                                             (repeat #\1 3))))))))))



(defsection vl-lex-integer

  (definlined vl-oct-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\o base)
               (member #\O base))))

  (definlined vl-signed-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\s base)
               (member #\S base))))

  (definlined vl-hex-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\h base)
               (member #\H base))))

  (definlined vl-dec-basep (base)
    (declare (xargs :guard (character-listp base)))
    (consp (or (member #\d base)
               (member #\D base))))

  (definlined vl-base-to-radix (base)
    (declare (xargs :guard (character-listp base)))
    (cond ((vl-hex-basep base) 16)
          ((vl-dec-basep base) 10)
          ((vl-oct-basep base) 8)
          (t 2)))

  (defthm vl-base-to-radix-upper
    (<= (vl-base-to-radix base) 16)
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable vl-base-to-radix))))

  (defthm vl-base-to-radix-lower
    (<= 2 (vl-base-to-radix base))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable vl-base-to-radix))))




  (defund vl-lex-integer (echars warnings)
    "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-warninglist-p warnings))
                    :verify-guards nil))
    (b* ( ;; An integer token might begin with:
         ;;
         ;;  1. a regular unsigned number (which could be a size specifier or the actual
         ;;     value for a plain decimal constant), or
         ;;
         ;;  2. with a base specifier like 'sd (for unsized but based numbers)
         ;;
         ;; We first try to read any numeric portion of echars into NUMBER.
         ;; When there is no number, REMAINDER1 == ECHARS and NUMBER == NIL.
         ((mv number remainder1) (vl-read-unsigned-number echars))

         ;; Interpret NUMBER if it exists.  If there is no number,
         ;; value-of-number will become NIL.
         (normalized-number      (vl-echarlist-kill-underscores number))
         (value-of-number        (vl-echarlist-unsigned-value normalized-number 10))

         ;; Now try to read the base specifier, if it exists.  If not,
         ;; REMAINDER2 will be REMAINDER1.
         ((mv ws remainder2)     (vl-read-while-whitespace remainder1))
         ((mv base remainder2)   (vl-read-any-base remainder2))

         ((when (and (not number) (not base)))
          ;; If there is not a plain unsigned number or a base, then this is
          ;; not an integer at all, so we fail.
          (mv nil echars warnings))

         (firstchar (if number (car number) (car base)))

         ((when (and number (not value-of-number)))
          ;; Sanity check.  We could try to prove this away, but to do so we'd
          ;; have to reason about vl-read-unsigned-number, and that just seems
          ;; like a lot of work.
          (mv (er hard? 'vl-lex-integer
                  "Lexer error (~s0): thought this was impossible; cannot ~
                  interpret ~s1 as a number."
                  (vl-location-string (vl-echar->loc firstchar))
                  (vl-echarlist->string number))
              echars
              warnings))

         ((when (not base))
          ;; We know there is a NUMBER because otherwise we failed above.  So,
          ;; there is a number and no base, which means this is a plain decimal
          ;; number with no X or Z digits.  This should become a signed,
          ;; base-10 integer whose width is implementation dependent.  We treat
          ;; it as a 32-bit number.
          (b* ((val-fix (mod value-of-number (expt 2 32)))
               (warnings
                (cond ((< value-of-number (expt 2 31))
                       warnings)
                      ((< value-of-number (expt 2 32))
                       (cons (make-vl-warning
                              :type :vl-warn-overflow
                              :msg "~l0: the plain number ~s1 is in [2^31, ~
                                    2^32); it will be considered a negative ~
                                    number by 32-bit Verilog implementations, ~
                                    but will be positive on 64-bit systems ~
                                    and beyond.  We recommend adding a size ~
                                    specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number))
                              :fn 'vl-lex-integer)
                             warnings))
                      (t
                       (cons (make-vl-warning
                              :type :vl-warn-overflow
                              :msg "~l0: the plain number ~s1 is over 2^32; ~
                                    we truncate it to ~x2 to emulate a 32-bit ~
                                    Verilog implementation.  But this number ~
                                    will have a different value on 64-bit ~
                                    systems and beyond.  We strongly suggest ~
                                    adding a size specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number)
                                          val-fix)
                              :fn 'vl-lex-integer)
                             warnings))))
               (token (make-vl-inttoken :etext number
                                        :width 32
                                        :signedp t
                                        :value val-fix
                                        :bits nil
                                        :wasunsized t)))
            (mv token remainder1 warnings)))

         ;; Otherwise there is a base.  This means that if there is a NUMBER,
         ;; it is the size specifier.

         ((when (and number (equal value-of-number 0)))
          ;; It's illegal to have a width of zero.  After reading the grammar,
          ;; we believe it is never allowed for two numbers to follow one
          ;; another when separated only by whitespace.  So there is no way to
          ;; parse this, and we are justified in causing an error rather than
          ;; returning number as its own inttoken.
          (mv (cw "Lexer error (~s0): found a number whose size is zero.~%"
                  (vl-location-string (vl-echar->loc firstchar)))
              echars
              warnings))

         (unsizedp (not number))
         (width    (or value-of-number 32))

         ;; The signedness and radix are determined by the base.
         (chars-of-base  (vl-echarlist->chars base))
         (signedp        (vl-signed-basep chars-of-base))
         (radix          (vl-base-to-radix chars-of-base))

         ;; Now we need to read the rest of the number.  There can be some
         ;; whitespace before the value.
         ((mv ws2 remainder2)
          (vl-read-while-whitespace remainder2))

         ;; Read the value...
         ((mv edigits remainder2)
          (case radix
            (16        (vl-read-hex-value remainder2))
            (10        (vl-read-decimal-value remainder2))
            (8         (vl-read-octal-value remainder2))
            (otherwise (vl-read-binary-value remainder2))))

         (etext (append number ws base ws2 edigits))

         ;; Before we try to interpret the value, we first clean up the digits
         ;; by removing any underscore characters.

         (normalized-edigits (vl-echarlist-kill-underscores edigits))

         ;; Now we try to interpret the value.  We won't be able to compute a
         ;; value if there are z's or x's, but in that case
         ;; vl-echarlist-unsigned-value returns nil, which is the "value" we
         ;; want to use anyway.
         (value (vl-echarlist-unsigned-value normalized-edigits radix))

         ((when value)
          ;; If there was a value, then just check to make sure it is in range
          ;; for this width and build an inttoken.
          (b* ((val-fix (mod value (expt 2 width)))
               (token   (make-vl-inttoken :etext etext
                                          :width width
                                          :signedp signedp
                                          :value val-fix
                                          :bits nil
                                          :wasunsized unsizedp))
               (warnings
                ;; Truncation warnings.
                (cond ((not unsizedp)
                       (if (= value val-fix)
                           warnings
                         (cons (make-vl-warning
                                :type :vl-warn-overflow
                                :msg "~l0: the number ~s1 is not within the ~
                                      range [0, 2^~x2) indicated by its size, ~
                                      and is being truncated to ~x2 bits, ~
                                      yielding ~x3."
                                :args (list (vl-echar->loc firstchar)
                                            value
                                            width
                                            val-fix)
                                :fn 'vl-lex-integer)
                               warnings)))
                      ((< value (expt 2 31))
                       warnings)
                      ((and signedp (< value (expt 2 32)))
                       (cons (make-vl-warning
                              :type :vl-warn-overflow
                              :msg "~l0: the unsized, signed number ~s1 is in ~
                                    [2^31, 2^32); it will be considered a ~
                                    negative number by 32-bit Verilog ~
                                    implementations, but will be positive on ~
                                    64-bit systems and beyond.  We recommend ~
                                    adding a size specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number))
                              :fn 'vl-lex-integer)
                             warnings))
                      ((< value (expt 2 32))
                       warnings)
                      (t
                       (cons (make-vl-warning
                              :type :v-warn-overflow
                              :msg "~l0: the unsized number ~s1 is over 2^32; ~
                                    we truncate it to ~x2 to emulate a 32-bit ~
                                    Verilog implementation.  But this number ~
                                    will have a different value on 64-bit ~
                                    systems and beyond.  We strongly suggest ~
                                    adding a size specifier to this number."
                              :args (list (vl-echar->loc firstchar)
                                          (vl-echarlist->string number)
                                          val-fix)
                              :fn 'vl-lex-integer)
                             warnings)))))
            (mv token remainder2 warnings)))

         ;; Otherwise, we weren't able to interpret the normalized edigits as a
         ;; number.  The number might still be valid, but just contain X or Z
         ;; characters.
         (digits (vl-echarlist->chars normalized-edigits))
         (bits   (case radix
                   (16        (vl-hex-digits-to-bitlist digits))
                   (10        (vl-decimal-digits-to-bitlist digits))
                   (8         (vl-octal-digits-to-bitlist digits))
                   (otherwise (vl-binary-digits-to-bitlist digits))))
         ((unless bits)
          ;; There aren't even any bits?
          (mv (cw "Lexer error (~s0): invalid number: ~s1.~%"
                  (vl-location-string (vl-echar->loc firstchar))
                  (vl-echarlist->string etext))
              echars
              warnings))

         ((mv warnings bits)
          (vl-correct-bitlist (vl-echar->loc firstchar)
                              bits
                              value-of-number
                              warnings))
         (token (make-vl-inttoken :etext etext
                                  :width width
                                  :signedp signedp
                                  :value value
                                  :bits bits
                                  :wasunsized unsizedp)))
      (mv token remainder2 warnings)))

  (local (in-theory (enable vl-inttoken-constraint-p)))
  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (verify-guards vl-lex-integer)

  (with-output
   :gag-mode :goals
   (def-token/remainder-thms vl-lex-integer
     :formals (echars warnings)))

  (defthm vl-warninglist-p-of-vl-lex-integer
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 2 (vl-lex-integer echars warnings))))
    :hints(("Goal" :in-theory (enable vl-lex-integer)))))



(definlined vl-lex-number (echars warnings)
  "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars)
                              (vl-warninglist-p warnings))))

; This routine finds either a real number or an integer.  We always check for
; real numbers first, because vl-lex-integer could be fooled into thinking,
; that a real number was just an integer with some other stuff following it,
; e.g., it will give you "3" when you try to parse "3.4".

  (mv-let (prefix remainder)
          (vl-read-real-number echars)
          (if prefix
              (mv (make-vl-realtoken :etext prefix)
                  remainder
                  warnings)
            (vl-lex-integer echars warnings))))

(def-token/remainder-thms vl-lex-number
  :formals (echars warnings))

(defthm vl-warninglist-p-of-vl-lex-number
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 2 (vl-lex-number echars warnings))))
  :hints(("Goal" :in-theory (enable vl-lex-number))))






;                          THE LEXER ITSELF
;
; Note that the lexer expects that its input stream has already been
; preprocessed, so there should not be any grave characters or compiler
; directives to worry about.

(defund vl-lex-plain (echars string type warnings)
  "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
  (declare (type string string)
           (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars)
                              (not (equal string ""))
                              (vl-plaintoken-type-p type))))

; We try to match the literal STRING at the beginning of ECHARS.  If so, we
; make a plaintoken using the matched characters and the specified TYPE.

  (let ((string (mbe :logic (if (and (stringp string)
                                     (not (equal string "")))
                                string
                              "foo")
                     :exec string)))
    (if (vl-matches-string-p string echars)
        (let* ((len   (length string))
               (etext (take len echars)))
          (mv (make-vl-plaintoken :etext etext :type type)
              (nthcdr len echars)
              warnings))
      (mv nil echars warnings))))

(def-token/remainder-thms vl-lex-plain
  :formals (echars string type warnings)
  :extra-tokenhyp (force (vl-plaintoken-type-p type))
  :extra-appendhyp (force (vl-plaintoken-type-p type)))

(defthm vl-warninglist-p-of-vl-lex-plain
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 2 (vl-lex-plain echars string type warnings))))
  :hints(("Goal" :in-theory (enable vl-lex-plain))))







(defun vl-plaintoken-alistp (x)
  (declare (xargs :guard t))

; We recognize an alist mapping stringps to plaintoken-type-ps.

  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (stringp (caar x))
         (not (equal (caar x) ""))
         (vl-plaintoken-type-p (cdar x))
         (vl-plaintoken-alistp (cdr x)))))


(defund vl-lex-plain-alist (echars alist warnings)
  "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars)
                              (vl-plaintoken-alistp alist)
                              (vl-warninglist-p warnings))))

; We walk through the alist, looking for the first string that matches the
; beginning of echars.  If we find one, we build a plaintoken using the
; matching echars and the corresponding type.  Since the alist is searched in
; order, you can search for long prefixes first, e.g., ">>>" before ">>".

  (if (atom alist)
      (mv nil echars warnings)
    (mv-let (token remainder warnings)
            (vl-lex-plain echars (caar alist) (cdar alist) warnings)
            (if token
                (mv token remainder warnings)
              (vl-lex-plain-alist echars (cdr alist) warnings)))))

(def-token/remainder-thms vl-lex-plain-alist
  :formals (echars alist warnings)
  :extra-tokenhyp (force (vl-plaintoken-alistp alist))
  :extra-appendhyp (force (vl-plaintoken-alistp alist)))

(defthm vl-warninglist-p-of-vl-lex-plain-alist
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 2 (vl-lex-plain-alist echars alist warnings))))
  :hints(("Goal" :in-theory (enable vl-lex-plain-alist))))



(defsection vl-lex-token1

  (definlined vl-lex-token1 (char1 echars warnings)
    "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
    (declare (xargs :guard (and (characterp char1)
                                (vl-echarlist-p echars)
                                (true-listp echars)
                                (consp echars)
                                (eql char1 (vl-echar->char (car echars)))
                                (vl-warninglist-p warnings))))

; This is the main routine in the lexer, and tries to find a single token at
; the front of echars.  We basically just try to consider all the tokens that
; could begin with each character.
;
; Inputs.
;  CHAR1 is the first character in ECHARS.
;  ECHARS is the vl-echarlist-p that we are lexing.
;
; When we wrote the lexer in program mode, we did not bother with a char1
; argument.  We were lead to add it in order to carry out the guard verification
; proof.  For some reason, the eqlable guards on these case statements are
; really hard for ACL2 if we are dealing with (vl-echar->char (car echars)),
; but are trivial when we just have char1.

    (if (char<= char1 #\9)
        ;; Code is 57 or less.

        (cond
         ((vl-whitespace-p char1) ;; codes 9, 10, 12, 32
          (mv-let (prefix remainder)
                  (vl-read-while-whitespace echars)
                  (mv (make-vl-plaintoken :etext prefix :type :vl-ws)
                      remainder
                      warnings)))

         ((vl-decimal-digit-p char1) ;; codes 48...57
          (vl-lex-number echars warnings))

         (t
          (case char1
            ;; Other special characters whose codes are less than 57.

            (#\! ;; 33
             (vl-lex-plain-alist echars
                                 '(("!==" . :vl-cne)
                                   ("!="  . :vl-neq)
                                   ("!"   . :vl-lognot))
                                 warnings))

            (#\" ;; 34
             (mv-let (tok rem)
                     (vl-lex-string echars)
                     (mv tok rem warnings)))

            (#\# ;; 35
             (vl-lex-plain echars "#" :vl-pound warnings))

            (#\$ ;; 36
             (mv-let (tok rem)
                     (vl-lex-system-identifier echars)
                     (mv tok rem warnings)))

            (#\% ;; 37
             (vl-lex-plain echars "%" :vl-rem warnings))

            (#\& ;; 38
             (vl-lex-plain-alist echars
                                 '(("&&&" . :vl-andandand)
                                   ("&&"  . :vl-logand)
                                   ("&"   . :vl-bitand))
                                 warnings))

            (#\' ;; 39
             (vl-lex-number echars warnings))

            (#\( ;; 40
             (vl-lex-plain-alist echars
                                 '(("(*" . :vl-beginattr)
                                   ("("  . :vl-lparen))
                                 warnings))

            (#\) ;; 41
             (vl-lex-plain echars ")" :vl-rparen warnings))

            (#\* ;; 42
             (vl-lex-plain-alist echars
                                 '(("**" . :vl-power)
                                   ("*)" . :vl-endattr)
                                   ("*"  . :vl-times))
                                 warnings))

            (#\+ ;; 43
             (vl-lex-plain-alist echars
                                 '(("+:" . :vl-pluscolon)
                                   ("+"  . :vl-plus))
                                 warnings))

            (#\, ;; 44
             (vl-lex-plain echars "," :vl-comma warnings))

            (#\- ;; 45
             (vl-lex-plain-alist echars
                                 '(("->" . :vl-arrow)
                                   ("-:" . :vl-minuscolon)
                                   ("-"  . :vl-minus))
                                 warnings))

            (#\. ;; 46
             (vl-lex-plain echars "." :vl-dot warnings))

            (#\/ ;; 47
             (cond ((vl-matches-string-p "//" echars)
                    (mv-let (tok rem)
                            (vl-lex-oneline-comment echars)
                            (mv tok rem warnings)))
                   ((vl-matches-string-p "/*" echars)
                    (mv-let (tok rem)
                            (vl-lex-block-comment echars)
                            (mv tok rem warnings)))
                   (t
                    (vl-lex-plain echars "/" :vl-div warnings))))

            (otherwise
             (mv nil echars warnings)))))

      ;; Otherwise, we know that the character code is at least 58.

      (if (vl-simple-id-head-p char1) ;; codes 65...90, 95, 97...122
          (mv-let (tok rem)
                  (vl-lex-simple-identifier-or-keyword echars)
                  (mv tok rem warnings))

        ;; Most of this stuff is pretty rare, so it probably isn't too
        ;; important to try to optimize the search.

        (case char1

          (#\: ;; 58
           (vl-lex-plain echars ":" :vl-colon warnings))

          (#\; ;; 59
           (vl-lex-plain echars ";" :vl-semi warnings))

          (#\< ;; 60
           (vl-lex-plain-alist echars
                               '(("<<<" . :vl-ashl)
                                 ("<<"  . :vl-shl)
                                 ("<="  . :vl-lte)
                                 ("<"   . :vl-lt))
                               warnings))

          (#\= ;; 61
           (vl-lex-plain-alist echars
                               '(("===" . :vl-ceq)
                                 ("=="  . :vl-eq)
                                 ("="   . :vl-equalsign))
                               warnings))

          (#\> ;; 62
           (vl-lex-plain-alist echars
                               '((">>>" . :vl-ashr)
                                 (">>"  . :vl-shr)
                                 (">="  . :vl-gte)
                                 (">"   . :vl-gt))
                               warnings))

          (#\? ;; 63
           (vl-lex-plain echars "?" :vl-qmark warnings))

          (#\@ ;; 64
           (vl-lex-plain echars "@" :vl-atsign warnings))


          (#\[ ;; 91
           (vl-lex-plain echars "[" :vl-lbrack warnings))

          (#\\ ;; 92
           (mv-let (tok rem)
                   (vl-lex-escaped-identifier echars)
                   (mv tok rem warnings)))

          (#\] ;; 93
           (vl-lex-plain echars "]" :vl-rbrack warnings))

          (#\^ ;; 94
           (vl-lex-plain-alist echars
                               '(("^~" . :vl-xnor)
                                 ("^"  . :vl-xor))
                               warnings))

          (#\{ ;; 123
           (vl-lex-plain echars "{" :vl-lcurly warnings))

          (#\| ;; 124
           (vl-lex-plain-alist echars
                               '(("||" . :vl-logor)
                                 ("|"  . :vl-bitor))
                               warnings))

          (#\} ;; 125
           (vl-lex-plain echars "}" :vl-rcurly warnings))

          (#\~ ;; 126
           (vl-lex-plain-alist echars
                               '(("~&" . :vl-nand)
                                 ("~|" . :vl-nor)
                                 ("~^" . :vl-xnor)
                                 ("~"  . :vl-bitnot))
                               warnings))

          (otherwise
           (mv nil echars warnings))))))

  (local (defthm lemma
           (equal (equal (acl2-count (second (vl-read-while-whitespace echars)))
                         (acl2-count echars))
                  (not (vl-whitespace-p (vl-echar->char (first echars)))))
           :hints(("Goal" :in-theory (enable vl-read-while-whitespace)))))

  (def-token/remainder-thms vl-lex-token1
    :formals (char1 echars warnings)
    :extra-tokenhyp
    (and (force (consp echars))
         (force (equal char1 (vl-echar->char (car echars)))))
    :extra-appendhyp
    (and (force (consp echars))
         (force (equal char1 (vl-echar->char (car echars)))))
    :extra-strongcounthyp
    (force (equal char1 (vl-echar->char (car echars)))))

  (defthm vl-warninglist-p-of-vl-lex-token1
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 2 (vl-lex-token1 char1 echars warnings))))
    :hints(("Goal" :in-theory (enable vl-lex-token1)))))

(definlined vl-lex-token (echars warnings)
  "Returns (MV TOKEN/NIL REMAINDER WARNINGS)"
  (declare (xargs :guard (and (vl-echarlist-p echars)
                              (true-listp echars)
                              (vl-warninglist-p warnings))))
  (if (not (consp echars))
      (mv nil echars warnings)
    (let* ((echar1 (car echars))
           (char1  (vl-echar->char echar1)))
      (vl-lex-token1 char1 echars warnings))))

(def-token/remainder-thms vl-lex-token
  :formals (echars warnings))

(defthm vl-warninglist-p-of-vl-lex-token
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 2 (vl-lex-token echars warnings))))
  :hints(("Goal" :in-theory (enable vl-lex-token))))





(defsection vl-lex

  (defund vl-lex-exec (echars acc warnings)
    "Returns (MV SUCCESSP TOKEN-LIST WARNINGS)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-tokenlist-p acc)
                                (true-listp acc)
                                (vl-warninglist-p warnings))))
    (if (consp echars)
        (mv-let (tok remainder warnings)
                (vl-lex-token echars warnings)
                (if (not tok)
                    (prog2$
                     (cw "About to cause an error.~%")
                     (mv (cw "Lexer error (~s0): unable to identify a valid token.~%~
                           [[ Previous  ]]: ~s1~%~
                           [[ Remaining ]]: ~s2~%"
                             (vl-location-string (vl-echar->loc (car echars)))
                             (let* ((rprev (reverse acc))
                                    (chop  (nthcdr (nfix (- (length rprev) 30)) rprev))
                                    (chars (vl-tokenlist->etext chop)))
                               (vl-echarlist->string chars))
                             (vl-echarlist->string (take (min 30 (length echars)) echars)))
                         acc
                         warnings))
                  (vl-lex-exec remainder (cons tok acc) warnings)))
      (mv t acc warnings)))

  (defund vl-lex (echars warnings)
    "Returns (MV SUCCESSP TOKEN-LIST WARNINGS)"
    (declare (xargs :guard (and (vl-echarlist-p echars)
                                (true-listp echars)
                                (vl-warninglist-p warnings))
                    :verify-guards nil))
    (mbe :logic
         (if (atom echars)
             (mv t nil warnings)
           (b* (((mv first echars warnings)
                 (vl-lex-token echars warnings))
                ((when (not first))
                 (mv nil nil warnings))
                ((mv successp rest warnings)
                 (vl-lex echars warnings)))
               (mv successp (cons first rest) warnings)))
         :exec
         (mv-let (successp tokens warnings)
                 (vl-lex-exec echars nil warnings)
                 (mv successp (reverse tokens) warnings))))

  (local (in-theory (enable vl-lex-exec vl-lex)))

  (local (defthm vl-lex-exec-successp-removal
           (equal (mv-nth 0 (vl-lex-exec echars acc warnings))
                  (mv-nth 0 (vl-lex echars warnings)))))

  (local (defthm vl-lex-exec-tokens-removal
           (equal (mv-nth 1 (vl-lex-exec echars acc warnings))
                  (revappend (mv-nth 1 (vl-lex echars warnings)) acc))))

  (local (defthm vl-lex-exec-warnings-removal
           (equal (mv-nth 2 (vl-lex-exec echars acc warnings))
                  (mv-nth 2 (vl-lex echars warnings)))))

  (defthm vl-lex-exec-redefinition
    (equal (vl-lex-exec echars acc warnings)
           (mv-let (successp tokens warnings)
                   (vl-lex echars warnings)
                   (mv successp (revappend tokens acc) warnings))))

  (defthm type-of-vl-lex-successp
    (booleanp (mv-nth 0 (vl-lex echars warnings)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-lex-tokens
    (true-listp (mv-nth 1 (vl-lex echars warnings)))
    :rule-classes :type-prescription)

  (verify-guards vl-lex)

;; Correctness Claim 1.  The lexer produces a list of tokens.
  (defthm vl-tokenlist-p-of-vl-lex-tokens
    (implies (force (vl-echarlist-p echars))
             (vl-tokenlist-p (mv-nth 1 (vl-lex echars warnings)))))

;; Correctness Claim 2.  If we flatten the resulting tokens, we obtain the
;; original characters.
  (defthm vl-tokenlist->etext-of-vl-lex-tokens
    (implies (and (first (vl-lex echars warnings))
                  (force (vl-echarlist-p echars))
                  (force (true-listp echars)))
             (equal (vl-tokenlist->etext (mv-nth 1 (vl-lex echars warnings)))
                    echars)))

  (defthm vl-warninglist-p-of-vl-lex-tokens
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 2 (vl-lex echars warnings)))))

  (defttag vl-optimize)
  (never-memoize vl-lex-exec)
  (progn! (set-raw-mode t)
          (defun vl-lex (echars warnings)
            (mv-let (successp tokens warnings)
              (vl-lex-exec echars nil warnings)
              (mv successp (nreverse tokens) warnings))))
  (defttag nil))





(defsection vl-kill-whitespace-and-comments

  (defund vl-kill-whitespace-and-comments-core (tokens tokens-acc cmap-acc)
    (declare (xargs :guard (vl-tokenlist-p tokens)))

; Returns (MV TOKENS-ACC CMAP-ACC).  TOKENS-ACC contains all of the
; non-whitespace, non-comment tokens of tokens in reverse order; CMAP-ACC is a
; comment map generated from the comments of tokens, also in reverse order.

    (if (atom tokens)
        (mv tokens-acc cmap-acc)

      (let ((type (vl-token->type (car tokens))))
        (vl-kill-whitespace-and-comments-core
         (cdr tokens)

         (if (or (eq type :vl-ws)
                 (eq type :vl-comment))
             tokens-acc
           (cons (car tokens) tokens-acc))

         (if (eq type :vl-comment)
             ;; See note on comment shifting in vl-commentmap-p to understand
             ;; why we change the column number to zero.
             (cons (cons (change-vl-location (vl-token->loc (car tokens)) :col 0)
                         (vl-token->string (car tokens)))
                   cmap-acc)
           cmap-acc)))))

  (defund vl-kill-whitespace-and-comments (tokens)
    (declare (xargs :guard (vl-tokenlist-p tokens)
                    :verify-guards nil))

; Returns (MV TOKENS CMAP).  TOKENS is a new token-list wherein the whitespace
; and comments have been removed; CMAP is the comment map generated from these
; tokens.

    (mbe :logic
         (if (atom tokens)
             (mv nil nil)
           (mv-let (tokens-rest cmap-rest)
                   (vl-kill-whitespace-and-comments (cdr tokens))
                   (let* ((type (vl-token->type (car tokens)))
                          (new-tokens (if (or (eq type :vl-ws)
                                              (eq type :vl-comment))
                                          tokens-rest
                                        (cons (car tokens) tokens-rest)))
                          (new-cmap (if (eq type :vl-comment)
                                        (cons (cons (change-vl-location (vl-token->loc (car tokens)) :col 0)
                                                    (vl-token->string (car tokens)))
                                              cmap-rest)
                                      cmap-rest)))
                     (mv new-tokens new-cmap))))
         :exec
         (mv-let (tokens-acc cmap-acc)
                 (vl-kill-whitespace-and-comments-core tokens nil nil)
                 (mv (reverse tokens-acc)
                     (reverse cmap-acc)))))

  (defttag vl-optimize)
   (never-memoize vl-kill-whitespace-and-comments-core)
  (progn! (set-raw-mode t)
          (defun vl-kill-whitespace-and-comments (tokens)
            (mv-let (tokens-acc cmap-acc)
              (vl-kill-whitespace-and-comments-core tokens nil nil)
              (mv (nreverse tokens-acc)
                  (nreverse cmap-acc)))))
  (defttag nil)

  (local (in-theory (enable vl-kill-whitespace-and-comments-core
                            vl-kill-whitespace-and-comments)))

  (local (defthm lemma
           (implies (true-listp tacc)
                    (true-listp (mv-nth 0 (vl-kill-whitespace-and-comments-core tokens tacc cacc))))))

  (local (defthm lemma2
           (implies (true-listp cacc)
                    (true-listp (mv-nth 1 (vl-kill-whitespace-and-comments-core tokens tacc cacc))))))

  (local (defthm lemma3
           (implies (true-listp tacc)
                    (equal (mv-nth 0 (vl-kill-whitespace-and-comments-core tokens tacc cacc))
                           (revappend (mv-nth 0 (vl-kill-whitespace-and-comments tokens))
                                      tacc)))
           :hints(("Goal" :induct (vl-kill-whitespace-and-comments-core tokens tacc cacc)))))

  (local (defthm lemma4
           (implies (true-listp cacc)
                    (equal (mv-nth 1 (vl-kill-whitespace-and-comments-core tokens tacc cacc))
                           (revappend (mv-nth 1 (vl-kill-whitespace-and-comments tokens))
                                      cacc)))
           :hints(("Goal" :induct (vl-kill-whitespace-and-comments-core tokens tacc cacc)))))

  (verify-guards vl-kill-whitespace-and-comments)

  (defthm true-listp-of-vl-kill-whitespace-and-comments-0
    (true-listp (mv-nth 0 (vl-kill-whitespace-and-comments x)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-kill-whitespace-and-comments-1
    (true-listp (mv-nth 1 (vl-kill-whitespace-and-comments x)))
    :rule-classes :type-prescription)

  (defthm vl-tokenlist-p-of-vl-kill-whitespace-and-comments
    (implies (force (vl-tokenlist-p tokens))
             (vl-tokenlist-p (mv-nth 0 (vl-kill-whitespace-and-comments tokens)))))

  (defthm vl-commentmap-p-of-vl-kill-whitespace-and-comments
    (implies (force (vl-tokenlist-p tokens))
             (vl-commentmap-p (mv-nth 1 (vl-kill-whitespace-and-comments tokens))))))




(defund vl-make-test-tstream (string)
  (declare (xargs :guard (stringp string)))

  ;; String is expected not to have any preprocessor symbols in it.  We turn it
  ;; into an estring, lex it, then turn it into tokens.  These can then be used
  ;; for testing.

  (mv-let (successp tokens warnings)
          (vl-lex (vl-echarlist-from-str string) nil)
          (declare (ignore warnings))
          (if (not successp)
              (er hard? 'vl-make-test-tstring "Lexing failed.")
            (mv-let (tokens cmap)
                    (vl-kill-whitespace-and-comments tokens)
                    (declare (ignore cmap))
                    tokens))))

(defthm vl-tokenlist-p-of-vl-make-test-tstream
  (vl-tokenlist-p (vl-make-test-tstream string))
  :hints(("Goal" :in-theory (enable vl-make-test-tstream))))

