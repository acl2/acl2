;;; Copyright 2026 J. David Taylor
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions are met:
;;;
;;; 1. Redistributions of source code must retain the above copyright notice,
;;;    this list of conditions and the following disclaimer.
;;;
;;; 2. Redistributions in binary form must reproduce the above copyright notice,
;;;    this list of conditions and the following disclaimer in the documentation
;;;    and/or other materials provided with the distribution.
;;;
;;; 3. Neither the name of the copyright holder nor the names of its
;;;    contributors may be used to endorse or promote products derived from this
;;;    software without specific prior written permission.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
;;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;;; POSSIBILITY OF SUCH DAMAGE.


(in-package "TYPE-SPEC")

(include-book "xdoc/top" :dir :system)
(include-book "projects/apply/top" :dir :system)

(defxdoc type-spec
  :parents (acl2::type-spec)
  :short "A library for working with type specifiers."
  :long
  "<p>The @('type-spec') library implements @(tsee typep$), an ACL2 variant of
  Common Lisp's <a
  href=\"https://www.lispworks.com/documentation/HyperSpec/Body/f_typep.htm#typep\">
  <tt>cl::typep</tt></a>.  @('typep$') is implemented as a macro that expands to
  an appropriate recognizing expression when the type specifier is a literal.
  Auxiliary features include a recognizer for type specifiers, @(tsee
  acl2-type-spec-p); @(see acl2::type-spec)-related @(see constants); a defined
  @(see theory); defined @(tsee *exports*); and an expansion utility @(tsee
  typep$expansion).</p>

  <p>Unlike the ACL2 system's handling of type specifiers, @('typep$') does not
  requires access to the @(tsee world).  The predicate for a @('satisfies') type
  specifier is only checked to be a legal variable.  Any malformed events due to
  this weakness will be detected and reported by the ACL2 system.</p>")

(defsection *exports*
  :parents (type-spec)
  :short "Symbols exported by the @('TYPE-SPEC') package."
  :long
  "<p>Symbols with names from the @('ACL2') package are from that package.</p>
  @(`(:code (list 'defconst '*exports* (list 'quote *exports*)))`)")

(defsection constants
  :parents (type-spec)
  :short "Type specifier relevant constants."
  :long
  "<p>The symbols in the following quoted lists are from the @('ACL2') package.</p>
  @(`(:code (list 'defconst
                  '*atomic-type-specifiers*
                  (list 'quote *atomic-type-specifiers*)))`)

  @(`(:code (list 'defconst
                  '*atomic-real-subtype-specifiers*
                  (list 'quote *atomic-real-subtype-specifiers*)))`)

  @(`(:code (list 'defconst
                  '*compound-type-specifier-names*
                  (list 'quote *compound-type-specifier-names*)))`)

  @(`(:code (list 'defconst
                  '*compound-real-type-specifier-names*
                  (list 'quote *compound-real-type-specifier-names*)))`)")


(defsection interval-designator-p
  :parents (acl2-type-spec-p)
  :short "Recognize a valid interval designator."
  :long
  "<p>An <a
  href=\"https://www.lispworks.com/documentation/HyperSpec/Body/12_af.htm\">interval
  designator</a> is a valid upper or lower bound for a numeric interval compound
  type specifier.</p>"

  (defun interval-designator-p (designator type-spec)
    (declare (xargs :guard t
                    :type-prescription
                    (booleanp (interval-designator-p designator type-spec))))
    (flet ((type-check (designator type-spec)
; Check that the numeric designator is properly typed
             (case type-spec
               (integer
                (integerp designator))
               (rational
                (rationalp designator))
               (real
                (real/rationalp designator)))))
      (cond
        ((not (member-eq type-spec *compound-real-type-specifier-names*))
         'nil)
        ((symbolp designator)
         (eq designator '*))
        ((consp designator)
         (and (null (cdr designator))
              (type-check (car designator) type-spec)))
        (t
         (type-check designator type-spec))))))


(defsection acl2-type-spec-p
  :parents (type-spec)
  :short "Recognize a valid ACL2 type specifier."
  :long "<p>@('acl2-type-spec-p') is warranted.  Since @('acl2-type-spec-p')
  does not take @('world') as an argument, it is a weak recognizer for
  @('satisfies') type specs.  It only checks that the predicate is a @(tsee
  legal-variablep).</p>"

  (defun acl2-type-spec-p (type-spec)
    (declare (xargs :guard t
                    :type-prescription
                    (booleanp (acl2-type-spec-p type-spec))))
    (cond
      ((symbolp type-spec)
       (and (member-eq type-spec *atomic-type-specifiers*)
            t))
      ((consp type-spec)
       (let ((name (car type-spec))
             (params (cdr type-spec)))
         (and (symbolp name)
              (member-eq name *compound-type-specifier-names*)
              (case name
                ((and or) ; (name . (type1 ... typek))
                 (if (consp params)
                     (and (acl2-type-spec-p (car params))
                          (acl2-type-spec-p (cons name (cdr params))))
                     (null params)))
                (complex ; (complex . (type-spec))
                 ;; NOTE: `COMPLEX' is disjoint from `REAL'
                 (and (consp params)
                      (null (cdr params))
                      (let ((type-spec (car params)))
                        (or (and (symbolp type-spec)
                                 (and (member-eq type-spec *atomic-real-subtype-specifiers*)
                                      t))
                            (and (consp type-spec)
                                 (symbolp (car type-spec))
                                 (member-eq (car type-spec) *compound-real-type-specifier-names*)
                                 (acl2-type-spec-p type-spec))))))
                ((integer real rational) ; (name . (i j))
                 (and (consp params)
                      (consp (cdr params))
                      (null (cddr params))
                      (and (interval-designator-p (first params) name)
                           (interval-designator-p (second params) name))))
                (member ; (member . (x1 ... xn))
                 (eqlable-listp params))
                (mod ; (mod . (i))
                 (and (consp params)
                      (null (cdr params))
                      (let ((param (car params)))
                        (and (integerp param)
                             (< 0 param)))))
                (not ; (not . (type-spec))
                 (and (consp params)
                      (null (cdr params))
                      (acl2-type-spec-p (car params))))
                (satisfies ; (satisfies . (predicate))
                 (and (consp params)
                      (null (cdr params))
                      (let ((predicate (car params)))
                        ;; `WORLD' is inaccessible
                        (legal-variablep predicate))))
                ((signed-byte unsigned-byte) ; (name . (size))
                 (and (consp params)
                      (null (cdr params))
                      (let ((size (car params)))
                        (and (integerp size)
                             (< 0 size)))))
                (string ; (string . (max))
                 (and (consp params)
                      (null (cdr params))
                      (let ((max (car params)))
                        (and (integerp max)
                             (<= 0 max)))))))))))

  (defthm acl2-type-spec-p-cr
    (implies (acl2-type-spec-p type-spec)
             (or (symbolp type-spec)
                 (and (consp type-spec)
                      (true-listp type-spec))))
    :rule-classes :compound-recognizer)

  (defthm acl2-type-spec-p-when-atom
    (implies (atom type-spec)
             (iff (acl2-type-spec-p type-spec)
                  (member type-spec *atomic-type-specifiers*))))

  (defwarrant acl2-type-spec-p))


;;;; `TYPEP$RUNTIME'
(defun typep$runtime (object type-spec)
  (declare (xargs :guard (acl2-type-spec-p type-spec)
                  :type-prescription :none))
  (and (mbt (acl2-type-spec-p type-spec))
       (cond
         ((symbolp type-spec)
          (case type-spec
            (atom
             (atom object))
            (bit
             (bitp object))
            (character
             (characterp object))
            (complex
             (complex/complex-rationalp object))
            (cons
             (consp object))
            (double-float
             (dfp object))
            ((integer signed-byte)
             (integerp object))
            (list
             (listp object))
            ;; If `TYPE-SPEC' is `NIL', vacuously return `NIL'.
            (null
             (null object))
            (number
             (acl2-numberp object))
            (ratio
             (and (rationalp object)
                  (not (integerp object))))
            (rational
             (rationalp object))
            (real
             (real/rationalp object))
            (standard-char
             (and (characterp object)
                  (standard-char-p object)))
            (string
             (stringp object))
            (symbol
             (symbolp object))
            ((t)
             t)
            (unsigned-byte
             (and (integerp object)
                  (<= 0 object)))))
         ((consp type-spec)
          (let ((name (car type-spec))
                (params (cdr type-spec)))
            (case name
              ((and or) ; (name . (type1 ... typek))
               (if (consp params)
                   (let ((bool (typep$runtime object (car params))))
                     (case name
                       (or
                        (or bool
                            (typep$runtime object (cons name (cdr params)))))
                       (and
                        (and bool
                             (typep$runtime object (cons name (cdr params)))))))
                   (case name
                     (or
                      nil)
                     (and
                      t))))
              (complex ; (complex . (type-spec))
               (let ((type-spec (car params)))
                 (and (complex/complex-rationalp object)
                      (typep$runtime (realpart object) type-spec)
                      (typep$runtime (imagpart object) type-spec))))
              ((integer real rational) ; (name . (i j))
               (let ((i (first params))
                     (j (second params)))
                 (and (typep$runtime object name)
                      (cond
                        ((symbolp i)
                         t)
                        ((consp i)
                         (< (car i) object))
                        (t
                         (<= i object)))
                      (cond
                        ((symbolp j)
                         t)
                        ((consp j)
                         (< object (car j)))
                        (t
                         (<= object j))))))
              (member ; (member . (x1 ... xn))
               (member object params))
              (mod ; (mod . (i))
               (and (integerp object)
                    (<= 0 object)
                    (< object (car params))))
              (not ; (not . (type-spec))
               (not (typep$runtime object (car params))))
              (satisfies ; (satisfies . (predicate))
               (apply$ (car params) (list object)))
              ((signed-byte unsigned-byte) ; (name . (size))
               (let ((size (car params)))
                 (case name
                   (signed-byte
                    (signed-byte-p size object))
                   (unsigned-byte
                    (unsigned-byte-p size object)))))
              (string ; (string . (max))
               (and (stringp object)
                    (int= (length object) (car params))))))))))

(defsection typep$runtime
  :parents (typep$)
  :short "Check if an object satifies a @(see acl2::type-spec)."
  :long
  "<p>@(call typep$runtime) returns a generalized boolean and its body is not
   @(see tame).  The obstructions are @('member') and @('satisfies')
   specifiers.</p>"

  (defthm typep$runtime-typically-booleanp
    (implies (or (atom type-spec)
                 (not (member (car type-spec)
                              '(and or member satisfies))))
             (booleanp (typep$runtime object type-spec)))
    :rule-classes nil))


;;;; `TYPEP$EXPANSION'
(defun flatten-cd (name nest)
; Flatten nest of conjunctions or disjunctions without exponential blowup.
; `NAME' is `AND' or `OR', and `NEST' is the list of conjoined or disjoined
; untranslated terms.  NEST is implicitly converted to a true list.
;
; `FLATTEN-CD' returns a list of untranslated terms such that the evaluation of
; (CONS NAME (FLATTEN-CD NAME NEST)) is equal to the evaluation of (CONS NAME
; NEST).  However, this is a meta-theorem.  We cannot prove it
; with `EV$' because macros cannot be `APPLY$'ed.
  (declare (xargs :guard (member-eq name '(and or))
                  :type-prescription (true-listp (flatten-cd name nest)))
           (type (member and or) name))
  (cond
    ((atom nest)
; (CONS NAME NEST) and (CONS NAME NIL) have the same evaluation when NEST is an
; ATOM.
     nil)

    ((consp (car nest))
; NEST is a CONSP and (CAR NEST) is a CONSP.
     (let* ((op (caar nest))
            (forms (if (member-eq op '(and or))
                       (if (eq op name)
                           (flatten-cd name (cdar nest))
                           (list (cons op (flatten-cd op (cdar nest)))))
                       (list (car nest)))))
; We must justify ourselves in three distinct cases:

; 1. Suppose `OP' is neither 'AND' nor 'OR'.  We have the following
; identifications:
;
; (CONS NAME
;       (APPEND (LIST (CAR NEST))
;               (FLATTEN-CD NAME (CDR NEST))))
;
; by definition of APPEND, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (FLATTEN-CD NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CONS NAME
;                   (FLATTEN-CD NAME (CDR NEST)))))
;
; by induction, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CONS NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CDR NEST)))
;
; by ACL2::CONS-CAR-CDR, evaluates as
;
; (CONS NAME NEST)

; 2. Suppose `OP' is NAME.  We have the following identifications:
;
; (CONS NAME
;       (APPEND (FLATTEN-CD NAME (CDAR NEST))
;               (FLATTEN-CD NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (APPEND (LIST (CONS NAME
;                           (FLATTEN-CD NAME (CDAR NEST))))
;               (LIST (CONS NAME
;                           (FLATTEN-CD NAME (CDR NEST))))))
;
; by the definition of APPEND, evaluates as
;
; (CONS NAME
;       (LIST (CONS NAME
;                   (FLATTEN-CD NAME (CDAR NEST)))
;             (CONS NAME
;                   (FLATTEN-CD NAME (CDR NEST)))))
;
; by induction, evaluates as
;
; (CONS NAME
;       (LIST (CONS NAME (CDAR NEST))
;             (CONS NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CDR NEST)))
;
; by ACL2::CONS-CAR-CDR, evalues as
;
; (CONS NAME NEST)

; 3. Suppose `OP' and NAME are not equal, but one is `and' and the other is
; `OR'. We have the following identifications:
;
; (CONS NAME
;       (APPEND (LIST (CONS OP (FLATTEN-CD OP (CDAR NEST))))
;               (FLATTEN-CD NAME (CDR NEST))))
;
; by definition of APPEND, evaluates as
;
; (CONS NAME
;       (CONS (CONS OP (FLATTEN-CD OP (CDAR NEST)))
;             (FLATTEN-CD NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (CONS (CONS OP (FLATTEN-CD OP (CDAR NEST)))
;             (CONS NAME
;                   (FLATTEN-CD NAME (CDR NEST)))))
;
; by induction, evaluates as
;
; (CONS NAME
;       (CONS (CONS OP (CDAR NEST))
;             (CONS NAME (CDR NEST))))
;
; by associativity of NAME and choice of OP, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CDR NEST)))
;
; by ACL2::CONS-CAR-CDR, evaluates as
;
; (CONS NAME NEST)

       (append forms (flatten-cd name (cdr nest)))))

    (t
; NEST is a CONSP, but (CAR NEST) is an ATOM.
;
; Suppose (CONS NAME (FLATTEN-CD NAME (CDR NEST))) has the same evaluation as
; (CONS NAME (CDR NEST)).  Then we have the following identifications:
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (FLATTEN-CD NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CONS NAME
;                   (FLATTEN-CD NAME (CDR NEST)))))
;
; by substitution of our induction hypothesis, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CONS NAME (CDR NEST))))
;
; by associativity of NAME, evaluates as
;
; (CONS NAME
;       (CONS (CAR NEST)
;             (CDR NEST)))
;
; by ACL2::CONS-CAR-CDR, evaluates as
;
; (CONS NAME NEST)
;
     (cons (car nest)
           (flatten-cd name (cdr nest))))))

(defun typep$expansion (object type-spec)
  (declare (xargs :guard (acl2-type-spec-p type-spec)
                  :type-prescription
                  (or (booleanp (typep$expansion object type-spec))
                      (and (consp (typep$expansion object type-spec))
                           (true-listp (typep$expansion object type-spec))))))
  (and (mbt (acl2-type-spec-p type-spec))
       (if (symbolp type-spec)
           (case type-spec
             (atom
              `(atom ,object))
             (bit
              `(bitp ,object))
             (character
              `(characterp ,object))
             (complex
              `(complex/complex-rationalp ,object))
             (cons
              `(consp ,object))
             (double-float
              `(dfp ,object))
             ((integer signed-byte)
              `(integerp ,object))
             (list
              `(listp ,object))
             (null
              `(null ,object))
             (number
              `(acl2-numberp ,object))
             (ratio
              `(and (rationalp ,object)
                    (not (integerp ,object))))
             (rational
              `(rationalp ,object))
             (real
              `(real/rationalp ,object))
             (standard-char
              `(and (characterp ,object)
                    (standard-char-p ,object)))
             (string
              `(stringp ,object))
             (symbol
              `(symbolp ,object))
             ((t)
              t)
             (unsigned-byte
              `(and (integerp ,object)
                    (<= 0 ,object)))
             (t
              nil))
           ;; (consp type-spec)
           (let ((name (car type-spec))
                 (params (cdr type-spec)))
             (case name
               ((and or)
                (cond
                  ;; (name)
                  ((endp params)
                   (case name
                     (or
                      nil)
                     (and
                      t)))
                  ;; (name . (type))
                  ((endp (cdr params))
                   (typep$expansion object (car params)))
                  ;; (name . (type1 ... typek))
                  (t
                   (cons name
; We would like to remove duplicates here.  We cannot naively apply
; `ACL2::REMOVE-DUPLICATES-EQUAL' because some terms may serve as guards for
; others (e.g. `SATISFIES').  We cannot naively apply
; `ACL2::HONS-REMOVE-DUPLICATES' because the final term of some conjunction or
; disjunction (possibly nested) may be a `SATISFIES' or `MEMBER' and that would
; alter the value of a generalized boolean while preserving its truthiness.  We
; leave this optimization for now.
                         (flatten-cd name
                                     (list (typep$expansion object (car params))
                                           (typep$expansion object (cons name (cdr params)))))))))
               (complex ; (complex . (type-spec))
                (let ((type-spec (car params)))
                  (append `(and (complex/complex-rationalp ,object))
                          (flatten-cd 'and (list (typep$expansion `(realpart ,object) type-spec)))
                          (flatten-cd 'and (list (typep$expansion `(imagpart ,object) type-spec))))))
               ((integer real rational) ; (name . (i j))
                (let* ((i (first params))
                       (j (second params))
                       (recognizer (typep$expansion object name))
                       (lower (and (not (symbolp i))
                                   (if (consp i)
                                       `(< ,(car i) ,object)
                                       `(<= ,i ,object))))
                       (upper (and (not (symbolp j))
                                   (if (consp j)
                                       `(< ,object ,(car j))
                                       `(<= ,object ,j)))))
                  (if (or lower upper)
                      `(and ,recognizer
                            ,@(and lower (list lower))
                            ,@(and upper (list upper)))
                      recognizer)))
               (member ; (member . (x1 ... xn))
                `(member ,object ',params))
               (mod ; (mod . (i))
                `(and (integerp ,object)
                      (<= 0 ,object)
                      (< ,object ,(car params))))
               (not ; (not . (type-spec))
                `(not ,(typep$expansion object (car params))))
               (satisfies ; (satisfies . (predicate))
                `(,(car params) ,object))
               ((signed-byte unsigned-byte) ; (name . (size))
                (let ((size (car params)))
                  (case name
                    (signed-byte
                     `(signed-byte-p ,size ,object))
                    (unsigned-byte
                     `(unsigned-byte-p ,size ,object)))))
               (string ; (string . (max))
                `(and (stringp ,object)
                      (int= (length ,object) ',(car params)))))))))

(defsection typep$expansion
  :parents (typep$)
  :short "Create a recognizing expression for a @(see acl2::type-spec)."
  :long
  "<p>In the form @(call typep$expansion), @('type-spec') must be a type
  specifier.  @('typep$expansion') computes a recognizer expression for that
  @(see acl2::type-spec).  For example, @('(typep$expansion 'x
  '(complex (integer (-3) 7)))') returns
  @(`(:code (typep$expansion 'x '(complex (integer (-3) 7))))`)</p>

  <p>@('typep$expansion') has an optimization over the naive expansion of a type
  specifier.  If the expansion would have nested @('and') forms, then
  @('typep$expansion') flattens them.  This is done similarly with nested
  @('or') forms, and is recursive.  However, @('typep$expansion') does not
  distibute conjunction over disjunction nor the reverse.</p>

  <p>This function is warranted.</p>"

  (defwarrant typep$expansion))


;;;; `TYPEP$'
(defsection typep$
  :parents (type-spec)
  :short "Check if an object satisfies a type specifier."
  :long
  "<p>@('typep$') is a macro alias for @(tsee typep$runtime) unless its second
  argument @('type-spec') is a quoted type specifier.  If its first argument
  @('object') is also quoted, then @(call typep$) expands to a literal.
  Otherwise, @('typep$') expands to an appropriate recognizing term for
  @('object') as described in @(see acl2::type-spec).  Furthermore, if the
  recognizing term is a conjunction or disjunction, it is @('let')-wrapped as in
  @(tsee defabbrev).</p>"

  (defmacro typep$ (object type-spec)
; The justification that `TYPEP$' is semantically consistent regardless of its
; arguments depends on two things:
;
; 1. The meta-theorem established in the comments of `FLATTEN-CD', and
; 2. The implementation of `TYPEP$RUNTIME' and `TYPEP$EXPANSION' are consistent.
;
; Both of these currently rely on manual checks.
    (declare (xargs :guard t))
; If `TYPE-SPEC' is a quoted constant and `OBJECT' is not, then we macro expand
; into the appropriate conjunction or disjunction of recognizers applied to
; `OBJECT'.
    (if (and (quotep type-spec)
             (acl2-type-spec-p (cadr type-spec)))
        (if (quotep object)
            ;; We evaluate at expansion time when both arguments are quoted.
            (typep$runtime (cadr object) (cadr type-spec))
; We do a test expansion to see if the result is composite.  If so, we wrap the
; body in a `LET', similarly to a `DEFABBREV'.
            (let* ((type-spec (cadr type-spec))
                   ;; UNE means "use nowhere else"
                   (expansion (typep$expansion 'typep$-une type-spec)))
              (if (and (consp expansion)
                       (member-eq (car expansion) '(and or)))
                  `(let ((typep$-une ,object))
                     ,expansion)
                  (typep$expansion object type-spec))))
; Otherwise, we place code for runtime checking.
        `(typep$runtime ,object ,type-spec)))

  (add-macro-fn typep$ typep$runtime)

;;;; Atomic Specifier Rewrite Theorems
  (defthm typep$-atom
    (equal (typep$runtime object 'atom)
           (atom object)))

  (defthm typep$-bit
    (equal (typep$runtime object 'bit)
           (bitp object)))

  (defthm typep$-character
    (equal (typep$runtime object 'character)
           (characterp object)))

  (defthm typep$-complex/atomic
    (equal (typep$runtime object 'complex)
           (complex/complex-rationalp object)))

  (defthm typep$-cons
    (equal (typep$runtime object 'cons)
           (consp object)))

  (defthm typep$-double-float
    (equal (typep$runtime object 'double-float)
           (dfp object)))

  (defthm typep$-integer/atomic
    (equal (typep$runtime object 'integer)
           (integerp object)))

  (defthm typep$-list
    (equal (typep$runtime object 'list)
           (listp object)))

  (defthm typep$-nil
    (equal (typep$runtime object 'nil)
           nil))

  (defthm typep$-null
    (equal (typep$runtime object 'null)
           (null object)))

  (defthm typep$-number
    (equal (typep$runtime object 'number)
           (acl2-numberp object)))

  (defthm typep$-ratio
    (equal (typep$runtime object 'ratio)
           (and (rationalp object)
                (not (integerp object)))))

  (defthm typep$-rational/atomic
    (equal (typep$runtime object 'rational)
           (rationalp object)))

  (defthm typep$-real/atomic
    (equal (typep$runtime object 'real)
           (real/rationalp object)))

  (defthm typep$-signed-byte/atomic
    (equal (typep$runtime object 'signed-byte)
           (integerp object)))

  (defthm typep$-standard-char
    (equal (typep$runtime object 'standard-char)
           (and (characterp object)
                (standard-char-p object))))

  (defthm typep$-string/atomic
    (equal (typep$runtime object 'string)
           (stringp object)))

  (defthm typep$-symbol
    (equal (typep$runtime object 'symbol)
           (symbolp object)))

  (defthm typep$-t
    (equal (typep$runtime object 't)
           t))

  (defthm typep$-unsigned-byte/atomic
    (equal (typep$runtime object 'unsigned-byte)
           (and (integerp object)
                (<= 0 object))))

;;;; Compound Specifier Rewrite Theorems
  (defthm typep$-and
    (implies (equal (car type-spec) 'and)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((type-specs (cdr type-spec)))
                           (or (null type-specs)
                               (and (typep$ object (car type-specs))
                                    (typep$ object (cons 'and (cdr type-specs))))))))))

  (defthm typep$-complex/compound
    (implies (equal (car type-spec) 'complex)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((type-spec (cadr type-spec)))
                           (and (complex-rationalp object)
                                (if (consp type-spec)
                                    (member (car type-spec) *compound-real-type-specifier-names*)
                                    (member type-spec *atomic-real-subtype-specifiers*))
                                (typep$ (realpart object) type-spec)
                                (typep$ (imagpart object) type-spec)))))))

  (defthm typep$-integer/compound
    (implies (equal (car type-spec) 'integer)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((i (cadr type-spec))
                               (j (caddr type-spec)))
                           (and (integerp object)
                                (interval-designator-p i 'integer)
                                (interval-designator-p j 'integer)
                                (cond
                                  ((equal i '*))
                                  ((consp i)
                                   (< (car i) object))
                                  (t
                                   (<= i object)))
                                (cond
                                  ((equal j '*))
                                  ((consp j)
                                   (< object (car j)))
                                  (t
                                   (<= object j)))))))))

  (defthm typep$-member
    (implies (equal (car type-spec) 'member)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (eqlable-listp (cdr type-spec))
                         (member object (cdr type-spec))))))

  (defthm typep$-mod
    (implies (equal (car type-spec) 'mod)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((i (cadr type-spec)))
                           (and (integerp object)
                                (<= 0 object)
                                (integerp i)
                                (< object i)))))))

  (defthm typep$-not
    (implies (equal (car type-spec) 'not)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (not (typep$ object (cadr type-spec)))))))

  (defthm typep$-or
    (implies (equal (car type-spec) 'or)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((type-specs (cdr type-spec)))
                           (and (consp type-specs)
                                (or (typep$ object (car type-specs))
                                    (typep$ object (cons 'or (cdr type-specs))))))))))

  (defthm typep$-rational/compound
    (implies (equal (car type-spec) 'rational)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((i (cadr type-spec))
                               (j (caddr type-spec)))
                           (and (rationalp object)
                                (interval-designator-p i 'rational)
                                (interval-designator-p j 'rational)
                                (cond
                                  ((equal i '*))
                                  ((consp i)
                                   (< (car i) object))
                                  (t
                                   (<= i object)))
                                (cond
                                  ((equal j '*))
                                  ((consp j)
                                   (< object (car j)))
                                  (t
                                   (<= object j)))))))))

  (defthm typep$-real/compound
    (implies (equal (car type-spec) 'real)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((i (cadr type-spec))
                               (j (caddr type-spec)))
                           (and (real/rationalp object)
                                (interval-designator-p i 'real)
                                (interval-designator-p j 'real)
                                (cond
                                  ((equal i '*))
                                  ((consp i)
                                   (< (car i) object))
                                  (t
                                   (<= i object)))
                                (cond
                                  ((equal j '*))
                                  ((consp j)
                                   (< object (car j)))
                                  (t
                                   (<= object j)))))))))

  (defthm typep$-satisfies
    (implies (equal (car type-spec) 'satisfies)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((predicate (cadr type-spec)))
                           (and (legal-variablep predicate)
                                (apply$ predicate (list object))))))))

  (defthm typep$-signed-byte/compound
    (implies (equal (car type-spec) 'signed-byte)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (signed-byte-p (cadr type-spec) object)))))

  (defthm typep$-string/compound
    (implies (equal (car type-spec) 'string)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((max (cadr type-spec)))
                           (and (stringp object)
                                (integerp max)
                                (<= 0 max)
                                (equal (length object) max)))))))

  (defthm typep$-unsigned-byte/compound
    (implies (equal (car type-spec) 'unsigned-byte)
             (equal (typep$ object type-spec)
                    (and (acl2-type-spec-p type-spec)
                         (let ((i (cadr type-spec)))
                           (and (unsigned-byte-p i object)
                                (< 0 i)))))))

  (defthm typep$-is-total
    (implies (not (acl2-type-spec-p type-spec))
             (not (typep$ object type-spec)))))


;;;; Epilogue
(in-theory
  (disable interval-designator-p
           acl2-type-spec-p
           typep$runtime
           typep$expansion))

(deftheory theory
  '((:e interval-designator-p)
    (:t interval-designator-p)
    (:e acl2-type-spec-p)
    (:t acl2-type-spec-p)
    acl2-type-spec-p-cr
    acl2-type-spec-p-when-atom
    apply$-warrant-acl2-type-spec-p-necc
    apply$-acl2-type-spec-p
    (:e typep$runtime)
    (:e flatten-cd)
    (:t flatten-cd)
    (:e typep$expansion)
    (:t typep$expansion)
    apply$-warrant-typep$expansion-necc
    apply$-typep$expansion
    typep$-atom
    typep$-bit
    typep$-character
    typep$-complex/atomic
    typep$-cons
    typep$-double-float
    typep$-integer/atomic
    typep$-list
    typep$-nil
    typep$-null
    typep$-number
    typep$-ratio
    typep$-rational/atomic
    typep$-real/atomic
    typep$-signed-byte/atomic
    typep$-standard-char
    typep$-string/atomic
    typep$-symbol
    typep$-t
    typep$-unsigned-byte/atomic
    typep$-and
    typep$-complex/compound
    typep$-integer/compound
    typep$-member
    typep$-mod
    typep$-not
    typep$-or
    typep$-rational/compound
    typep$-real/compound
    typep$-satisfies
    typep$-signed-byte/compound
    typep$-string/compound
    typep$-unsigned-byte/compound
    typep$-is-total))

(defsection theory
  :parents (type-spec)
  :short "The @('TYPE-SPEC') package theory."
  :long
  "@(`(:code (list 'deftheory 'theory
                   (list 'quote (let ((world (w state)))
                                  (reverse (acl2::theory 'theory))))))`)")
