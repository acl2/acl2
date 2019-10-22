; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "abstract-syntax")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
(include-book "std/strings/binary" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "std/strings/octal" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pretty-printer
  :parents (atj-implementation)
  :short "A pretty-printer for the abstract syntax of Java,
          for ATJ's implementation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This pretty-printer produces text
     in the form of @(tsee msgp) and @(tsee msg-listp) values.
     The latter generally consist of lines of text;
     that is always the case at the top level,
     i.e. a Java compilation unit is turned into a list of lines.
     Some pretty-printing functions produce @(tsee msgp) values
     that other pretty-printing functions
     incorporate into larger text.
     In the pretty-printing functions,
     we consistently use the result names
     @('part') for @(tsee msgp) values that are part of lines,
     @('parts') for @(tsee msg-listp) values that are lists of parts of lines,
     @('line') for @(tsee msgp) values that are individual lines, and
     @('lines') for @(tsee msg-listp) values that are multiple lines.")
   (xdoc::p
    "A separate function writes the lines for a Java compilation unit
     to an output channel, which is associated to a file.
     The newline characters are added to this function;
     they do not appear in the @(tsee msgp) and @(tsee msg-listp) values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

(defrulel msgp-when-stringp
  (implies (stringp x)
           (msgp x)))

(defrulel msgp-when-consp-and-stringp-and-character-alistp
  (implies (and (consp x)
                (stringp (car x))
                (character-alistp (cdr x)))
           (msgp x)))

(local (in-theory (disable msgp)))

(defrulel msg-listp-when-string-listp
  :parents nil
  (implies (string-listp x)
           (msg-listp x))
  :enable msg-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-indent ((level natp))
  :returns (spaces stringp)
  :short "Spaces from the left margin for the specified level of indentation."
  :long
  (xdoc::topstring-p
   "We indent by increments of 4 spaces.")
  (implode (repeat (* 4 level) #\Space))
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system))))

(define print-comma-sep ((parts msg-listp))
  :returns (part msgp :hyp (msg-listp parts))
  :short "Turn zero or more parts into a single part
          containing the initial parts, comma-separated."
  (cond ((endp parts) "")
        ((endp (cdr parts)) (car parts))
        (t (msg "~@0, ~@1"
                (car parts)
                (print-comma-sep (cdr parts))))))

(define print-jchar ((char characterp))
  :returns (part msgp)
  :short "Pretty-print a Java character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This turns an ACL2 character, viewed as a Java character,
     into a form that can be correctly pretty-printed
     when the character is part of a Java character or string literal.
     This takes into account
     not only Java's character and string literal syntax [JLS:3.10],
     but also the fact that the pretty-printer uses ACL2's formatted printing,
     where the tilde has a special meaning.")
   (xdoc::p
    "A single quote or double quote or backslash is preceded by a backslash.
     Double quotes do not need a preceding backslash in a character literal,
     and single quotes do not need a preceding backslash in a string literal,
     but for now for simplicity we escape both single and double quotes
     in both character and string literals.")
   (xdoc::p
    "The other characters with codes between 32 and 125 are left unchanged.")
   (xdoc::p
    "For backspace, horizontal tab, line feed, form feed, and carriage return
     we use the escape sequences
     @('\b'), @('\t'), @('\n'), @('\f'), and @('\r').")
   (xdoc::p
    "All the other characters, including tilde,
     are turned into their octal escapes.
     This is needed for tilde,
     which otherwise would cause errors or misinterpretations
     in ACL2's formatted printing."))
  (b* (((when (member char '(#\' #\" #\\))) (implode (list #\\ char)))
       (code (char-code char))
       ((when (and (<= 32 code)
                   (<= code 125))) (implode (list char)))
       ((when (= code 8)) "\\b")
       ((when (= code 9)) "\\t")
       ((when (= code 10)) "\\n")
       ((when (= code 12)) "\\f")
       ((when (= code 13)) "\\r"))
    (implode (cons #\\ (str::natchars8 code)))))

(define print-jchars ((chars character-listp))
  :returns (part msgp)
  :short "Lift @(tsee print-jchar) to lists."
  :long
  (xdoc::topstring-p
   "The representations of the characters are juxtaposed one after the other.
    This is used only for string literals, not character literals.")
  (cond ((endp chars) "")
        (t (msg "~@0~@1"
                (print-jchar (car chars))
                (print-jchars (cdr chars))))))

(define print-jliteral ((lit jliteralp))
  :returns (part msgp)
  :short "Pretty-print a Java literal."
  :long
  (xdoc::topstring-p
   "We pretty-print our limited form of floating-point literals
    just by appending @('.0') after their decimal integer digits.")
  (jliteral-case
   lit
   :integer (b* ((digits (jintbase-case
                          lit.base
                          :decimal (str::natstr lit.value)
                          :hexadecimal (str::cat "0x" (str::natstr16 lit.value))
                          :octal (if (= lit.value 0)
                                     "0"
                                   (str::cat "0" (str::natstr8 lit.value)))
                          :binary (str::cat "0b" (str::natstr2 lit.value)))))
              (if lit.long?
                  (str::cat digits "L")
                digits))
   :floating (b* ((digits (str::natstr lit.value)))
               (str::cat digits ".0"))
   :boolean (if lit.value "true" "false")
   :character (msg "'~@0'" (print-jchar lit.value))
   :string (msg "\"~@0\"" (print-jchars (explode lit.value)))
   :null "null"))

(define print-jtype ((type jtypep))
  :returns (part msgp)
  :short "Pretty-print a Java type."
  (jtype-case type
              :boolean "boolean"
              :char "char"
              :byte "byte"
              :short "short"
              :int "int"
              :long "long"
              :float "float"
              :double "double"
              :class type.name
              :array (msg "~@0[]" (print-jtype type.comp)))
  :measure (jtype-count type))

(define print-junop ((unop junopp))
  :returns (part msgp)
  :short "Pretty-print a Java unary operator."
  (junop-case unop
              :preinc "++"
              :predec "--"
              :uplus "+"
              :uminus "-"
              :bitcompl "~"
              :logcompl "!"))

(define print-jbinop ((binop jbinopp))
  :returns (part msgp)
  :short "Pretty-print a Java binary operator."
  (jbinop-case binop
               :mul "*"
               :div "/"
               :rem "%"
               :add "+"
               :sub "-"
               :shl "<<"
               :sshr ">>"
               :ushr ">>>"
               :lt "<"
               :gt ">"
               :le "<="
               :ge ">="
               :instanceof "instanceof"
               :eq "=="
               :ne "!="
               :bitand "&"
               :bitxor "^"
               :bitior "|"
               :logand "&&"
               :logor "||"
               :asg "="
               :asg-mul "*="
               :asg-div "/="
               :asg-rem "%="
               :asg-add "+="
               :asg-sub "-="
               :asg-shl "<<="
               :asg-sshr ">>="
               :asg-ushr ">>>="
               :asg-bitand "&="
               :asg-bitxor "^="
               :asg-bitior "|="))

(defines print-jexprs
  :short "Pretty-print Java expressions."

  (define print-jexpr ((expr jexprp))
    :returns (part msgp)
    (jexpr-case expr
                :literal (print-jliteral expr.get)
                :name expr.get
                :newarray (msg "new ~@0[~@1]"
                               (print-jtype expr.type)
                               (print-jexpr expr.size))
                :newarray-init (msg "new ~@0[]{~@1}"
                                    (print-jtype expr.type)
                                    (print-comma-sep
                                     (print-jexpr-list expr.init)))
                :array (msg "~@0[~@1]"
                            (print-jexpr expr.array)
                            (print-jexpr expr.index))
                :newclass (msg "new ~@0(~@1)"
                               (print-jtype expr.type)
                               (print-comma-sep (print-jexpr-list expr.args)))
                :field (msg "~@0.~@1"
                            (print-jexpr expr.target)
                            expr.name)
                :method (msg "~@0(~@1)"
                             expr.name
                             (print-comma-sep (print-jexpr-list expr.args)))
                :smethod (msg "~@0.~@1(~@2)"
                              (print-jtype expr.type)
                              expr.name
                              (print-comma-sep (print-jexpr-list expr.args)))
                :imethod (msg "~@0.~@1(~@2)"
                              (print-jexpr expr.target)
                              expr.name
                              (print-comma-sep (print-jexpr-list expr.args)))
                :postinc (msg "~@0++"
                              (print-jexpr expr.arg))
                :postdec (msg "~@0--"
                              (print-jexpr expr.arg))
                :cast (msg "(~@0) ~@1"
                           (print-jtype expr.type)
                           (print-jexpr expr.arg))
                :unary (msg "~@0~@1"
                            (print-junop expr.op)
                            (print-jexpr expr.arg))
                :binary (msg "~@0 ~@1 ~@2"
                             (print-jexpr expr.left)
                             (print-jbinop expr.op)
                             (print-jexpr expr.right))
                :cond (msg "~@0 ? ~@1 : ~@2"
                           (print-jexpr expr.test)
                           (print-jexpr expr.then)
                           (print-jexpr expr.else))
                :paren (msg "(~@0)"
                            (print-jexpr expr.get)))
    :measure (jexpr-count expr))

  (define print-jexpr-list ((exprs jexpr-listp))
    :returns (parts msg-listp)
    (cond ((endp exprs) nil)
          (t (cons (print-jexpr (car exprs))
                   (print-jexpr-list (cdr exprs)))))
    :measure (jexpr-list-count exprs))

  :verify-guards nil ; done below
  ///
  (verify-guards print-jexpr))

(define print-jline-blank ()
  :returns (line msgp)
  :short "Pretty-print a blank line of code."
  "~%")

(define print-jline ((content msgp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print a (non-blank) line of code."
  :long
  (xdoc::topstring-p
   "The content to print is preceded by
    indentation according to the current level.")
  (msg "~s0~@1~%" (atj-indent indent-level) content))

(define print-jlocvar ((locvar jlocvarp) (indent-level natp))
  :returns (line msgp)
  (b* (((jlocvar locvar) locvar))
    (print-jline (msg "~@0~@1 ~@2 = ~@3;"
                      (if locvar.final? "final " "")
                      (print-jtype locvar.type)
                      locvar.name
                      (print-jexpr locvar.init))
                 indent-level)))

(defines print-jstatems+jblocks
  :short "Pretty-print statements and blocks."
  :long
  (xdoc::topstring-p
   "Note that we print the statements that form a block
    one after the other, without surrounding them with curly braces.
    We do print curly braces when printing
    method declarations and @('if') statements,
    producing valid Java concrete syntax,
    but our current treatment of blocks is somewhat ``improper'',
    because syntactically blocks include curly braces.
    This impropriety should be remedied
    in future versions of this pretty-printer.")

  (define print-jstatem ((statem jstatemp) (indent-level natp))
    :returns (lines msg-listp)
    (jstatem-case
     statem
     :locvar (list (print-jlocvar statem.get indent-level))
     :expr (list (print-jline (msg "~@0;"
                                   (print-jexpr statem.get))
                              indent-level))
     :return (list (if statem.expr?
                       (print-jline (msg "return ~@0;"
                                         (print-jexpr statem.expr?))
                                    indent-level)
                     (print-jline "return;" indent-level)))
     :throw (list (print-jline (msg "throw ~@0;"
                                    (print-jexpr statem.expr))
                               indent-level))
     :if (append (list (print-jline (msg "if (~@0) {"
                                         (print-jexpr statem.test))
                                    indent-level))
                 (print-jblock statem.then (1+ indent-level))
                 (list (print-jline "}" indent-level)))
     :ifelse (append (list (print-jline (msg "if (~@0) {"
                                             (print-jexpr statem.test))
                                        indent-level))
                     (print-jblock statem.then (1+ indent-level))
                     (list (print-jline "} else {" indent-level))
                     (print-jblock statem.else (1+ indent-level))
                     (list (print-jline "}" indent-level)))
     :do (append (list (print-jline "do {" indent-level))
                 (print-jblock statem.body (1+ indent-level))
                 (list (print-jline (msg "} while (~@0);"
                                         (print-jexpr statem.test))
                                    indent-level)))
     :for (append (list (print-jline (msg "for (~@0; ~@1; ~@2) {"
                                          (print-jexpr statem.init)
                                          (print-jexpr statem.test)
                                          (print-jexpr statem.update))
                                     indent-level))
                  (print-jblock statem.body (1+ indent-level))
                  (list (print-jline "}" indent-level))))
    :measure (jstatem-count statem))

  (define print-jblock ((block jblockp) (indent-level natp))
    :returns (lines msg-listp)
    (cond ((endp block) nil)
          (t (append (print-jstatem (car block) indent-level)
                     (print-jblock (cdr block) indent-level))))
    :measure (jblock-count block)))

(define print-jaccess ((access jaccessp))
  :returns (part msgp)
  :short "Pretty-print an access modifier."
  (jaccess-case access
                :public "public "
                :protected "protected "
                :private "private "
                :default ""))

(define print-jfield ((field jfieldp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print a field declaration."
  (b* (((jfield field) field))
    (print-jline (msg "~@0~@1~@2~@3~@4~@5 ~@6 = ~@7;"
                      (print-jaccess field.access)
                      (if field.static? "static " "")
                      (if field.final? "final " "")
                      (if field.transient? "transient " "")
                      (if field.volatile? "volatile " "")
                      (print-jtype field.type)
                      field.name
                      (print-jexpr field.init))
                 indent-level)))

(define print-jresult ((result jresultp))
  :returns (part msgp)
  :short "Pretty-print a method result."
  (jresult-case result
                :type (print-jtype result.get)
                :void "void"))

(define print-jparam ((param jparamp))
  :returns (part msgp)
  :short "Pretty-print a formal parameter."
  (b* (((jparam param) param))
    (msg "~@0~@1 ~@2"
         (if param.final? "final " "")
         (print-jtype param.type)
         param.name)))

(define print-jparam-list ((params jparam-listp))
  :returns (parts msg-listp)
  :short "Pretty-print a formal parameter list."
  (cond ((endp params) nil)
        (t (cons (print-jparam (car params))
                 (print-jparam-list (cdr params))))))

(define print-jmethod ((method jmethodp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a method declaration."
  (b* (((jmethod method) method)
       (modifiers (msg "~@0~@1~@2~@3~@4~@5~@6"
                       (print-jaccess method.access)
                       (if method.abstract? "abstract " "")
                       (if method.static? "static " "")
                       (if method.final? "final " "")
                       (if method.synchronized? "synchronized " "")
                       (if method.native? "native " "")
                       (if method.strictfp? "strictfp " ""))))
    (append (list (print-jline (msg "~@0~@1 ~@2(~@3) ~@4{"
                                    modifiers
                                    (print-jresult method.result)
                                    method.name
                                    (print-comma-sep
                                     (print-jparam-list method.params))
                                    (if method.throws
                                        (msg "throws ~@0 "
                                             (print-comma-sep method.throws))
                                      ""))
                               indent-level))
            (print-jblock method.body (1+ indent-level))
            (list (print-jline "}" indent-level)))))

(define print-jcinitializer ((initializer jcinitializerp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a class initializer."
  (append (list (print-jline (if (jcinitializer->static? initializer)
                                 "static {"
                               "{")
                             indent-level))
          (print-jblock (jcinitializer->code initializer) (1+ indent-level))
          (list (print-jline "}" indent-level))))

(defines print-jclasses+jcmembers

  (define print-jcmember ((member jcmemberp) (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a class member declaration."
    (jcmember-case member
                   :field (list (print-jfield member.get indent-level))
                   :method (print-jmethod member.get indent-level)
                   :class (print-jclass member.get indent-level))
    :measure (jcmember-count member))

  (define print-jcbody-element ((body-element jcbody-element-p)
                                (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a Java class body declaration."
    (jcbody-element-case body-element
                         :member (print-jcmember body-element.get indent-level)
                         :init (print-jcinitializer body-element.get
                                                    indent-level))
    :measure (jcbody-element-count body-element))

  (define print-jcbody-element-list ((body-elements jcbody-element-listp)
                                     (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a sequence of class body declarations."
    :long
    (xdoc::topstring-p
     "Each one is preceded by a blank line.")
    (cond ((endp body-elements) nil)
          (t (append (list (print-jline-blank))
                     (print-jcbody-element (car body-elements)
                                           indent-level)
                     (print-jcbody-element-list (cdr body-elements)
                                                indent-level))))
    :measure (jcbody-element-list-count body-elements))

  (define print-jclass ((class jclassp) (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a class declaration."
    (b* (((jclass class) class)
         (modifiers (msg "~@0~@1~@2~@3~@4"
                         (print-jaccess class.access)
                         (if class.abstract? "abstract " "")
                         (if class.static? "static " "")
                         (if class.final? "final " "")
                         (if class.strictfp? "strictfp " ""))))
      (append (list (print-jline (msg "~@0class ~@1 ~@2{"
                                      modifiers
                                      class.name
                                      (if class.superclass?
                                          (msg "extends ~@0 "
                                               class.superclass?)
                                        ""))
                                 indent-level))
              (print-jcbody-element-list class.body (1+ indent-level))
              (list (print-jline "}" indent-level))))
    :measure (jclass-count class)))

(define print-jclass-list ((classes jclass-listp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a sequence of class declarations."
  :long
  (xdoc::topstring-p
   "Each one is preceded by a blank line.")
  (cond ((endp classes) nil)
        (t (append (list (print-jline-blank))
                   (print-jclass (car classes) indent-level)
                   (print-jclass-list (cdr classes) indent-level)))))

(define print-jimport ((import jimportp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print an import declaration."
  (print-jline (msg "import ~s0~@1;"
                    (if (jimport->static? import) "static " "")
                    (jimport->target import))
               indent-level))

(define print-jimports ((imports jimport-listp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a sequence of import declarations."
  (cond ((endp imports) nil)
        (t (cons (print-jimport (car imports) indent-level)
                 (print-jimports (cdr imports) indent-level)))))

(define print-jcunit ((cunit jcunitp))
  :returns (lines msg-listp)
  :short "Pretty-print a compilation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function does not have an indentation level argument,
     because it starts at level 0.")
   (xdoc::p
    "If there is a package declaration,
     we precede the import declarations (if any)
     with a blank line to separate the latter from the former."))
  (b* (((jcunit cunit) cunit))
    (append (if cunit.package?
                (list (print-jline (msg "package ~@0;"
                                        cunit.package?)
                                   0))
              nil)
            (if (and cunit.imports
                     cunit.package?)
                (cons (print-jline-blank)
                      (print-jimports cunit.imports 0))
              (print-jimports cunit.imports 0))
            (print-jclass-list cunit.types 0))))

(define print-jlines-to-channel ((lines msg-listp) (channel symbolp) state)
  :returns state
  :mode :program
  :short "Write pretty-printed lines to an output channel."
  (cond ((endp lines) state)
        (t (b* (((mv & state) (fmt1! "~@0"
                                     (list (cons #\0 (car lines)))
                                     0 channel state nil)))
             (print-jlines-to-channel (cdr lines) channel state)))))

(defttag :open-input-channel)

(define print-to-jfile ((lines msg-listp) (filename stringp) state)
  :returns state
  :mode :program
  :short "Write pretty-printed lines to a file."
  (b* (((mv channel state) (open-output-channel! filename :character state))
       (state (print-jlines-to-channel lines channel state))
       (state (close-output-channel channel state)))
    state))

(defttag nil)
