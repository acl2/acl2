; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-identifier-rules
  :short "Rules related to C identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "During symbolic execution,
     C identifiers in the computation state
     have the canonical form @('(ident <string>)'),
     where @('<string>') is a quoted string constant.
     To keep them in this form, we leave @(tsee ident) disabled.
     Since the symbolic execution
     sometimes applies @(tsee ident-fix) to identifiers,
     we enable @('ident-fix-when-identp') and @('identp-of-ident'),
     so that @(tsee ident-fix) can be rewritten away.
     Sometimes the symbolic execution produces equalities over identifiers:
     we introduce a rule that reduces those to equalities over strings.
     Since the latter equalities involve the string fixer,
     we enable its executable counterpart.
     Similarly, sometimes the symbolic execution produces
     calls of @(tsee <<) over identifiers:
     we introduce a rule that reduces those to @(tsee <<) over strings.")
   (xdoc::p
    "In the course of symbolic execution,
     terms appears of the form @('(exec-fun <ident> ...)'),
     where @('<ident>') is a quoted identifier constant,
     obtained by the C ASTs being executed.
     This @('<ident>') does not have the form @('(ident <string>'));
     we introduce and enable a rule
     to turn @('<ident>') into @('(ident <string>')
     when it appears in @(tsee exec-fun).
     We introduce similar rules for terms of the form
     @('(create-var <ident> ...)'),
     @('(read-var <ident> ...)'),
     @('(read-static-var <ident> ...)'),
     @('(write-var <ident> ...)'),
     @('(write-static-var <ident> ...)'),
     @('(type-struct <ident>)'),
     @('(exec-member <ident>)'), and
     @('(exec-memberp ... <ident> ...)')."))

  (defruled equal-of-ident-and-const
    (implies (and (syntaxp (and (quotep x)
                                (quotep c)))
                  (identp c))
             (equal (equal (ident x) c)
                    (equal (str-fix x)
                           (ident->name c)))))

  (defruled equal-of-ident-and-ident
    (equal (equal (ident x)
                  (ident y))
           (equal (str-fix x)
                  (str-fix y))))

  (defruled <<-of-ident-and-ident
    (equal (<< (ident x)
               (ident y))
           (<< (str-fix x)
               (str-fix y)))
    :enable (<< lexorder ident))

  (defruled exec-fun-of-const-identifier
    (implies (and (syntaxp (quotep fun))
                  (identp fun))
             (equal (exec-fun fun
                              args compst fenv limit)
                    (exec-fun (ident (ident->name fun))
                              args compst fenv limit))))

  (defruled read-static-var-of-const-identifier
    (implies (and (syntaxp (quotep var))
                  (identp var))
             (equal (read-static-var var compst)
                    (read-static-var (ident (ident->name var)) compst))))

  (defruled create-var-of-const-identifier
    (implies (and (syntaxp (quotep var))
                  (identp var))
             (equal (create-var var val compst)
                    (create-var (ident (ident->name var)) val compst))))

  (defruled read-var-of-const-identifier
    (implies (and (syntaxp (quotep var))
                  (identp var))
             (equal (read-var var compst)
                    (read-var (ident (ident->name var)) compst))))

  (defruled write-var-of-const-identifier
    (implies (and (syntaxp (quotep var))
                  (identp var))
             (equal (write-var var val compst)
                    (write-var (ident (ident->name var)) val compst))))

  (defruled write-static-var-of-const-identifier
    (implies (and (syntaxp (quotep var))
                  (identp var))
             (equal (write-static-var var val compst)
                    (write-static-var (ident (ident->name var)) val compst))))

  (defruled type-struct-of-const-identifier
    (implies (and (syntaxp (quotep tag))
                  (identp tag))
             (equal (type-struct tag)
                    (type-struct (ident (ident->name tag))))))

  (defruled exec-member-of-const-identifier
    (implies (and (syntaxp (quotep mem))
                  (identp mem))
             (equal (exec-member val mem)
                    (exec-member val (ident (ident->name mem))))))

  (defruled exec-memberp-of-const-identifier
    (implies (and (syntaxp (quotep mem))
                  (identp mem))
             (equal (exec-memberp val mem compst)
                    (exec-memberp val (ident (ident->name mem)) compst))))

  (defruled exec-arrsub-of-memberp-of-const-identifier
    (implies
     (and (syntaxp (quotep mem))
          (identp mem))
     (equal
      (exec-arrsub-of-memberp str mem sub compst)
      (exec-arrsub-of-memberp str (ident (ident->name mem)) sub compst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-identifier-rules*
  :short "List of rules related to C identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see atc-identifier-rules)."))
  '(ident-fix-when-identp
    identp-of-ident
    equal-of-ident-and-const
    equal-of-ident-and-ident
    <<-of-ident-and-ident
    (:e str-fix)
    (:e identp)
    (:e ident->name)
    exec-fun-of-const-identifier
    create-var-of-const-identifier
    read-var-of-const-identifier
    read-static-var-of-const-identifier
    write-var-of-const-identifier
    write-static-var-of-const-identifier
    type-struct-of-const-identifier
    exec-member-of-const-identifier
    exec-memberp-of-const-identifier
    exec-arrsub-of-memberp-of-const-identifier))
