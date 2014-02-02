; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "parse-ranges")
(include-book "parse-lvalues")
(include-book "parse-delays")
(include-book "parse-strengths")
(include-book "../../mlib/expr-tools")
(local (include-book "../../util/arithmetic"))


(local (in-theory (disable ;consp-when-vl-expr-p
                           acl2::consp-under-iff-when-true-listp
                           ;consp-when-vl-atom-p
                           ;consp-when-vl-atomguts-p
                           default-car
                           default-cdr)))




; SPECIAL NOTE ABOUT BLANK PORTS.
;
; The Verilog grammar contains a nasty ambiguity in handling arguments for
; module instances due to the possibility of "blank ports".  Blank ports may
; be used to model an instantiation where a port is not connected to anything.
; For instance, after writing
;
;    module m (a, b, c) ; ... ; endmodule
;
; In another module we may instantiate M, and not connect anything to port b,
; by writing something like this:
;
;    m my_instance (a, , c);
;
; In the grammar, this causes the following ambiguity.  Let Epsilon be the
; empty production, and note that:
;
;   - Epsilon may be a valid ordered_port_connection.  I think of this as a
;     "blank port."  Hence, list_of_port_connections may be Epsilon, and such a
;     think might be thought of as a singleton list containing a blank port.
;
;   - On the other hand, module_instance is said to take an OPTIONAL
;     list_of_port_connections.  If we omit the list_of_port_connections
;     entirely, we might think of it it as an empty list containing no ports.
;
; So in the context of a module instance, what does Epsilon mean?  Is it an
; empty list containing no ports, or is it a singleton list containing one
; blank port.  The grammar is ambiguous.
;
; To explore how Cadence handles this case, I now direct your attention to the
; file blank.v, which explores this question and some related matters.  The
; short of it (in particular see inst1a) is that Cadence seems to treat this as
; an empty list, with no ports.  And a funny consequence of this is that one
; cannot instantiate a one-port module with a blank, unless named argument
; lists are used.
;
; Cadence's handling seems like the most sensible choice, and we are going to
; mimick it.  Because this is somewhat delicate, we also include a number of
; unit tests at the bottom of this file.

; list_of_port_connections ::=
;    ordered_port_connection { ',' ordered_port_connection }
;  | named_port_connection { ',' named_port_connection }
;
; ordered_port_connection ::=
;   {attribute_instance} [expression]
;
; named_port_connection ::=
;   {attribute_instance} '.' identifier '(' [expression] ')'

(defparser vl-parse-list-of-ordered-port-connections (tokens warnings)
  :result (vl-plainarglist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak

  ;; Think of this as "Get me 1+ ordered_port_connections, separated by
  ;; commas."  On success, this always returns at least one port, even if that
  ;; means returning a blank port!  Note that this leads to an unusually weak
  ;; count theorem.

  (seqw tokens warnings

        (atts := (vl-parse-0+-attribute-instances))

        ;; If we see a comma to begin with, then we have a blank port at the
        ;; front of the list.
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-ordered-port-connections))
          (return (cons (make-vl-plainarg :expr nil :atts atts) rest)))

        ;; If we see an rparen, we have just one blank port.
        (when (vl-is-token? :vl-rparen)
          (return (list (make-vl-plainarg :expr nil :atts atts))))

        ;; Otherwise, there should be an expression here.
        (expr := (vl-parse-expression))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-ordered-port-connections)))
        (return (cons (make-vl-plainarg :expr expr :atts atts) rest))))

(defparser vl-parse-named-port-connection (tokens warnings)
  :result (vl-namedarg-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (:= (vl-match-token :vl-dot))
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (unless (vl-is-token? :vl-rparen)
          (expr := (vl-parse-expression)))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-namedarg :name (vl-idtoken->name id)
                                  :expr expr
                                  :atts atts))))

(defparser vl-parse-list-of-named-port-connections (tokens warnings)
  :result (vl-namedarglist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-named-port-connection))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-named-port-connections)))
        (return (cons first rest))))

(defparser vl-parse-list-of-port-connections (tokens warnings)
  :result (vl-arguments-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count weak

  ;; Note that this function always returns a non-empty arguments object
  ;; on success.  The modinst production must explicitly handle the empty
  ;; case and NOT call this function if it sees "()".

  (mv-let (erp val explore new-warnings)
          (seqw tokens warnings
                (args := (vl-parse-list-of-ordered-port-connections))
                (return (vl-arguments nil args)))
          (if erp
              (seqw tokens warnings
                    (args := (vl-parse-list-of-named-port-connections))
                    (return (vl-arguments t args)))
            (mv erp val explore new-warnings))))


; parameter_value_assignment ::= '#' '(' list_of_parameter_assignments ')'
;
; list_of_parameter_assignments ::=
;    expression { ',' expression }
;  | named_parameter_assignment { ',' named_parameter_assignment }
;
; named_parameter_assignment ::=
;  '.' identifier '(' [ mintypmax_expression ] ')'

(defparser vl-parse-named-parameter-assignment (tokens warnings)
  :result (vl-namedarg-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-dot))
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (expr := (vl-parse-mintypmax-expression))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-namedarg :name (vl-idtoken->name id)
                                  :expr expr))))

(defparser vl-parse-list-of-named-parameter-assignments (tokens warnings)
  :result (vl-namedarglist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-named-parameter-assignment))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-named-parameter-assignments)))
        (return (cons first rest))))

(defparser vl-parse-list-of-parameter-assignments (tokens warnings)
  :result (vl-arguments-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-dot)
          (args := (vl-parse-list-of-named-parameter-assignments))
          (return (vl-arguments t args)))
        (exprs := (vl-parse-1+-expressions-separated-by-commas))
        (return (vl-arguments nil (vl-exprlist-to-plainarglist exprs)))))

(defparser vl-parse-parameter-value-assignment (tokens warnings)
  :result (vl-arguments-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-pound))
        (:= (vl-match-token :vl-lparen))
        (args := (vl-parse-list-of-parameter-assignments))
        (:= (vl-match-token :vl-rparen))
        (return args)))






; module_instantiation ::=
;    identifier [ parameter_value_assignment ]
;      module_instance { ',' module_instance } ';'
;
; module_instance ::=
;    identifier [range] '(' [list_of_port_connections] ')'


(defparser vl-parse-module-instance (modname paramargs atts tokens warnings)
  :guard (and (stringp modname)
              (vl-arguments-p paramargs)
              (vl-atts-p atts))
  :result (vl-modinst-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
       (instname := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-lbrack)
         (range := (vl-parse-range)))
       (:= (vl-match-token :vl-lparen))
       ;; Note special avoidance of actually parsing () lists.
       (unless (vl-is-token? :vl-rparen)
         (portargs := (vl-parse-list-of-port-connections)))
       (rparen := (vl-match-token :vl-rparen))
       (return (make-vl-modinst :loc (vl-token->loc instname)
                                :instname (vl-idtoken->name instname)
                                :modname modname
                                :range range
                                :paramargs paramargs
                                :portargs (or portargs
                                              (vl-arguments nil nil))
                                :atts atts))))

(defparser vl-parse-1+-module-instances (modname paramargs atts tokens warnings)
  :guard (and (stringp modname)
              (vl-arguments-p paramargs)
              (vl-atts-p atts))
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-module-instance modname paramargs atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-module-instances modname paramargs atts)))
        (return (cons first rest))))

(defparser vl-parse-module-instantiation (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (modid := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-pound)
          (paramargs := (vl-parse-parameter-value-assignment)))
        (insts := (vl-parse-1+-module-instances (vl-idtoken->name modid)
                                                (or paramargs
                                                    (vl-arguments nil nil))
                                                atts))
        (semi := (vl-match-token :vl-semi))
        (return insts)))






;; BOZO, okay now how do we tell these from UDP instantiations?


; udp_instantiation ::= identifier [drive_strength] [delay2] udp_instance { ',' udp_instance } ';'
;
; udp_instance ::=
;    [name_of_udp_instance] '(' lvalue ',' expression { ',' expression } ')'
;
; name_of_udp_instance ::= identifier [range]

(defparser vl-parse-udp-instance (loc modname str delay atts tokens warnings)
  :guard (and (vl-location-p loc)
              (stringp modname)
              (vl-maybe-gatestrength-p str)
              (vl-maybe-gatedelay-p delay)
              (vl-atts-p atts))
  :result (vl-modinst-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-idtoken)
          (inst-id := (vl-match-token :vl-idtoken))
          (when (vl-is-token? :vl-lbrack)
            (range := (vl-parse-range))))
        (:= (vl-match-token :vl-lparen))
        (lvalue := (vl-parse-lvalue))
        (:= (vl-match-token :vl-comma))
        (exprs := (vl-parse-1+-expressions-separated-by-commas))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-modinst :loc loc
                                 :instname (and inst-id
                                                (vl-idtoken->name inst-id))
                                 :modname modname
                                 :range range
                                 :paramargs (vl-arguments nil nil)
                                 :portargs
                                 (vl-arguments nil (vl-exprlist-to-plainarglist (cons lvalue exprs)))
                                 :str str
                                 :delay delay
                                 :atts atts))))

(defparser vl-parse-1+-udp-instances (loc modname str delay atts tokens warnings)
  :guard (and (vl-location-p loc)
              (stringp modname)
              (vl-maybe-gatestrength-p str)
              (vl-maybe-gatedelay-p delay)
              (vl-atts-p atts))
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-udp-instance loc modname str delay atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-udp-instances loc modname str delay atts)))
        (return (cons first rest))))

(defconst *vl-all-drivestr-kwds*
  (append (strip-cars *vl-ds0-alist*)
          (strip-cars *vl-ds1-alist*)))

(with-output
 :off prove :gag-mode :goals
 (defparser vl-parse-udp-instantiation (atts tokens warnings)
   :guard (vl-atts-p atts)
   :result (vl-modinstlist-p val)
   :resultp-of-nil t
   :true-listp t
   :fails gracefully
   :count strong
   (seqw tokens warnings
        (modname := (vl-match-token :vl-idtoken))
        (when (and (vl-is-token? :vl-lparen)
                   (vl-is-some-token? *vl-all-drivestr-kwds* (cdr tokens)))
          (str := (vl-parse-drive-strength)))
        (when (vl-is-token? :vl-pound)
          (delay := (vl-parse-delay2)))
        (insts := (vl-parse-1+-udp-instances (vl-token->loc modname)
                                             (vl-idtoken->name modname)
                                             str delay atts))
        (:= (vl-match-token :vl-semi))
        (return insts))))



(defun vl-udp/modinst-pick-error-to-report (m-err u-err)
  (declare (xargs :guard t))
  ;; Errors from vl-parse-error-fn have the form (MSG FUNCTION LOC).  This is
  ;; a godawful hack to try to figure out which error is "better".
  (b* ((mloc (if (and (tuplep 3 m-err)
                      (stringp (first m-err))
                      (vl-location-p (third m-err)))
                 (third m-err)
               *vl-fakeloc*))
       (uloc (if (and (tuplep 3 u-err)
                      (stringp (first u-err))
                      (vl-location-p (third u-err)))
                 (third u-err)
               *vl-fakeloc*))
       ((vl-location mloc) mloc)
       ((vl-location uloc) uloc)
       (u-greater (or (> uloc.line mloc.line)
                      (and (= uloc.line mloc.line)
                           (> uloc.col mloc.col)))))
    ;; Prefer the m-err if there's any tie...
    (if u-greater
        u-err
      m-err)))


; It is not always possible to distinguish between udp/module instantiations at
; parse time, because, e.g., "foo bar(x, 3, 5);" might be valid for either one,
; depending upon whether foo is a module or a primitive.  And foo might not yet
; have even been defined, so we really can't tell until later.
;
; The function below is not really that great of a solution.  We just try first
; to treat it as a module instantiation, and if that fails we try to treat it
; as a udp instantiation.  In either case, we make a modinst-p anyway, so
; really all this accomplishes is certain syntactic checks like "if you have a
; strength, you definitely are a UDP so don't allow named arglists", etc.

(defparser vl-parse-udp-or-module-instantiation (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (mv-let (m-err val explore new-warnings)
          (vl-parse-module-instantiation atts tokens)
          (if (not m-err)
              (mv m-err val explore new-warnings)
            (mv-let (u-err val explore new-warnings)
                    (vl-parse-udp-instantiation atts tokens warnings)
                    (if (not u-err)
                        (mv u-err val explore new-warnings)
                      (mv (vl-udp/modinst-pick-error-to-report m-err u-err)
                          nil tokens warnings))))))





;; UNIT TEST FOR ARG PARSING

(local
 (encapsulate
  ()

  (local (include-book "../lexer/lexer")) ;; for making test inputs from strings


  (defund vl-pretty-plainarg (x)
    (declare (xargs :guard (vl-plainarg-p x)))
    (let ((expr (vl-plainarg->expr x)))
      (if (not expr)
          :blank
        (vl-pretty-expr expr))))

  (defprojection vl-pretty-plainarg-list (x)
    (vl-pretty-plainarg x)
    :guard (vl-plainarglist-p x))

  (defund vl-pretty-namedarg (x)
    (declare (xargs :guard (vl-namedarg-p x)))
    (let ((name (vl-namedarg->name x))
          (expr (vl-namedarg->expr x)))
      (list name '<-- (if expr (vl-pretty-expr expr) :blank))))

  (defprojection vl-pretty-namedarg-list (x)
    (vl-pretty-namedarg x)
    :guard (vl-namedarglist-p x))

  (defund vl-pretty-arguments (x)
    (declare (xargs :guard (vl-arguments-p x)))
    (if (vl-arguments->namedp x)
        (list :namedargs
              (vl-pretty-namedarg-list (vl-arguments->args x)))
      (list :plainargs
            (vl-pretty-plainarg-list (vl-arguments->args x)))))

  (defmacro test-parse-modinst-args (&key input (successp 't) expect remainder)
    `(with-output
      :off summary
      (assert! (mv-let (erp val tokens warnings)
                       (vl-parse-udp-or-module-instantiation nil
                                                             (make-test-tokens ,input)
                                                             'warnings)
                       (if ,successp
                           (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                        (not erp))
                                (prog2$ (cw "VAL: ~x0.~%" val)
                                        (and (vl-modinstlist-p val)
                                             (equal (len val) 1)))
                                (let* ((inst (first val))
                                       (args (vl-modinst->portargs inst)))
                                  (and
                                   (prog2$ (cw "ARGS: ~x0.~%" (vl-pretty-arguments args))
                                           (equal (vl-pretty-arguments args) ',expect))
                                   (prog2$ (cw "Atts: ~x0.~%" (vl-modinst->atts inst))
                                           (equal (vl-modinst->atts inst) nil))
                                   (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                           (equal tokens ,remainder))
                                   (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                           (equal warnings 'warnings)))))
                         ;; Otherwise, we expect it to fail.
                         (prog2$ (cw "Erp: ~x0.~%" erp)
                                 erp))))))

  (test-parse-modinst-args
   :input "foo inst (a, b, c);"
   :expect (:PLAINARGS ((ID "a") (ID "b") (ID "c"))))

  (test-parse-modinst-args
   :input "foo inst ();"
   :expect (:PLAINARGS ()))

  (test-parse-modinst-args
   :input "foo inst (a,);"
   :expect (:PLAINARGS ((ID "a") :blank)))

  (test-parse-modinst-args
   :input "foo inst (,a);"
   :expect (:PLAINARGS (:blank (ID "a"))))

  (test-parse-modinst-args
   :input "foo inst (,);"
   :expect (:PLAINARGS (:blank :blank)))

  (test-parse-modinst-args
   :input "foo inst (,,);"
   :expect (:PLAINARGS (:blank :blank :blank)))

  (test-parse-modinst-args
   :input "foo inst (,,,);"
   :expect (:PLAINARGS (:blank :blank :blank :blank)))

  (test-parse-modinst-args
   :input "foo inst (a,,c);"
   :expect (:PLAINARGS ((ID "a") :blank (ID "c"))))

  (test-parse-modinst-args
   :input "foo inst (, a, , c);"
   :expect (:PLAINARGS (:blank (ID "a") :blank (ID "c"))))

  (test-parse-modinst-args
   :input "foo inst (.a(1), .b(2));"
   :expect (:NAMEDARGS (("a" <-- 1) ("b" <-- 2))))

  (test-parse-modinst-args
   :input "foo inst (.a(1), .b(2), );"
   :successp nil)

  (test-parse-modinst-args
   :input "foo inst (.a(1), );"
   :successp nil)

  (test-parse-modinst-args
   :input "foo inst (, .a(1));"
   :successp nil)))

