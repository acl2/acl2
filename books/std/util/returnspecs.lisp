; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "da-base")
(include-book "look-up")
(program)

(defxdoc returns-specifiers
  :parents (std/util define)
  :short "A concise way to name, document, and prove basic type-like theorems
about a function's return values."

  :long "<p>The @(see define) macro and some other @(see std/util) macros
support a @(':returns') option.  This option provides a concise way to name,
document, and prove basic type-like theorems about the return values of your
functions.  Named return values also allow your function to be used with the
special <see topic='@(url acl2::patbind-ret)'>ret</see> binder for @(see
b*).</p>

<p>The general form is:</p>

@({
    :returns return-spec       ;; for single-value functions
 or :returns (mv return-spec*) ;; for multiple-valued functions
})

<p>There should be exactly one @('return-spec') per return value.  Each
return-spec has the form:</p>

@({
     name               ;; just for naming return values
  or (name [option]*)   ;; for naming, documenting, and proving theorems
})

<p>where @('name') is a symbol and the options can come in any order.  To
distinguish between the two forms of @(':returns'), it is not legal to use
@('mv') as the name of a return value.  The options are:</p>

<dl>

<dt>@('<xdoc>'), any string literal</dt>

<dd>You can document each return value with a string literal.  The string may
make use of @(see xdoc::markup) and @(see xdoc::preprocessor) directives.
Typically these descriptions should be short and not include
document-structuring tags like @('<p>'), @('<ul>'), @('<h3>'), and so forth.
See the section on xdoc integration, below, for more details.</dd>

<dt>@('<return-type>'), a symbol or term</dt>

<dd>When provided, the return type is used to generate a basic type-like
theorems about the return values.</dd>

<dd><b>Important Note</b> in the multiple-valued case, this approach assumes
you are using the @('tools/mv-nth') book.  The theorems we prove target terms
like @('(mv-nth 0 (f ...))') and @('(mv-nth 1 (f ...))').  This will not work
well if @(see mv-nth) is enabled, especially about the 0th return value. For
your convenience, @('define') automatically includes the @('tools/mv-nth')
book.  You really should be using it, you know.</dd>

<dd>As a convenient shorthand, you can use a single symbol like @('evenp').
The theorem to be proven in this case might be, e.g., @('(evenp (f x))') for a
single-valued function, or @('(evenp (mv-nth 3 (f x)))') if this is the
fourth (because of zero-indexing) return value of a multiply-valued function.
The symbol @('t') is explicitly allowed and results in no theorem.  The symbol
@('nil') and keyword symbols are explicitly invalid as return types.</dd>

<dd>In certain cases, you may wish to prove a more complex theorem, e.g., say
we want to prove this return value is always greater than 5.  To support this,
you can write a return type like @('(< 5 ans)'), where @('ans') is the
@('name') of this return value.  You can also refer to the names of other
return values in this term.  To make it easy to distinguish return types from
other options, the return type term must be a cons and must not begin with
@('quote').</dd>

<dt>@(':hyp hyp-term')</dt>

<dd>This option only makes sense when there is a return-type term.  By default,
the return-type theorem is unconditional.  If the theorem needs a hypothesis,
you can put it here.</dd>

<dd>Frequently, the hypothesis you want for a type-like theorem is for the
guards of the function to be met.  As a convenient shorthand, @('hyp-term') may
be:

<ul>
<li>@(':guard') -- use the function's guard as the hypothesis</li>
<li>@(':fguard') -- like @(':guard'), but @(see force) the entire guard</li>
</ul>

If neither of these is what you want, you can provide an arbitrary
@('hyp-term').  Typically this term should mention only the formals of your
function.  The return values of the theorem will not be bound in scope of the
hyp, so trying to refer to them in a hypothesis is generally an error.</dd>

<dt>@(':hints hints-term')</dt>

<dd>This option only makes sense when there is a return-type term.  By default,
this is @('nil'), but when specified, the hints are passed to the proof attempt
for the associated return-type.</dd>

<dt>@(':rule-classes classes')</dt>

<dd>This option only makes sense when there is a return-type term.  By default,
the return-type theorem is added as a @(':rewrite') rule.  If you want to use
other @(see acl2::rule-classes), then you will want to override this default.</dd>

<dt>@(':name name')</dt>

<dd>This allows you to control the name of the associated theorem.</dd>

<dd>The default value of @('name') is <it>type</it>-of-<it>your-function</it>.
For example, @('natp-of-foo').</dd>

</dl>")

(def-primitive-aggregate returnspec
  (name          ; a symbol, the name of this return value
   doc           ; a string, "" when omitted
   return-type   ; t when omitted
   hyp           ; t when omitted
   hints         ; nil when omitted
   hintsp        ; t if hints were provided
   rule-classes  ; :rewrite when omitted
   thm-name      ; NIL (to generate a name) or the name for the theorem
   )
  :tag :return-spec)

(defconst *default-returnspec*
  (make-returnspec :name 'ret
                   :doc ""
                   :return-type t
                   :hyp t
                   :hints nil
                   :hintsp nil
                   :rule-classes :rewrite
                   :thm-name nil))


(defun returnspeclist-p (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (returnspec-p (car x))
         (returnspeclist-p (cdr x)))))

(defun returnspeclist->names (x)
  (declare (xargs :guard (returnspeclist-p x)))
  (if (atom x)
      nil
    (cons (returnspec->name (car x))
          (returnspeclist->names (cdr x)))))



; User-level syntax for returns specifiers

(defun parse-returnspec-item
  (fnname   ; context for error message
   varname  ; name of this return value
   item     ; item in user-level return-spec syntax after keywords are removed,
            ; i.e., it should be a doc string or a return-type indicator, i.e.,
            ; a term or a predicate name
   terms    ; accumulator for return-type indicators
   docs     ; accumulator for doc strings
   )
  "Returns (mv terms docs)"
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-returnspec-item)
       ((when (eq item t))
        ;; T is explicitly allowed as a return type
        (mv (cons item terms) docs))

       ((when (or (eq item nil)
                  (keywordp item)))
        ;; NIL/keywords are explicitly not allowed
        (raise "Error in ~x0: return type for ~x1 is ~x2, which is not ~
                allowed." fnname varname item)
        (mv terms docs))

       ((when (symbolp item))
        (mv (cons `(,item ,varname) terms) docs))

       ((when (and (consp item)
                   (not (eq (car item) 'quote))))
        (mv (cons item terms) docs))

       ((when (stringp item))
        (mv terms (cons item docs))))

    (raise "Error in ~x0, return type for ~x1: expected return type terms or ~
            documentation strings, but found ~x2." fnname varname item)
    (mv terms docs)))

(defun parse-returnspec-items (fnname varname items terms docs)
  "Returns (mv terms docs)"
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-returnspec-items)
       ((when (not items))
        (mv terms docs))
       ((when (atom items))
        (raise "Error in ~x0: expected returnspec-items for ~x1 to be ~
                nil-terminated, but found ~x2 as the final cdr."
               fnname varname items)
        (mv terms docs))
       ((mv terms docs)
        (parse-returnspec-item fnname varname (car items) terms docs)))
    (parse-returnspec-items fnname varname (cdr items) terms docs)))

(defun parse-returnspec
  (fnname  ; context for error messages
   x       ; actual return specifier the user provided
   world   ; for special extra sanity checking
   )
  "Returns a returnspec-p."
  (declare (xargs :guard (plist-worldp world)))
  (b* ((__function__ 'parse-returnspec)
       ((when (eq x 'mv))
        (raise "Error in ~x0: return values may not be named MV." fnname)
        *default-returnspec*)
       ((when (symbolp x))
        ;; Fine, just a name, no docs/type
        ;; A user once got very confused why :returns character-listp
        ;; wasn't proving that his function wasn't returning a character
        ;; list.  So, now, make sure this isn't a defined function.
        (b* ((look (getprop x 'acl2::formals :bad 'acl2::current-acl2-world world))
             ((unless (eq look :bad))
              (raise "Error in ~x0: you named a return value ~x1, which is ~
                      the name of a defined function, but you don't have any ~
                      return type associated with this value.  There's a good ~
                      chance this you meant this to be the return value's ~
                      type instead of its name.~%~%If you really want to name ~
                      this return value ~x1 and not prove anything about it, ~
                      you can use syntax like ~x2.~%" fnname x (list x t))
              *default-returnspec*))
          ;; Else, seems fine, just a name.
          (make-returnspec :name x
                           :doc ""
                           :return-type t
                           :rule-classes :rewrite
                           :hyp nil
                           :hints nil
                           :thm-name nil)))
       ((when (atom x))
        (raise "Error in ~x0: return specifiers must be symbols or lists, but ~
                found: ~x1" fnname x)
        *default-returnspec*)

       ((cons varname options) x)
       ((unless (symbolp varname))
        (raise "Error in ~x0: return specifiers must start with a symbol ~
                name, so this return specifier is not valid: ~x1" fnname x)
        *default-returnspec*)
       ((when (eq varname 'mv))
        (raise "Error in ~x0: return values may not be named MV." fnname)
        *default-returnspec*)

       ((mv kwd-alist other-opts)
        ;; bozo better context for error message here would be good
        (extract-keywords fnname '(:hyp :hints :rule-classes :name) options nil))
       (hyp (if (assoc :hyp kwd-alist)
                (cdr (assoc :hyp kwd-alist))
              t))
       ((when (and (keywordp hyp)
                   (not (eq hyp :guard))
                   (not (eq hyp :fguard))))
        ;; bozo not really a very good place to check for this.
        (raise "Error in ~x0: invalid keyword ~x1 used as a :hyp." fnname hyp)
        *default-returnspec*)
       ((mv hints hintsp)
        (if (assoc :hints kwd-alist)
            (mv (cdr (assoc :hints kwd-alist)) t)
          (mv nil nil)))
       (rule-classes (if (assoc :rule-classes kwd-alist)
                         (cdr (assoc :rule-classes kwd-alist))
                       :rewrite))
       (thm-name (if (assoc :name kwd-alist)
                     (cdr (assoc :name kwd-alist))
                   nil))
       ((mv terms docs)
        (parse-returnspec-items fnname varname other-opts nil nil))
       (return-type
        (cond ((atom terms) ;; no return-type terms, fine, default is t
               t)
              ((atom (cdr terms))
               (car terms))
              (t
               (raise "Error in ~x0: return specifier ~x1 has multiple return ~
                       type terms, but at most one is allowed: ~&2"
                      fnname varname terms))))
       (xdoc
        (cond ((atom docs) ;; no documentation, go figure, default is ""
               "")
              ((atom (cdr docs))
               (car docs))
              (t
               (progn$
                (raise "Error in ~x0: return specifier ~x1 has multiple xdoc ~
                        strings, but at most one is allowed: ~x2."
                       fnname varname terms)
                "")))))
    (make-returnspec :name varname
                     :doc xdoc
                     :return-type return-type
                     :rule-classes rule-classes
                     :hyp hyp
                     :hints hints
                     :hintsp hintsp
                     :thm-name thm-name)))

(defun parse-returnspecs-aux (fnname x world)
  "Returns a returnspeclist-p"
  ;; Assumes they've already been normalized...
  (declare (xargs :guard (plist-worldp world)))
  (if (atom x)
      nil
    (cons (parse-returnspec fnname (car x) world)
          (parse-returnspecs-aux fnname (cdr x) world))))

(defun normalize-returnspecs (fnname x)
  ;; We support two forms of returns:
  ;;  :returns return-spec
  ;;  :returns (mv return-spec ... return-spec)
  ;; We require that return-value names are never MV, so we can just check for MV to
  ;; tell thich kind of return spec we are dealing with.
  ;; This function just converts either form into a list of return specs
  ;; with no MV part.
  (declare (xargs :guard t))
  (b* ((__function__ 'normalize-returnspecs)
       ((unless x)
        ;; Fine, no return spec
        nil)
       ((when (eq x 'mv))
        (raise "Error in ~x0: :returns may not be just MV." fnname))
       ((when (symbolp x))
        ;; Fine
        (list x))
       ((when (atom x))
        (raise "Error in ~x0: :returns may not be ~x1." fnname x))
       ((when (eq (car x) 'mv))
        (if (true-listp (cdr x))
            (cdr x)
          (raise "Error in ~x0: :returns must be nil-terminated." fnname x))))
    (list x)))

(defun parse-returnspecs (fnname x world)
  "Returns a returnspeclist-p"
  (declare (xargs :guard (plist-worldp world)))
  (parse-returnspecs-aux fnname
                         (normalize-returnspecs fnname x)
                         world))


(defun arity-check-returns (name name-fn specs world)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-fn)
                              (returnspeclist-p specs)
                              (plist-worldp world))))
  (b* (((when (atom specs))
        ;; Fine, the user just didn't name/document the return values.
        t)
       (stobjs-out (look-up-return-vals name-fn world))
       ((when (equal (len stobjs-out) (len specs)))
        ;; Fine, arity looks OK.
        t)
       ((when (getprop name-fn 'acl2::non-executablep nil 'acl2::current-acl2-world world))
        ;; The function is non-executable so stobjs-out doesn't necessarily say
        ;; anything coherent, nothing to really check.
        t))
    (er hard? 'arity-check-returns
        "Error in ~x0: ACL2 thinks this function has ~x1 return ~
         values, but :returns has ~x2 entries!"
        name
        (len stobjs-out)
        (len specs))))


(defsection untranslate-and

  (defun untranslate-and (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           ;; (and x) --> x
           (list x))
          ((and (consp x)
                (eq (first x) 'if)
                (equal (len x) 4)
                (equal (fourth x) ''nil))
           ;; (and x y ...) --> (if x (and y ...) nil)
           (cons (second x)
                 (untranslate-and (third x))))
          (t
           (list x)))))

(defun force-each (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(force ,(car x))
          (force-each (cdr x)))))

(defun fancy-force-hyp (x)
  (declare (xargs :guard t))
  (b* ((hyp-list (untranslate-and x)))
    (cons 'and (force-each hyp-list))))

(defun fancy-hyp (x)
  (declare (xargs :guard t))
  (b* ((hyp-list (untranslate-and x)))
    (cons 'and hyp-list)))



(defun returnspec-thm-body (fnname binds x world)
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       ((when (equal x.return-type t)) t)
       (hyp (cond
             ((eq x.hyp :guard) (fancy-hyp (look-up-guard fnname world)))
             ((eq x.hyp :fguard) (fancy-force-hyp (look-up-guard fnname world)))
             (t x.hyp)))
       (concl `(b* (,binds)
                 ,x.return-type)))
    (if (eq hyp t)
        concl
      `(implies ,hyp ,concl))))

(defun returnspec-generate-name (name x singlep badname-okp)
  ;; Get the name for a return-spec theorem.
  ;; Usually we can produce a good name like:
  ;;   natp-of-fn
  ;;   natp-of-fn.new-x
  ;; Or similar.  But, for more complex return-types, say something like
  ;;   (equal (len new-x) (len x))
  ;; we are too dumb to generate a good name.
  ;;
  ;; Badname-okp indicates whether we're willing to accept a "bad", generic
  ;; name of the form "return-type-of-fn" or "return-type-of-fn.new-x" or
  ;; similar.
  ;;
  ;; We'll tolerate bad names if the user is just giving a :returns specifier
  ;; in a function, mainly for backwards compatibility.  (i.e., badname-okp
  ;; will be true).
  ;;
  ;; However, for the new, subsequent return-specs, we'll require explicit
  ;; names for complex conclusions. (i.e., badname-okp will be nil).
  (b* (((returnspec x) x)
       ((when x.thm-name)
        ;; The user provided an explicit name, so use that.
        x.thm-name)
       (multi-suffix (if singlep
                         ""
                       (concatenate 'string "." (symbol-name x.name))))
       ((when (and (tuplep 2 x.return-type)
                   (symbolp (first x.return-type))
                   (equal (second x.return-type) x.name)))
        ;; Simple return type like (natp ans)
        (intern-in-package-of-symbol
         (concatenate 'string
                      (symbol-name (first x.return-type))
                      "-OF-"
                      (symbol-name name)
                      multi-suffix)
         name))
       ((unless badname-okp)
        (er hard? 'returnspec-generate-name
            "Return spec for ~x0, ~x1, must be given an explicit name."
            name x.return-type)))
    ;; Complex return type
    (intern-in-package-of-symbol
     (concatenate 'string "RETURN-TYPE-OF-" (symbol-name name) multi-suffix)
     name)))

(defun returnspec-default-default-hint (fnname id world)
  (and (eql (len (acl2::recursivep fnname t world)) 1) ;; singly recursive
       (let* ((pool-lst (acl2::access acl2::clause-id id :pool-lst)))
         (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
              (cond ((not pool-lst)
                     (let ((formals (look-up-formals fnname world)))
                       `(:induct (,fnname . ,formals)
                         :in-theory (disable (:d ,fnname)))))
                    ((equal pool-lst '(1))
                     `(:computed-hint-replacement
                       ((and stable-under-simplificationp
                             (expand-calls ,fnname)))
                       :in-theory (disable (:d ,fnname)))))))))

(defun returnspec-default-hints (fnname world)
  (let ((entry (cdr (assoc 'returnspec (table-alist 'std::default-hints-table world)))))
    (subst fnname 'fnname entry)))

(defmacro set-returnspec-default-hints (hint)
  `(table std::default-hints-table 'returnspec ',hint))

(set-returnspec-default-hints
 ((returnspec-default-default-hint 'fnname acl2::id world)))


(defun returnspec-sublis (subst str-subst x)
  "Like sublis, but only substitutes symbols, and looks them up both by value and by name."
  (if (atom x)
      (if (symbolp x)
          (let ((look (assoc-equal x subst)))
            (if look
                (cdr look)
              (let ((look (assoc-equal (symbol-name x) subst)))
                (if look
                    (cdr look)
                  (let ((subst (dumb-str-sublis str-subst (symbol-name x))))
                    (if (equal subst (symbol-name x))
                        x
                      (intern-in-package-of-symbol subst x)))))))
        x)
    (cons-with-hint (returnspec-sublis subst str-subst (car x))
                    (returnspec-sublis subst str-subst (cdr x))
                    x)))

(defun returnspec-strsubst (fnname fnname-fn)
  `(("<FN>" . ,(symbol-name fnname))
    ("<FN!>" . ,(symbol-name fnname-fn))))

(defun returnspec-single-thm (name name-fn x body-subst hint-subst badname-okp world)
  "Returns EVENTS"
  ;; Only valid to call AFTER the function has been submitted, because we look
  ;; up the guard/formals from the world.
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-fn)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       (formals (look-up-formals name-fn world))
       (binds `(,x.name (,name-fn . ,formals)))
       (formula (returnspec-sublis body-subst nil (returnspec-thm-body name-fn binds x world)))
       ((when (eq formula t)) nil)
       (strsubst (returnspec-strsubst name name-fn))
       (hints (if x.hintsp
                  (returnspec-sublis hint-subst strsubst x.hints)
                (returnspec-default-hints name-fn world))))
    `((defthm ,(returnspec-generate-name name x t badname-okp)
        ,formula
        :hints ,hints
        :rule-classes ,(returnspec-sublis hint-subst nil x.rule-classes)))))

(defun returnspec-multi-thm (name name-fn binds x body-subst hint-subst badname-okp world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-fn)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       (formula (returnspec-sublis body-subst nil (returnspec-thm-body name-fn binds x world)))
       ((when (equal formula t)) nil)
       (strsubst (returnspec-strsubst name name-fn))
       (hints (if x.hintsp
                  (returnspec-sublis hint-subst strsubst x.hints)
                (returnspec-default-hints name-fn world))))
    `((defthm ,(returnspec-generate-name name x nil badname-okp)
        ,formula
        :hints ,hints
        :rule-classes ,(returnspec-sublis hint-subst nil x.rule-classes)))))

(defun returnspec-multi-thms (name name-fn binds x body-subst hint-subst badname-okp world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-fn)
                              (returnspeclist-p x)
                              (plist-worldp world))))
  (if (atom x)
      nil
    (append (returnspec-multi-thm name name-fn binds (car x) body-subst hint-subst badname-okp world)
            (returnspec-multi-thms name name-fn binds (cdr x) body-subst hint-subst badname-okp world))))



(defun make-symbol-ignorable (x)
  (declare (xargs :guard (symbolp x)))
  (intern-in-package-of-symbol
   (concatenate 'string "?" (symbol-name x))
   x))

(defun make-symbols-ignorable (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (atom x)
      nil
    (cons (make-symbol-ignorable (car x))
          (make-symbols-ignorable (cdr x)))))

(defun returnspec-mv-nth-subst (names idx call)
  (if (atom names)
      nil
    (cons (cons (car names) `(mv-nth ,idx ,call))
          (returnspec-mv-nth-subst (cdr names) (1+ idx) call))))

(defun returnspec-symbol-packages (syms)
  (if (atom syms)
      nil
    (add-to-set-equal (symbol-package-name (car syms))
                      (returnspec-symbol-packages (cdr syms)))))

(defun returnspec-call-sym-pairs (packages call)
  (if (atom packages)
      nil
    (cons (cons (intern$ "<CALL>" (car packages)) call)
          (returnspec-call-sym-pairs (cdr packages) call))))




(defun returnspec-return-value-subst (name name-fn formals names)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp names))))
  ;; NOTE: These are intended for use with returnspec-sublis, which only
  ;; replaces symbols, but will also look up the name of a symbol.  So a
  ;; binding whose key is a string affects all symbols with that name, whereas
  ;; bindings of symbols only affect those exact symbols.
  (b* ((call (cons name-fn formals))
       (both-subst `(("<CALL>" . ,call)
                     ("<FN>" . ,name)
                     ("<FN!>" . ,name-fn)
                     ("<VALUES>" . ,names)))
       ((when (eql (len names) 1))
        (mv both-subst (cons (cons (car names) call) both-subst))))
    (mv both-subst (append both-subst (returnspec-mv-nth-subst names 0 call)))))

(defun returnspec-thms (name name-fn specs world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-fn)
                              (returnspeclist-p specs)
                              (plist-worldp world))))
  (b* ((- (arity-check-returns name name-fn specs world))
       ((unless specs)
        nil)
       (badname-okp t)
       (names   (returnspeclist->names specs))
       (formals (look-up-formals name-fn world))
       ((mv body-subst hint-subst) (returnspec-return-value-subst name name-fn formals names))
       ((when (equal (len specs) 1))
        (returnspec-single-thm name name-fn (car specs) body-subst hint-subst badname-okp world))
       (ignorable-names (make-symbols-ignorable names))
       (binds   `((mv . ,ignorable-names) (,name-fn . ,formals))))
    (returnspec-multi-thms name name-fn binds specs body-subst hint-subst badname-okp world)))
