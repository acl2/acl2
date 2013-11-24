; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2012 Centaur Technology
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

(in-package "STD")
(include-book "da-base")
(include-book "look-up")
(include-book "misc/assert" :dir :system)
(program)

(defxdoc returns-specifiers
  :parents (std/util define)
  :short "A concise way to name, document, and prove basic type-like theorems
about a function's return values."

  :long "<p>BOZO rewrite this to be more general.</p>

<p>A more elaborate extended option is @(':returns').  This is a concise way to
name, document, and prove basic type-like theorems about the return values of
your functions.  The general form is:</p>

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

</dl>")

(def-primitive-aggregate returnspec
  (name          ; a symbol, the name of this return value
   doc           ; a string, "" when omitted
   return-type   ; t when omitted
   hyp           ; t when omitted
   hints         ; nil when omitted
   rule-classes  ; :rewrite when omitted
   )
  :tag :return-spec)

(defconst *default-returnspec*
  (make-returnspec :name 'ret
                   :doc ""
                   :return-type t
                   :hyp t
                   :hints nil
                   :rule-classes :rewrite))


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
        (b* ((look (getprop x 'acl2::formals :bad
                            'acl2::current-acl2-world world))
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
                           :hints nil)))
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
        (extract-keywords fnname '(:hyp :hints :rule-classes) options nil))
       (hyp (if (assoc :hyp kwd-alist)
                (cdr (assoc :hyp kwd-alist))
              t))
       ((when (and (keywordp hyp)
                   (not (eq hyp :guard))
                   (not (eq hyp :fguard))))
        ;; bozo not really a very good place to check for this.
        (raise "Error in ~x0: invalid keyword ~x1 used as a :hyp." fnname hyp)
        *default-returnspec*)
       (hints (if (assoc :hints kwd-alist)
                  (cdr (assoc :hints kwd-alist))
                nil))
       (rule-classes (if (assoc :rule-classes kwd-alist)
                         (cdr (assoc :rule-classes kwd-alist))
                       :rewrite))
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
                     :hints hints)))

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
  ;; We require that names are never MV, so we can just check for MV to
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
           (list x))))

  (local
   (progn
     (assert! (equal (untranslate-and 'x) '(x)))
     (assert! (equal (untranslate-and 't) '(t)))
     (assert! (equal (untranslate-and '(if x y z)) '((if x y z))))
     (assert! (equal (untranslate-and '(if x y 'nil)) '(x y)))
     (assert! (equal (untranslate-and '(if x (if a b c) 'nil)) '(x (if a b c))))
     (assert! (equal (untranslate-and '(if x (if a b 'nil) 'nil)) '(x a b))))))

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

(defun returnspec-single-thm (fnname x world)
  "Returns EVENTS"
  ;; Only valid to call AFTER the function has been submitted, because we look
  ;; up the guard/formals from the world.
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       ((when (equal x.return-type t))
        nil)
       (formals (look-up-formals fnname world))
       (hyp     (cond ((eq x.hyp :guard)
                       (fancy-hyp (look-up-guard fnname world)))
                      ((eq x.hyp :fguard)
                       (fancy-force-hyp (look-up-guard fnname world)))
                      (t
                       x.hyp)))
       (hints x.hints)
       (concl   `(let ((,x.name (,fnname . ,formals)))
                   ,x.return-type))
       (formula (if (eq hyp t)
                    concl
                  `(implies ,hyp ,concl))))
    `((defthm ,(intern-in-package-of-symbol
                (concatenate 'string "RETURN-TYPE-OF-" (symbol-name fnname))
                fnname)
        ,formula
        :hints ,hints
        :rule-classes ,x.rule-classes))))

(defun returnspec-multi-thm (fnname binds x world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       ((when (equal x.return-type t))
        nil)
       (hyp (cond
             ((eq x.hyp :guard) (fancy-hyp (look-up-guard fnname world)))
             ((eq x.hyp :fguard) (fancy-force-hyp (look-up-guard fnname world)))
             (t x.hyp)))

       (hints x.hints)
       (concl `(b* (,binds)
                 ,x.return-type))
       (formula (if (eq hyp t)
                    concl
                  `(implies ,hyp ,concl))))
    `((defthm ,(intern-in-package-of-symbol
                (concatenate 'string "RETURN-TYPE-OF-" (symbol-name fnname)
                             "." (symbol-name x.name))
                fnname)
        ,formula
        :hints ,hints
        :rule-classes ,x.rule-classes))))

(defun returnspec-multi-thms (fnname binds x world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspeclist-p x)
                              (plist-worldp world))))
  (if (atom x)
      nil
    (append (returnspec-multi-thm fnname binds (car x) world)
            (returnspec-multi-thms fnname binds (cdr x) world))))





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

(defun returnspec-thms (fnname specs world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspeclist-p specs)
                              (plist-worldp world))))
  (b* (((unless specs)
        nil)
       ((when (equal (len specs) 1))
        (returnspec-single-thm fnname (car specs) world))
       (names   (returnspeclist->names specs))
       (ignorable-names (make-symbols-ignorable names))
       (formals (look-up-formals fnname world))
       (binds   `((mv . ,ignorable-names) (,fnname . ,formals))))
    (returnspec-multi-thms fnname binds specs world)))
