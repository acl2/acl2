; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "svtv-stobj-util")

(define svtv-data-defnamemap-core ((design design-p)
                                   (user-names svtv-namemap-p)
                                   svtv-data)
  :guard (modalist-addr-p (design->modalist design))
  :returns (mv err
               (namemap svtv-name-lhs-map-p)
               new-svtv-data)
  (b* ((svtv-data (svtv-data-set-design design svtv-data))
       ((mv err svtv-data) (svtv-data-maybe-compute-flatten svtv-data))
       ((when err)
        (mv err nil svtv-data))
       ((mv errs namemap) (svtv-data-namemap->lhsmap user-names svtv-data)))
    (mv (and errs (msg-list errs)) namemap svtv-data))
  ///
  (defret <fn>-correct
    (and (equal (svtv-data$c->design new-svtv-data) (design-fix design))
         (implies (not err)
                  (equal (svtv-data$c->flatten-validp new-svtv-data) t))))

  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :design))
                  (not (equal key :flatten))
                  (not (equal key :flatten-validp))
                  (not (equal key :moddb))
                  (not (equal key :aliases))
                  (not (equal key :flatnorm-validp))
                  (not (equal key :phase-fsm-validp))
                  (not (equal key :cycle-fsm-validp))
                  (not (equal key :pipeline-validp))
                  (not (equal key :namemap-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))


(define defnamemap-user-names-aux (names (errs-acc true-listp) (acc svtv-namemap-p))
  ;; Process various forms of names into a user namemap. In priority order:
  ;; "signal"          --> ("signal" . "signal")
  ;; (svar . "signal") --> (svar . "signal")
  ;; ("signal" svar)   --> (svar . "signal")
  ;; ("signal" . svar) --> (svar . "signal")
  :returns (mv errs (user-names svtv-namemap-p))
  :prepwork ((local (defthm svar-p-when-stringp
                      (implies (stringp x)
                               (svar-p x))
                      :hints(("Goal" :in-theory (enable svar-p))))))
  (b* (((when (atom names)) (mv (reverse (mbe :logic (true-list-fix errs-acc) :exec errs-acc))
                                (reverse (svtv-namemap-fix acc))))
       ((mv errs-acc acc)
        (b* ((form (car names))
             ((when (stringp form))
              (mv errs-acc (cons (cons form form) acc)))
             ((when (atom form))
              (mv (cons (msg "Non-string atom entry: ~x0" form)
                        errs-acc)
                  acc))
             ((when (stringp (cdr form)))
              (if (svar-p (car form))
                  (mv errs-acc (cons form acc))
                (mv (cons (msg "Non-SVAR paired with string: ~x0" form) errs-acc) acc)))
             ((unless (stringp (car form)))
              (mv (cons (msg "Cons with neither car nor cdr a string: ~x0" form) errs-acc) acc))
             ((when (and (consp (cdr form))
                         (not (cddr form))
                         (svar-p (cadr form))))
              (mv errs-acc (cons (cons (cadr form) (car form)) acc)))
             ((when (svar-p (cdr form)))
              (mv errs-acc (cons (cons (cdr form) (car form)) acc))))
          (mv (cons (msg "Car a string but unrecognized cdr: ~x0" form) errs-acc) acc))))
    (defnamemap-user-names-aux (cdr names) errs-acc acc)))

(define defnamemap-user-names (names)
  :returns (mv err (user-names svtv-namemap-p))
  (b* (((mv errs user-names) (defnamemap-user-names-aux names nil nil))
       ((when errs)
        (mv (msg "Errors in syntax of name inputs. See :xdoc ~x0 for accepted syntax. Errors: ~@1"
                 'defnamemap (msg-list errs))
            user-names)))
    (mv nil user-names)))

(define defnamemap-core ((design design-p)
                         names
                         svtv-data)
  :returns (mv err (namemap svtv-name-lhs-map-p) new-svtv-data)
  :guard (modalist-addr-p (design->modalist design))
  (b* (((mv err user-names) (defnamemap-user-names names))
       ((when err) (mv err nil svtv-data)))
    (svtv-data-defnamemap-core design user-names svtv-data)))
       

(defun assigns-for-defnamemap-sigs (args env signame)
  (declare (xargs :mode :program))
  (if (atom args)
      nil
    (cons (if (consp (car args))
              `(,(caar args) (sv::lhs-eval-zero (,signame ,(cadar args)) ,env))
            (mv-let (sym ign)
              (acl2::decode-varname-for-patbind (car args))
              (declare (ignore ign))
              `(,(car args) (sv::lhs-eval-zero (,signame ,sym) ,env))))
          (assigns-for-defnamemap-sigs (cdr args) env signame))))




(defun defnamemap-events (name namemap pkg-sym)
  (b* ((constname (intern-in-package-of-symbol
                   (concatenate 'string "*" (symbol-name name) "-NAMEMAP*")
                   pkg-sym))
       (signame (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-SIG")
                 pkg-sym))
       (bindername (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "-SIGS")
                    pkg-sym)))
    `(progn (defconst ,constname
              ',(make-fast-alist namemap))
            (defmacro ,signame (name)
              (b* ((look (hons-get name ,constname)))
                (and (not look) (er hard? ',signame "Didn't find signal: ~x0~%" name))
                (list 'quote (cdr look))))
            (def-b*-binder ,bindername
              :body
              #!acl2
              (b* (((mv pre-bindings name rest)
                    (if (and (consp (car forms))
                             (not (eq (caar forms) 'quote)))
                        (mv `((?tmp-for-namemap-sigs ,(car forms)))
                            'tmp-for-namemap-sigs
                            `(check-vars-not-free (tmp-for-namemap-sigs) ,rest-expr))
                      (mv nil (car forms) rest-expr))))
                `(b* (,@pre-bindings
                      . ,(sv::assigns-for-defnamemap-sigs args name ',sv::signame))
                   ,rest))))))





(defun defnamemap-fn (name design names names-p pkg-sym stobj)
  ;; Recognize syntax for pre-evaluated names -- otherwise, evaluate.
  (b* ((names (if (or (eq names nil)
                      (and (consp names)
                           (or (stringp (car names))
                               (and (consp (car names))
                                    (or (stringp (caar names))
                                        (stringp (cdar names)))))))
                  (kwote names)
                names))
       ((unless design)
        (er hard? 'defnamemap "~x0 is required" :design))
       ((unless names-p)
        (er hard? 'defnamemap "~x0 is required" :names))
       (pkg-sym (or pkg-sym name)))
    `(make-event
      (b* (((mv err namemap ,stobj)
            (defnamemap-core ,design ,names ,stobj))
           ((when err)
            (mv err nil state ,stobj))
           (events (defnamemap-events ',name namemap ',pkg-sym)))
        (mv nil events state ,stobj)))))

(defmacro defnamemap (name &key design (names 'nil names-p) pkg-sym (stobj 'svtv-data))
  (defnamemap-fn name design names names-p pkg-sym stobj))


(defxdoc defnamemap
  :parents (svtv-to-fsm)
  :short "Define a mapping between some user-provided names and internal
signals of a design, with convenient macros for accessing them and looking them
up in environments."
  :long "<p>SV designs use fairly verbose and ugly variable names
internally. To access signals of a design less painfully, this macro supports the
definition of maps from user-provided names to SV-internal signals, with macro
support for converting them at translation time and conveniently looking them
up in environments.</p>

<p>Usage:</p>
@({
 (defnamemap myname
    :design *my-sv-design*
    :names '((\"foo.bar[3].baz\"    baz3)  ;; Verilog-style signal names paired with user variable names
             (\"src_data[1]\"       src2)
             (\"result_flags[0]\"   ie))
    :pkg-sym my-pkg        ;; optional, defaults to basename
    :stobj my-svtv-stobj)  ;; optional, defaults to sv::svtv-data
 })

<p>The invocation above produces three things:</p>

<ul>
<li>A constant @('*myname-namemap*'), containing the namemap object</li>

<li>A macro @('myname-sig'), which can be invoked as e.g. @('(myname-sig
baz3)'), which translates to the quoted value that @('baz3') is mapped to in
the namemap</li>

<li>A (see B*) binder @('myname-sigs') that looks up the values of the given
signals in an environment (a @(see svex-env) object) and binds them to
names. For example:
@({
 (b* (((myname-sigs baz3 (my-src src2)) env))
   (list baz3 my-src))
 })

Here the variables @('baz3') and @('my-src') will be bound to (respectively)
the values bound to the SV-internal translations of Verilog signal names
@('\"foo.bar[3].baz\"') and @('\"src_data[0]\"') in @('env').
</li>
</ul>

<h3>@(':names') syntax</h3>

<p>For convenience, this macro supports a few different syntactic forms for the
elements of the @(':names') argument:</p>

<ul>
<li> @('\"verilogname\"') will use the given string itself as the variable name, mapping that string to the SV-internal translation of it.</li>
<li>@('(name . \"verilogname\")')</li>
<li>@('(\"verilogname\" name)') (similar to @(see defsvtv$) syntax within @(':stages')</li>
<li>@('(\"verilogname\" . name)')</li>
</ul>

<p>Additionally, the macro should be able to determine whether the user wanted to
evaluate the names or not. E.g., the following three forms should all have the
same result:</p>

@({
 :names ((\"foo\" bar) ...)
 :names '((\"foo\" bar) ...)
 :names (cons (list \"foo\" 'bar) ...)
 })


<h3>Internals</h3>

<p>The internal representations of these signals are as @(see lhs) objects.  An
LHS is a fixed-width concatenation of fixed segments of signals.  The design
hierarchy has to be consulted to determine the particular LHS that a given
Verilog-style name maps to.  To compute the mapping (in particular, to
translate the Verilog-style names to proper SV-internal LHS objects), the
design is first flattened and its @(see moddb) and <see topic='@(url
alias-normalization)'>aliases</see> mappings are computed.  This step can be
skipped if it was already done previously and the result stored in the @(see
svtv-data) stobj, as it would be by (for example) a prior @(see defsvtv$) or
@(see defcycle) event.</p>

<p>Since the signal names map to LHS objects, the values extracted for them
from the environment are computed with @(see lhs-eval-zero).  This zero-extends
the value of the signal at its width.  The following is a possible expansion for the B* binding:</p>

@({
 (b* (((myname-sigs baz3 (my-src src2)) env))
   (list baz3 my-src))
 -->
 (let* ((baz3 (lhs-eval-zero '((5 :VAR (\"foo\" \"bar\" 3 . \"baz\") . 0)) env))
        (my-src (lhs-eval-zero '((64 \"src_data\" . 64)) env)))
   (list baz3 my-src))
 })

")
        
       

  ;; (svar . "signal") --> (svar . "signal")
  ;; ("signal" svar)   --> (svar . "signal")
  ;; ("signal" . svar) --> (svar . "signal")


