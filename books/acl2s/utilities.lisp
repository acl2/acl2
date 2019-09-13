#|$ACL2s-Preamble$;
; Copyright (C) 2018, Northeastern University
; Written by Pete Manolios
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "kestrel/utilities/proof-builder-macros" :dir :system)

(defxdoc ACL2s-utilities
  :parents (acl2::acl2-sedan)
  :short "Utilities used in ACL2s."
  :long "<p>
This is a collection of utilities used in ACL2s, the ACL2 Sedan.
</p>
")

(defxdoc acl2-pc::repeat-until-done
  :parents (acl2::proof-builder-commands acl2s-utilities)
  :short "A proof-builder command that repeats the given instructions
  until all goals have been proved" 
  :long "<p>
@({
 Example:
 (repeat-until-done induct (repeat bash))

 General Form:
 (repeat-until-done instr1 ... instrk)
 })
</p>

<p>where each @('instri') is a proof-builder instruction.
</p>
")

(define-pc-macro repeat-until-done (&rest instrs)
  (value
   `(repeat (do-all
             ,@(append instrs 
                       `((negate (when-not-proved fail))))))))

(defxdoc make-n-ary-macro
  :parents (acl2s-utilities)
  :short "A macro that 
creates an arbitrary-arity macro given a binary function
and associates the function name with the macro name using
@(see add-macro-fn)."
  :long "<p>
@({
 Examples:
 (make-n-ary-macro set-union binary-set-union nil t)

 (make-n-ary-macro ^ expt 1)

 General Form:
 (make-n-ary-macro new-macro-name binary-fun-name identity right-associate-p)
 })
</p>
 
<p>where @('new-macro-name') is the name of the macro to define,
@('binary-fun-name') is the name of an existing binary function and
@('identity') is what the macro should return with no arguments.
@('right-associate-p') is an optional argument, which when set to
@('t') flattens right-associated arguments (see @(see add-macro-fn)).
</p>

<p>
Given
one argument, the macro will just return that argument. Given more
than one argument, the macro will expand to a right-associated call of
the function. For example:

@({
(set-union) expands to nil

(set-union arg1) expands to arg1

(set-union arg1 arg2) expands to (binary-set-union arg1 arg2)

(set-union arg1 arg2 arg3) expands to 
(binary-set-union arg1 (binary-set-union arg2 arg3))

and so on.
})
</p>
")

(defmacro make-n-ary-macro (macro bin-fun id &optional
                                  right-associate-p)
  (declare (xargs :guard (and (symbolp macro) (symbolp bin-fun)
                              (booleanp right-associate-p))))
  `(progn
     (defmacro ,macro (&rest rst)
       (cond ((null rst) ,id)
             ((null (cdr rst)) (car rst))
             (t (xxxjoin ',bin-fun rst))))
     (add-macro-fn ,macro ,bin-fun ,right-associate-p)))

(defxdoc test-then-skip-proofs
  :parents (acl2s-utilities acl2::cgen)
  :short "The ACL2s version of @('skip-proofs')."
  :long"<p>
A macro that is similar to @('skip-proofs'), except that we first perform
testing. The macro supports testing for @(see thm), 
@(see defthm), @(see defcong), @(see defequiv), and
@(see defrefinement) forms. All other forms are just turned into
@('skip-proof')s forms, without testing.
</p>
")

;; If there are opportunities to do so, we should extend
;; test-then-skip-proofs so that it supports more forms.

(defmacro test-then-skip-proofs (thm)
  (declare (xargs :guard (true-listp thm)))
  (cond
   ((equal (car thm) 'defthm)
    `(encapsulate ()
      (acl2s::test? ,(third thm))
      (skip-proofs ,thm)))
   ((equal (car thm) 'thm)
    `(encapsulate ()
      (acl2s::test? ,(second thm))
      (skip-proofs ,thm)))
   ((member (car thm) '(acl2::defcong acl2::defequiv acl2::defrefinement))
    `(make-event
      (er-let* ((defthm (acl2::macroexpand1* ',thm 'ctx (w state) state)))
               (value `(encapsulate
                        ()
                        (acl2s::test? ,(second (third defthm)))
                        (skip-proofs ,',thm))))))
   (t `(skip-proofs ,thm))))

(defxdoc thm-no-test
  :parents (acl2s-utilities acl2::cgen)
  :short "A version of @('thm') with testing disabled."
  :long"<p>
A macro that uses @('with-outer-locals') to locally turn off
@('cgen') testing and then calls @('thm').
</p>
")

(defmacro thm-no-test (&rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (make-event (mv-let (erp val state)
                        (thm ,@args)
                        (declare (ignore val))
                        (cond (erp (er soft 'thm "The thm failed"))
                              (t (value `(value-triple :passed))))))))

(defxdoc defthm-no-test
  :parents (acl2s-utilities acl2::cgen)
  :short "A version of @('defthm') with testing disabled."
  :long"<p>
A macro that uses @('with-outer-locals') to locally turn off
@('cgen') testing and then calls @('defthm').
</p>
")

(defmacro defthm-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defthm ,name ,@args)))

;---------------------------------------------------------------------------
; Symbol generation utilities

; The following functions, macros and theorems are used to generate
; symbols. A general principle for symbol generation is that generated
; symbols should be in the current package. Doing that in ACL2
; requires using make-event in a top level form to determine the
; current package from state and then passing this package to
; functions that generate symbols. The code below is used in
; defthm.lisp to define defequiv, defrefinement and defcong.

#|
(defun sym-string-listp (l)
  (declare (xargs :guard t))
  (if (consp l)
      (and (or (symbolp (car l))
               (stringp (car l)))
           (sym-string-listp (cdr l)))
    (null l)))

(defun symbol-string-app (l)
  (declare (xargs :guard (sym-string-listp l)))
  (if (endp l)
      ""
    (concatenate 'string (if (symbolp (car l))
                             (symbol-name (car l))
                           (car l))
                 (symbol-string-app (cdr l)))))

(defthm symbol-string-app-contract-thm
  (implies (sym-string-listp l)
           (stringp (symbol-string-app l))))
|#

(defun best-package (x y)
  (declare (xargs :guard (and (stringp x) (stringp y))))
  (let* ((p '("" "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"
              "COMMON-LISP" "LISP" "KEYWORD" "CGEN"
              "DEFDATA" "ACL2" "ACL2S"))
         (ly (len (member-equal y p)))
         (lx (len (member-equal x p))))
    (if (< lx ly) x y)))
    
(defun best-package-symbl-list (l s)
  (declare (xargs :guard (and (good-atom-listp l) (stringp s))))
  (cond ((endp l) s)
        ((symbolp (car l))
         (best-package-symbl-list
          (cdr l)
          (best-package (symbol-package-name (car l)) s)))
        (t (best-package-symbl-list (cdr l) s))))

(defthm best-package-symbl-list-stringp
  (implies (and (good-atom-listp l) (stringp s))
           (stringp (best-package-symbl-list l s))))

(defthm best-package-symbl-list-not-empty
  (implies (and (good-atom-listp l) (stringp s) (not (equal s "")))
           (not (equal (best-package-symbl-list l s) ""))))

#|
Now in defthm.lisp

(defun fix-pkg (pkg)
  (declare (xargs :guard (and (or (null pkg) (stringp pkg))
                              (not (equal pkg "")))))
  (if (and pkg (not (equal pkg *main-lisp-package-name*)))
      pkg
    "ACL2"))

(defmacro fix-intern$ (name pkg)
  `(intern$ ,name (fix-pkg ,pkg)))

(defmacro fix-intern-in-pkg-of-sym (string sym)
; This one is a bit different in ACL2 source file defthm.lisp.
  `(intern-in-package-of-symbol ,string (fix-sym ,sym)))

(defun pack-to-string (l)
  (declare (xargs :guard (good-atom-listp l)))
  (coerce (packn1 l) 'string))

(defun gen-sym-sym (l sym)

; This is a version of packn-pos that fixes the package (so that it's not
; *main-lisp-package-name*).

  (declare (xargs :guard (and (good-atom-listp l)
                              (symbolp sym))))
  (fix-intern-in-pkg-of-sym (pack-to-string l) sym))

|#

(defun fix-sym (sym)
  (declare (xargs :guard (symbolp sym)))
  (if (equal (symbol-package-name sym) "COMMON-LISP")
      (pkg-witness "ACL2")
    sym))

(defthm character-listp-explode-nonnegative-integer
  (implies (and (integerp x)
                (<= 0 x)
                (print-base-p b)
                (character-listp ans))
           (character-listp (explode-nonnegative-integer x b ans))))

(defthm character-listp-explode-atom
  (implies (and (acl2-numberp x)
                (print-base-p b))
           (character-listp (explode-atom x b))))


(verify-termination fix-pkg)
(verify-termination fix-sym)
(verify-termination pack-to-string)
(verify-termination gen-sym-sym)

(verify-guards fix-pkg)
(verify-guards fix-sym)
(verify-guards pack-to-string)
(verify-guards gen-sym-sym)

(defun gen-sym-pkg-fn (l pkg)
  (declare (xargs :guard (and (good-atom-listp l)
                              (or (null pkg) (stringp pkg))
                              (not (equal pkg "")))))
  (fix-intern$ (pack-to-string l) pkg))

(defmacro gen-sym-pkg (l &optional pkg)
  (declare (xargs :guard t))
  `(gen-sym-pkg-fn ,l ,pkg))

(defun make-symbl-fun (l pkg)
  (declare (xargs :guard (and (good-atom-listp l)
                              (or (null pkg) (stringp pkg))
                              (not (equal pkg "")))))
  (fix-intern$ (pack-to-string l)
               (if pkg pkg (best-package-symbl-list l "ACL2"))))

; l is a list containing strings or symbols.
(defmacro make-symbl (l &optional pkg)
  (declare (xargs :guard t))
  `(make-symbl-fun ,l ,pkg))

; l is a list containing strings or symbols.
(defmacro make-sym (s suf &optional pkg)
; Returns the symbol s-suf.
  (declare (xargs :guard t))
  `(make-symbl (list ,s '- ,suf) ,pkg))

(defun get-alist (key alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal key alist)))

(defxdoc n<
  :parents (acl2s-utilities acl2::well-founded-relation)
  :short "The well-founded less-than relation on natural numbers."
  :long "<p>
If @('x') and @('y') are both natural numbers then @('(n< x y)') is true
iff @('x') is strictly less than @('y'). @('n<') is well-founded on the natural
numbers and is useful for beginners who want to use measure
functions over natural numbers.
</p>
")

(defun nat-id (x)
  (declare (xargs :guard (natp x)))
  x)

(defun n< (x y)
  (declare (xargs :guard (and (natp x) (natp y))))
  (< x y))

(defthm less-than-is-well-founded-relation
  (and (implies (natp x) (o-p (nat-id x)))
       (implies (and (natp x)
                     (natp y)
                     (n< x y))
                (o< (nat-id x) (nat-id y))))
  :rule-classes :well-founded-relation)

(defmacro defthm-test-no-proof (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled t))
    (test? ,@args)
    (skip-proofs (defthm ,name ,@args))))

(defmacro defthmskipall (name &rest args)
  `(skip-proofs (defthm-no-test ,name ,@args)))

(defmacro defun-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defun ,name ,@args)))

; I tried a few different ways of doing this, so I figured I would
; leave this here so that if I make any other changes, there is less
; updating to do.
(defun tbl-set-fn (tbl key val)
  `(table ,tbl ,key ,val))

(defun tbl-get-fn (tbl key)
  `(b* ((wrld (w state)))
     (cdr (assoc-eq ,key (table-alist ',tbl wrld)))))

(defun all-tlps (l)
  (declare (xargs :guard t))
  (or (atom l)
      (and (true-listp l)
           (all-tlps (car l))
           (all-tlps (cdr l)))))
                     
(mutual-recursion
 (defun subst-var (new old form)
   (declare (xargs :guard (and (atom old) (all-tlps form))))
   (cond ((atom form)
          (cond ((equal form old) new)
                (t form)))
         ((acl2::fquotep form) form)
         (t (cons (car form)
                  (subst-var-lst new old (cdr form))))))

 (defun subst-var-lst (new old l)
   (declare (xargs :guard (and (atom old) (true-listp l) (all-tlps l))))
   (cond ((endp l) nil)
         (t (cons (subst-var new old (car l))
                  (subst-var-lst new old (cdr l)))))))

(mutual-recursion
 (defun subst-fun-sym (new old form)
   (declare (xargs :guard (and (legal-variablep old)
                               (legal-variablep new)
                               (all-tlps form))))
   (cond ((atom form)
          form)
         ((acl2::fquotep form) form)
         (t (cons (if (atom (car form))
                      (subst-var new old (car form))
                    (subst-fun-sym new old (car form)))
                  (subst-fun-lst new old (cdr form))))))

 (defun subst-fun-lst (new old l)
   (declare (xargs :guard (and (legal-variablep old)
                               (legal-variablep new)
                               (true-listp l)
                               (all-tlps l))))
   (cond ((endp l) nil)
         (t (cons (subst-fun-sym new old (car l))
                  (subst-fun-lst new old (cdr l)))))))

(mutual-recursion
 (defun subst-expr1 (new old term)
   (declare (xargs :guard (all-tlps term) :guard-debug t))
   (cond
    ((equal term old) new)
    ((atom term) term)
    ((quotep term) term)
    (t (cons (car term)
             (subst-expr1-lst new old (cdr term))))))

 (defun subst-expr1-lst (new old args)
   (declare (xargs :guard (and (true-listp args) (all-tlps args))))
   (if (endp args)
       nil
     (cons (subst-expr1 new old (car args))
           (subst-expr1-lst new old (cdr args))))))

(defun subst-expr (new old term)
  (declare (xargs :guard (and (not (quotep old)) (all-tlps term))))
  (if (atom old)
      (subst-var new old term)
    (subst-expr1 new old term)))

#|

;; PETE: These functions were leading to errors. For example, in
;; parse-defunc, the check for recp was using fun-sym-in-termp, and
;; this was leading to a guard error. The code I now use uses
;; pseudo-translate and all-ffnames.  The subst-fun-sym functions were
;; also updated to do a better job of dealing with lambdas, let, let*,
;; etc, but they are probably not bullet-proof.

(mutual-recursion
 (defun fun-syms-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil))
   (cond ((acl2::variablep term) nil)
         ((acl2::fquotep term) nil)
         (t (cons (acl2::ffn-symb term)
                  (fun-syms-in-term-lst (acl2::fargs term))))))

 (defun fun-syms-in-term-lst (l)
   (declare (xargs :guard (pseudo-term-listp l)
                   :verify-guards nil))
   (cond ((endp l) nil)
         (t (append (fun-syms-in-term (car l))
                    (fun-syms-in-term-lst (cdr l)))))))

(defun fun-sym-in-termp (f term)
  (declare (xargs :guard (and (legal-variablep f)
                              (pseudo-termp term))
                  :verify-guards nil))
  (and (member-equal f (fun-syms-in-term term)) t))
|#

