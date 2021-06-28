#|$ACL2s-Preamble$;
; Copyright (C) 2018, Northeastern University
; Written by Pete Manolios
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "kestrel/utilities/proof-builder-macros" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "data-structures/utilities" :dir :system)

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

(defun pkgp (pkg)
  (declare (xargs :guard t))
  (and (stringp pkg)
       (not (equal pkg ""))))

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

#|
; May be useful if I (local ...) causes problems

(defun gen-acl2s-local-fn (var val forms state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((old (get-acl2s-defaults var (w state)))
       (set? (not (equal old val)))
       (set (and set? `((with-output
                         :off :all
                         (acl2s-defaults :set ,var ,val)))))
       (reset (and set? `((with-output
                           :off :all
                           (acl2s-defaults :set ,var ,old)))))
       (forms (acl2::collect$ (lambda$ (x) `(with-output :stack :pop ,x))
                              forms)))
    `(encapsulate nil ,@set ,@forms ,@reset)))

(defmacro gen-acl2s-local (var val forms)
  `(with-output
    :off :all :stack :push
    (make-event (gen-acl2s-local-fn ',var ',val ',forms state))))
|#

(defun gen-acl2s-local-fn (var val forms)
  (declare (xargs :mode :program))
  (b* ((set `(with-output
              :off :all :on (error)
              (local (acl2s-defaults :set ,var ,val))))
       (forms (collect$ '(lambda (x) `(with-output :stack :pop ,x))
                        forms)))
    `(with-output
      :off :all :stack :push
      (encapsulate nil ,set ,@forms))))

(defmacro gen-acl2s-local (var val forms)
  (gen-acl2s-local-fn var val forms))

; :trans1 (gen-acl2s-local testing-enabled nil ((test? (= x y)) (thm t)))

;; If there are opportunities to do so, we should extend
;; test-then-skip-proofs so that it supports more forms.

(defmacro test-then-skip-proofs (thm)
  (declare (xargs :guard (true-listp thm)))
  (cond
   ((equal (car thm) 'defthm)
    `(gen-acl2s-local testing-enabled
                      t
                      ((test? ,(third thm))
                       (skip-proofs ,thm))))
   ((equal (car thm) 'thm)
    `(gen-acl2s-local testing-enabled
                      t
                      ((test? ,(second thm))
                       (skip-proofs ,thm))))
   ((member (car thm) '(defcong defequiv defrefinement))
    `(with-output
      :off :all :on (error) :stack :push
      (make-event
       (er-let* ((defthm
                   (acl2::macroexpand1* ',thm 'ctx (w state) state))
                 (form (acl2::trans-eval (cadadr defthm) 'ctx state t)))
                (value `(with-output
                         :stack :pop
                         (gen-acl2s-local
                          testing-enabled
                          t
                          ((test? ,(third (cdr form)))
                           (skip-proofs ,',thm)))))))))
    (t `(skip-proofs ,thm))))

; :trans1 (test-then-skip-proofs (defthm foo (equal (+ x y) (+ y x))))
; :trans1 (test-then-skip-proofs (thm  (equal (+ x y) (+ y x))))
; :trans1 (test-then-skip-proofs (defequiv =))


(defxdoc thm-no-test
  :parents (acl2s-utilities acl2::cgen)
  :short "A version of @('thm') with testing disabled."
  :long"<p>
A macro that locally turns off @('cgen') testing and then calls @('thm').
</p>
")


(defmacro thm-no-test (&rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((thm ,@args))))

; :trans1 (thm-no-test (equal (+ x y) (+ y x)))
; :trans1 (thm (equal (+ x y) (+ y x)))

(defxdoc defthm-no-test
  :parents (acl2s-utilities acl2::cgen)
  :short "A version of @('defthm') with testing disabled."
  :long"<p>
A macro that locally turns off @('cgen') testing and then calls @('defthm').
</p>
")

(defmacro defthm-no-test (name &rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((defthm ,name ,@args))))

; :trans1 (defthm-no-test foo (equal (+ x y) (+ y x)))
; :u (defthm foo (equal (+ x y) (+ y x))) :u

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
              *main-lisp-package-name*
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
  (implies (and (good-atom-listp l) (pkgp s))
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

(defun gen-keyword (symbol)
  (intern (symbol-name symbol) "KEYWORD"))

(defun fix-sym (sym)
  (declare (xargs :guard (symbolp sym)))
  (if (equal (symbol-package-name sym) *main-lisp-package-name*)
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

; (verify-termination fix-pkg) ; Matt K. mod: now comes in :logic mode
(verify-termination fix-sym)
(verify-termination pack-to-string)
(verify-termination gen-sym-sym)

; (verify-guards fix-pkg) ; Matt K. mod: now comes guard-verified
(verify-guards fix-sym)
(verify-guards pack-to-string)
(verify-guards gen-sym-sym)

(defun gen-sym-pkg (l pkg)
  (declare (xargs :guard (and (good-atom-listp l)
                              (or (null pkg) (pkgp pkg)))))
  (fix-intern$ (pack-to-string l) pkg))

#|
(defmacro gen-sym-pkg (l &optional pkg)
  (declare (xargs :guard t))
  `(gen-sym-pkg-fn ,l ,pkg))
|#

(defun make-symbl (l pkg)
  (declare (xargs :guard (and (good-atom-listp l)
                              (or (null pkg) (pkgp pkg)))))
  (fix-intern$ (pack-to-string l)
               (if pkg pkg (best-package-symbl-list l "ACL2"))))

(defun mk-acl2s-sym (l)
  (declare (xargs :guard (good-atom-listp l)))
  (make-symbl l "ACL2S"))

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
  `(gen-acl2s-local testing-enabled
                    t
                    ((test? ,@args)
                     (skip-proofs (defthm ,name ,@args)))))

; :trans1 (defthm-test-no-proof foo (equal (+ x y) (+ y x)))
; :u (defthm foo (equal (+ x y) (+ y x))) :u

(defmacro defthmskipall (name &rest args)
  `(skip-proofs (defthm-no-test ,name ,@args)))

; :trans1 (defthmskipall foo (equal (+ x y) (+ y x)))
; :u (defthm foo (equal (+ x y) (+ y x))) :u

(defmacro defun-no-test (name &rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((defun ,name ,@args))))

; :trans1 (defun-no-test f (x) (1+ x))
; :u  (defun f (x) (1+ x)) :u

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

(defun eqlable-2-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x))
         (eqlablep (caar x))
         (eqlable-alistp (cdar x))
         (eqlable-2-alistp (cdr x)))))

(defthm eqlable-2-alistp-eqlable-alistp
  (implies (eqlable-2-alistp a)
           (eqlable-alistp a)))

; Document this
(mutual-recursion
 (defun subst-var (new old form)
   (declare (xargs :guard (atom old)))
   (cond ((atom form)
          (cond ((equal form old) new)
                (t form)))
         ((acl2::fquotep form) form)
         (t (cons (car form)
                  (subst-var-lst new old (cdr form))))))

 (defun subst-var-lst (new old l)
   (declare (xargs :guard (atom old)))
   (cond ((atom l) nil)
         (t (cons (subst-var new old (car l))
                  (subst-var-lst new old (cdr l)))))))

; Used to have a guard for old, new in nest below of legal-variable,
; but now use symbol because * is not a legal variable and needed this
; in bare-bones mode.
(mutual-recursion
 (defun subst-fun-sym (new old form)
   (declare (xargs :guard (and (symbolp old)
                               (symbolp new))))
   (cond ((atom form)
          form)
         ((acl2::fquotep form) form)
         (t (cons (if (atom (car form))
                      (subst-var new old (car form))
                    (subst-fun-sym new old (car form)))
                  (subst-fun-lst new old (cdr form))))))

 (defun subst-fun-lst (new old l)
   (declare (xargs :guard (and (symbolp old)
                               (symbolp new))))
   (cond ((atom l) nil)
         (t (cons (subst-fun-sym new old (car l))
                  (subst-fun-lst new old (cdr l)))))))

(mutual-recursion
 (defun subst-expr1 (new old term)
   (declare (xargs :guard t :guard-debug t))
   (cond
    ((equal term old) new)
    ((atom term) term)
    ((quotep term) term)
    (t (cons (car term)
             (subst-expr1-lst new old (cdr term))))))

 (defun subst-expr1-lst (new old args)
   (declare (xargs :guard t))
   (if (atom args)
       nil
     (cons (subst-expr1 new old (car args))
           (subst-expr1-lst new old (cdr args))))))

(defun subst-expr (new old term)
  (declare (xargs :guard (not (quotep old))))
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

(defconst *contract-checking-values*
  '(:on :off))

; Modified from set-guard-checking
(defmacro set-contract-checking (flg)
  (declare (xargs :guard
                  (let ((flg (if (and (consp flg)
                                      (eq (car flg) 'quote)
                                      (consp (cdr flg)))
                                 (cadr flg)
                               flg)))
                    (member-eq flg *contract-checking-values*))))
  `(let* ((current-flg (f-get-global 'guard-checking-on state))
          (flg ,(if (and (consp flg) (eq (car flg) 'quote) (consp (cdr flg)))
                    (cadr flg)
                  flg))
          (gflg (if (eq flg :off) nil :all)))
     (cond
      ((and (raw-mode-p state) flg)
       (er soft 'set-contract-checking
           "It is illegal (and anyhow, would be useless) to attempt to modify ~
            contract checking while in raw mode, since contracts are not checked in ~
            raw mode."))
      ((eq gflg current-flg)
       (pprogn
        (fms "Contract-checking already has value ~x0.~%~%"
             (list (cons #\0 flg))
             *standard-co* state nil)
        (value :invisible)))
      ((eq flg :off)
       (pprogn (f-put-global 'guard-checking-on nil state)
               (fms "Turning contract-checking :OFF.~%~%"
                    nil *standard-co* state nil)
               (value :invisible)))
      (t (pprogn
          (f-put-global 'guard-checking-on gflg state)
          (assert$ (and gflg (not (eq gflg current-flg)))
                   (fms "Turning contract-checking :ON.~%~%"
                        nil *standard-co* state nil))
          (value :invisible))))))

; A recognizer for quoted objects. Notice that quotep and fquotep only
; recognize quoted object for pseudo-terms, even though they have a
; guard of t.

(defun rquotep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (eq (car x) 'quote)
       (null (cddr x))))

; A recognizer for quoted objects that are conses. Notice that quotep
; and fquotep only recognize quoted object for pseudo-terms, even
; though they have a guard of t.

(defun rfquotep (x)
  (declare (xargs :guard (consp x)))
  (and (consp (cdr x))
       (eq (car x) 'quote)
       (null (cdr (cdr x)))))

(defloop rquote-listp (xs)
  (declare (xargs :guard t))
  (for ((x in xs)) (always (rquotep x))))

(defloop unrquote-lst (xs)
  (declare (xargs :guard (rquote-listp xs)))
  (for ((x in xs))
       (collect (unquote x))))

; Added this since even on very simple examples defconst
; seems to go on forever.
(defmacro def-const (name form &optional doc)
  `(with-output
    :off :all :gag-mode nil :stack :push
    (make-event
     (let ((form ,form))
       `(with-output
         :stack :pop 
         (defconst ,',name ',form ,@(and ,doc '(,doc))))))))

; Utilities to stage rules.

(mutual-recursion
 (defun find-first-call (fn term)
 ; Find the first call of fn in term.
  (cond ((acl2::variablep term) nil)
        ((acl2::fquotep term) nil)
        ((equal (acl2::ffn-symb term) fn)
         term)
        (t (find-first-call-lst fn (acl2::fargs term)))))

 (defun find-first-call-lst (fn lst)
 ; Find the first call of fn in a list of terms.
  (cond ((endp lst) nil)
        (t (or (find-first-call fn (car lst))
               (find-first-call-lst fn (cdr lst)))))))

(defun stage1 (fn max clause flg)
; If the clause is stable under simplification and there is a call of
; fn in it, expand it.  But don't do it more than max times.
 (let ((temp (and flg
                  (find-first-call-lst fn clause))))
   (if temp
       (if (zp max)
           (cw "~%~%HINT PROBLEM:  The maximum repetition count of ~
                your STAGE hint been reached without eliminating ~
                all of the calls of ~x0.  You could supply a larger ~
                count with the optional second argument to STAGE ~
                (which defaults to 100).  But think about what is ~
                happening! Is each stage permanently eliminating a ~
                call of ~x0?~%~%"
               fn)
         `(:computed-hint-replacement
            ((stage1 ',fn ,(- max 1)
                     clause
                     stable-under-simplificationp))
           :expand (,temp)))
     nil)))

(defmacro stage (fn &optional (max '100))
 `(stage1 ',fn ,max clause stable-under-simplificationp))

; see custom.lisp where the stage hints have been added.

(defun pair-tl (x y)
  (if (or (endp x) (endp y))
      nil
    (cons (list (car x) (car y)) (pair-tl (cdr x) (cdr y)))))

(defun stage-rule1 (fn def-rule vars max clause flg)
; If the clause is stable under simplification and there is a call of
; fn in it, expand it.  But don't do it more than max times.
  (let ((temp (and flg
                   (find-first-call-lst fn clause))))
    (if temp
        (if (zp max)
            (cw "~%~%HINT PROBLEM:  The maximum repetition count of ~
                your STAGE hint been reached without eliminating ~
                all of the calls of ~x0.  You could supply a larger ~
                count with the optional second argument to STAGE ~
                (which defaults to 100).  But think about what is ~
                happening! Is each stage permanently eliminating a ~
                call of ~x0?~%~%"
                fn)
          `(:computed-hint-replacement
            ((stage-rule1 ',fn
                          ',def-rule
                          ',vars
                          ,(- max 1)
                          clause
                          stable-under-simplificationp))
            :expand (:with ,def-rule ,temp)))
      nil)))

(defmacro stage-rule (fn def-rule &optional (max '100) vars)
  `(stage-rule1 ',fn
                ',def-rule
                (or ,vars (formals ',fn (w state)))
                ,max
                clause
                stable-under-simplificationp))

#|
 Here is an example of how this is used

 (add-default-hints!
  '((stage-rule cfix cfix-definition-rule))
  :at-end t)

|#

; utility fn to print if verbose flag is true
(defmacro cw? (verbose-flag &rest rst)
  `(if ,verbose-flag
     (cw ,@rst)
     nil))

(defmacro ecw (&rest rst)
  `(prog2$ (cw ,@(butlast rst 1))
           (mv t ,(car (last rst)) state)))

(defmacro ecw? (verbose-flag &rest rst)
  `(if ,verbose-flag
       (ecw ,@rst)
     nil))

