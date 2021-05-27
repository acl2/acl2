; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

;;These macros facilitate localization of events:

(defmacro local-defun (&rest body)
  (list 'local (cons 'defun body)))

(defmacro local-defund (&rest body)
  (list 'local (cons 'defund body)))

(defmacro local-defthm (&rest body)
  (list 'local (cons 'defthm body)))

(defmacro local-defthmd (&rest body)
  (list 'local (cons 'defthmd body)))

(defmacro local-in-theory (&rest body)
  (cons 'local
	(cons (cons 'in-theory (append body 'nil))
	      'nil)))

(defmacro defbvecp (name formals width &key thm-name hyp hints)
  (let* ((thm-name
          (or thm-name
              (intern-in-package-of-symbol
               (concatenate 'string
                            (if (consp width)
                                "BV-ARRP$"
                              "BVECP$")
                            (symbol-name name))
               name)))
         (x (cons name formals))
         (typed-term (if (consp width)
                         (list 'ag 'index x)
                       x))
         (bvecp-concl (if (consp width)
                          (list 'bv-arrp x (car (last width)))
                        (list 'bvecp x width)))
         (concl (list 'and
                      (list 'integerp typed-term)
                      (list '<= 0 typed-term))))
    (list* 'defthm thm-name
           (if hyp
               (list 'implies hyp bvecp-concl)
             bvecp-concl)
           :rule-classes
           (list
            :rewrite
            (list :forward-chaining :trigger-terms (list x))
            (list :type-prescription
                  :corollary
                  (if hyp
                      (list 'implies hyp concl)
                    concl)
                  :typed-term typed-term
                  ;; hints for the corollary
                  :hints
                  (if (consp width)
                      '(("Goal"
                         :in-theory
                         '(implies bvecp
                                   bv-arrp-implies-nonnegative-integerp)))
                    '(("Goal"
                       :in-theory
                       '(implies bvecp))))))
           (if hints (list :hints hints) nil))))

(defun sub1-induction (n)
      (if (zp n)
          n
        (sub1-induction (1- n))))

; These will be the functions to disable in acl2 proofs about signal bodies.
; We use this in the compiler.

(defconst *rtl-operators-after-macro-expansion*
  '(log= log<>
    log< log<= log> log>=
    comp2< comp2<= comp2> comp2>=
    land lior lxor lnot
    logand1 logior1 logxor1
    shft
    cat mulcat
    bits bitn setbits setbitn
    ag as
    * + ; from macroexpansion of mod* or mod+
    ;mod- ;now a macro!
    floor rem decode encode
    ;; bind ; handled specially in fixup-term
    ;; if1 ;  a macro, so we don't disable it
    ;; quote, n!, arr0 ; handled specially in fixup-term
    natp1 ; doesn't matter, only occurs in for-loop defuns (must be enabled in those proofs anyway)
    mk-bvarr mk-bvec
    ))

; Macro fast-and puts conjunctions in a tree form, which can avoid stack
; overflows by ACL2's translate functions.

(defun split-list (lst lo hi)
  (cond ((endp lst)
         (mv lo hi))
        ((endp (cdr lst))
         (mv (cons (car lst) lo) hi))
        (t
         (split-list (cddr lst)
                     (cons (car lst) lo)
                     (cons (cadr lst) hi)))))

(defun fast-and-fn (conjuncts)
  (declare (xargs :mode :program))
  (cond ((endp conjuncts) ''t)
        ((endp (cdr conjuncts)) (car conjuncts))
        (t
         (mv-let (hi lo)
             (split-list conjuncts () ())
           (list 'if
                 (fast-and-fn hi)
                 (fast-and-fn lo)
                 'nil)))))

(defmacro fast-and (&rest conjuncts)
  (fast-and-fn conjuncts))

(defmacro defsig (name param body)
  (declare (ignore param))
  (let ((realname  (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name name)
                                 "$")
                    name)))
    `(progn (defund ,realname (n $path)
              ,body)
            (defmacro ,name (n)
              (list ',realname n '$path))
            (add-macro-alias ,name ,realname))))

(defmacro defsigd (name params body)
  (let ((realname (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "$")
                    name)))
    `(progn (defund ,realname (,@params $path)
              ,body)
            (defmacro ,name ,params
              (list ',realname ,@params '$path))
            (add-macro-alias ,name ,realname))))

(defmacro defthm-nl (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  `(encapsulate
     ()

     (local (set-default-hints
             '((nonlinearp-default-hint stable-under-simplificationp
                                        hist pspv))))

     (defthm ,@thm)))

(defmacro defthmd-nl (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  `(encapsulate
     ()

     (local (set-default-hints
             '((nonlinearp-default-hint stable-under-simplificationp
                                        hist pspv))))

     (defthmd ,@thm)))

(defmacro defthm-nl++ (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  `(encapsulate
     ()

     (local
      (set-default-hints
       '((nonlinearp-default-hint++ id
                                    stable-under-simplificationp
                                    hist
                                    nil))))

     (defthm ,@thm)))

(defmacro defthmd-nl++ (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  `(encapsulate
     ()

     (local
      (set-default-hints
       '((nonlinearp-default-hint++ id
                                    stable-under-simplificationp
                                    hist
                                    nil))))

     (defthmd ,@thm)))
