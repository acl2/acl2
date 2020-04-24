; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; To do:

; - Document verify-guards-program with xdoc.

; - Control the output, perhaps simply by turning it off unless a :verbose
;   option is supplied.  Notice for example the error message currently
;   produced for f5p in the example (verify-guards-program f6p) below.

; - For each system utility used below, either document it in :doc
;   system-utilities or replace it below with a corresponding documented system
;   utility.  For example, we could use function-namep in
;   verify-guards-program-forms.

; - Perhaps store functions in a table when they are "guard-verified" in this
;   sense, and insist that all supporters (ancestors) are in that table before
;   applying verify-guards-program to a given function symbol.  The table could
;   probably be easily extended by having the top-level make-event generate a
;   table event.

; - Consider causing an error if the argument to verify-guards-program is
;   already a guard-verified function symbol, and maybe even if it's already in
;   :logic mode (since then perhaps verify-guards would be more appropriate).

; - Consider a mechanism for providing termination hints.

; - Consider adding an option that proves both termination and guards for the
;   given function, rather than skipping the termination proof.

; - Consider including the book std/testing/eval.lisp and use must-fail and
;   perhaps must-succeed to incorporate the tests at the end, below.  Perhaps
;   the successes could simply be local encapsulates.  Maybe create
;   verify-guards-program-tests.lisp for this.  Maybe add bigger tests.

; - Here we document a potential problem, which may not occur (it apparently
;   hasn't yet).  Suppose that a :program mode function is defined using some
;   raw Lisp code.  We can promote that function to :logic mode, in spite of
;   ACL2's usual prohibition against that, because of our use of trust tags.
;   But if that :logic-mode function is not guard-verified, or if it has a
;   non-trivial guard, we might wind up avoiding the raw Lisp code, which for
;   system functions might cause problems.  Consider for example:

;     (defun foo (x) (declare (xargs :mode :program)) x)
;     :q
;     (defun foo (x) (cw "Hello!~%") x)
;     (lp)
;     (foo 3) ; prints "Hello!"
;     (verify-termination foo)
;     (foo 3) ; does NOT print "Hello!"
;     (verify-guards foo)
;     (foo 3) ; prints "Hello!"

;   If foo is a system function whose raw Lisp code is critical for the
;   verify-guards call above, we could be in trouble.

; - Deal with the comment in verify-termination-forms-with-measures.  Better
;   yet: avoid the :OR by checking for measures and then always laying down the
;   :? "call" when there's no measure.

; - Consider an option for whether or not to skip-proofs on the
;   verify-termination for the top-level function.

; - Have an option that just returns the forms, rather than passing them to LD.

; - Perhaps remove excess skip-proofs.

; - Note that because a defttag is executed under the make-event, a command
;   tuple is laid down when using verify-guards-program if no previous defttag
;   has been executed.  Often that defttag won't be needed, so consider adding
;   a keyword argument to control whether or not the defttag is done.  Or
;   perhaps even compute whether it's needed, say by seeing whether system
;   functions are involved.

; - Add an option that saves all of the generated verify-termination and
;   verify-guards events (all with skip-proofs) before the final verify-guards
;   (which does not have skip-proofs), so that the user can work towards
;   admitting that final event without having to redo all those skip-proofs
;   events each time.

(program)

(defun all-ffn-symbs-lst+translate (forms fns ctx wrld state-vars acc)

; We are translating only to get the function symbols, so we don't concern
; ourselves about translating for execution.

  (cond
   ((endp forms) acc)
   (t (all-ffn-symbs-lst+translate
       (cdr forms)
       (cdr fns)
       ctx wrld state-vars
       (mv-let (erp tbody)
         (translate-cmp (car forms)
                        t   ; stobjs-out
                        nil ; logic-modep
                        t   ; known-stobjs
                        ctx wrld state-vars)
         (cond
          (erp (er hard ctx
                   "Translate failed for body of ~x0 with the following ~
                    message:~|~@1"
                   (car fns)
                   tbody))
          (t (all-ffn-symbs tbody
                            (all-ffn-symbs (guard (car fns) nil wrld)
                                           acc)))))))))

(defun all-ffn-symbs-mut-rec-logic (names wrld acc)
  (cond ((endp names) acc)
        (t (all-ffn-symbs-mut-rec-logic
            (cdr names)
            wrld
            (all-ffn-symbs (body (car names) nil wrld)
                           (all-ffn-symbs (guard (car names) nil wrld)
                                          acc))))))

(defun immediate-supps (fn old-fns wrld ctx state-vars)
  (let ((defun-mode (getpropc fn 'symbol-class nil wrld)))
    (case defun-mode
      (:common-lisp-compliant (mv nil nil))
      (:ideal
       (let ((recp (getpropc fn 'recursivep nil wrld)))
         (cond ((cdr recp)
                (mv recp (all-ffn-symbs-mut-rec-logic recp wrld old-fns)))
               (t
                (mv nil (all-ffn-symbs (body fn nil wrld)
                                       (all-ffn-symbs (guard fn nil wrld)
                                                      old-fns)))))))
      (t ; :program mode
       (let* ((defs (recover-defs-lst fn wrld))
              (sibs (strip-cars defs)))
         (mv sibs
             (all-ffn-symbs-lst+translate (strip-last-elements defs)
                                          sibs
                                          ctx wrld state-vars old-fns)))))))

(defun hons-acons-nil-lst (lst alist)
  (cond ((endp lst) alist)
        (t (hons-acons-nil-lst (cdr lst)
                               (hons-acons (car lst) nil alist)))))

(defun non-compliant-supporters-rec (fns wrld ctx state-vars supps)

; At the top level, where supps is an atom, we extend supps by associating each
; supporter of a function fn in fns with one of the following.

; t    - normal case, where fn is not defined recursively
; sibs - a list of all mutual-recursion siblings of fn, including fn (in
;        the singly-recursive case, including only fn)
; nil  - fn is defined in a mutual-recursion with some g already associated
;        with a non-nil value in supps

; As we recur, we skip any member of fns that is already a key of supps.

  (cond
   ((endp fns) supps)
   ((or (eq (getpropc (car fns) 'symbol-class nil wrld)
            :common-lisp-compliant)
        (hons-get (car fns) supps))
    (non-compliant-supporters-rec (cdr fns) wrld ctx state-vars supps))
   (t (mv-let (sibs extended-fns)
        (immediate-supps (car fns) (cdr fns) wrld ctx state-vars)
        (non-compliant-supporters-rec
         extended-fns wrld ctx state-vars
         (hons-acons (car fns)
                     (or sibs t)
                     (hons-acons-nil-lst sibs supps)))))))

(defun non-compliant-supporters-fixer (alist acc)

; For each (fn . val) in the alist computed by non-compliant-supporters-rec,
; val is one of three forms documented there: a list sibs in the recursive
; case, t in the non-recursive case, and nil for entries to be skipped.  Here
; we drop the nil entries (and reverse the order, but that's irrelevant).  We
; also drop the final cdr.

  (cond ((atom alist) acc)
        (t (non-compliant-supporters-fixer
            (cdr alist)
            (if (null (cdar alist))
                acc
              (cons (car alist) acc))))))

(defun non-compliant-supporters (fn wrld ctx state-vars)

; We return an alist associating each function symbol ancestral in fn that is
; not :common-lisp-compliant with nil if the symbol is not mutually recursive,
; else with the list of all its mutual-recursion siblings.

  (with-fast-alist 'supps
    (non-compliant-supporters-fixer
     (non-compliant-supporters-rec (list fn) wrld ctx state-vars 'supps)
     nil)))

(mutual-recursion

(defun non-compliant-supporters-depth (fn wrld ctx state-vars)
  (mv-let (sibs extended-fns)
    (immediate-supps fn nil wrld ctx state-vars)
    (1+ (non-compliant-supporters-depth-lst
         (set-difference-eq extended-fns (or sibs (list fn)))
         wrld ctx state-vars))))

(defun non-compliant-supporters-depth-lst (fns wrld ctx state-vars)
  (cond ((endp fns) 0)
        (t (max (non-compliant-supporters-depth (car fns) wrld ctx state-vars)
                (non-compliant-supporters-depth-lst (cdr fns) wrld ctx
                                                    state-vars)))))
)

(memoize 'non-compliant-supporters-depth)

(defun order-alist-by-non-compliant-supporters-depth (alist wrld ctx state-vars
                                                            acc)

; They keys of the given alist are all function symbols of wrld.  We return a
; new alist with the same entries, but ordered by the depth of the key, so that
; the first entry is for the first function symbol introduced and the last
; entry is for the last function symbol introduced.  We avoid using the
; 'absolute-event-number because that changes with verify-termination.

  (cond ((endp alist)
         (prog2$
          (clear-memoize-table 'non-compliant-supporters-depth)
          (strip-cdrs (merge-sort-car-< acc))))
        (t (order-alist-by-non-compliant-supporters-depth
            (cdr alist)
            wrld ctx state-vars
            (acons (non-compliant-supporters-depth (caar alist)
                                                   wrld ctx state-vars)
                   (car alist)
                   acc)))))

(defun verify-termination-forms-with-measures (fns wrld)
  (cond ((endp fns) nil)
        (t (cons

; If there is already a measure declared for (car fns), it will be an error to
; lay down a measure here.  However, if there is a measure declared for (car
; fns) then it seems unlikely we would need to call
; verify-termination-forms-mut-rec, since presumably the other siblings have
; measures too and thus verify-termination-form would succeed without needing
; to do this computation.  Still, an error is possible.

            `(,(car fns)
              (declare (xargs :measure
                              (:? ,@(formals (car fns) wrld))
                              :verify-guards nil)))
            (verify-termination-forms-with-measures (cdr fns) wrld)))))

(defun verify-termination-form (f sibs wrld)
  (cond ((consp sibs) ; recursive

; Initially, the test above was (getpropc f 'recursivep nil wrld).  But that's
; only a suitable test if f is in :logic mode.  The point here is that for
; recursive functions, ACL2 might not be able to guess a measure when no
; measure is supplied, so the first verify-termination form below might fail;
; see f5p below for an example.  Our solution to that problem is simply to try
; again in that case, supplying an explicit measure arbitrarily based on the
; first formal.  (If the formals are nil this might or might not work, but the
; formals are very unlikely to be nil for a recursively defined function.)

         `(make-event
           '(:or (skip-proofs
                  (verify-termination ,f
                    (declare (xargs :verify-guards nil))))
                 (skip-proofs
                  (verify-termination
                    ,@(verify-termination-forms-with-measures sibs wrld))))))
        (t `(skip-proofs (verify-termination ,f
                           (declare (xargs :verify-guards nil)))))))

(defun verify-term-guards-form (g sibs hints otf-flg wrld)
  (cond ((eq (getpropc g 'symbol-class nil wrld)
             :program)
         `(progn
            ,(verify-termination-form g sibs wrld)
            (verify-guards ,g
                           ,@(and hints `(:hints ,hints))
                           ,@(and otf-flg `(:otf-flg ,otf-flg)))))
        (t ; typically (eq class :ideal)
         `(verify-guards ,g
                         ,@(and hints `(:hints ,hints))
                         ,@(and otf-flg `(:otf-flg ,otf-flg))))))

(defun verify-guards-program-forms-1 (fn-alist fn hints otf-flg wrld acc)

; Fn-alist is an alist with entries (fn . val), where fn is a function symbol
; of wrld and val is t if fn is non-recursive, else val is a list of the
; mutual-recursion siblings of fn (hence, just (fn) if fn is singly recursive).
; Moreover, fn-alist is sorted by depth: the key that is the oldest function
; symbol comes first, and newest, last.  We avoid using the
; 'absolute-event-number because that changes with verify-termination.

  (cond ((atom fn-alist)
         (reverse acc)) ; restore the order
        (t (verify-guards-program-forms-1
            (cdr fn-alist)
            fn
            hints
            otf-flg
            wrld
            (let ((entry (car fn-alist)))
              (cons (let* ((val (cdr entry))
                           ;; Test whether this is the entry for the
                           ;; function on which verify-guards-program
                           ;; was invoked (if so, attempt the guard
                           ;; proof [with hints], if not skip the guard
                           ;; proof):
                           (main-fnp (and (not (eq t val))
                                          (member-eq fn val)))
                           (form (verify-term-guards-form (car entry)
                                                          (cdr entry)
                                                          (and main-fnp hints)
                                                          (and main-fnp otf-flg)
                                                          wrld)))
                      (if main-fnp
                          form
                        `(skip-proofs ,form)))
                    acc))))))

(defun verify-guards-program-forms (fn hints otf-flg wrld)
  (cond ((not (and (symbolp fn)
                   (function-symbolp fn wrld)))
         `((value-triple (er hard 'verify-guards-program
                             "Not a function symbol: ~x0"
                             ',fn))))
        (t (let* ((ctx 'verify-guards-program)
                  (state-vars (default-state-vars nil
                                :temp-touchable-vars t
                                :temp-touchable-fns t))
                  (alist (order-alist-by-non-compliant-supporters-depth
                          (non-compliant-supporters fn wrld ctx state-vars)
                          wrld ctx state-vars nil)))
             (verify-guards-program-forms-1 alist fn hints otf-flg wrld nil)))))

(defmacro verify-guards-program (fn &key
                                    (print ':use-default print-p)
                                    (hints 'nil)
                                    (otf-flg 'nil))
  `(make-event (mv-let (erp val state)
                 (ld (list* '(logic)
                            '(set-state-ok t)
                            '(set-irrelevant-formals-ok t)
                            '(set-ignore-ok t)
                            '(defttag :verify-guards-program)
                            '(set-temp-touchable-vars t state)
                            '(set-temp-touchable-fns t state)
                            '(assign verify-termination-on-raw-program-okp t)
                            (verify-guards-program-forms ',fn ',hints ',otf-flg (w state)))
                     :ld-error-action :error
                     ,@(and print-p `(:ld-pre-eval-print ,print)))
                 (declare (ignore val))
                 (mv erp (list 'value-triple (if erp :FAILED :SUCCESS)) state))))
