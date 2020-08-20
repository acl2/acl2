; A linter for ACL2
;
; Copyright (C) 2018-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;; An ACL2 "lint" tool.  This applies some checks to all functions currently
;; defined in the world.  It currently checks for calls of CW with missing
;; arguments and calls of IF with resolvable tests.

;; NOTE: There is another lint tool in books/tools/lint.lisp.  It checks for
;; different things.

;; TODO: Check for a hyp of (syntaxp (quote x)), which is almost certainly an error.

;; TODO: Look for unchanged names of the form theorem-for-XXX from make-flag

;; TODO: Look for hyps and guard conjuncts that are known true or false by type-set.

;; TODO: Print terms (such as if-tests) as untranslated terms somehow

;; TODO: Add support for supressing various kinds of report.

(include-book "format-strings")
(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/utilities/my-get-event" :dir :system)
(include-book "kestrel/utilities/defun-events" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/substitution" :dir :system)
(include-book "std/strings/substrp" :dir :system)

;dup
(defun enquote-list (items)
  (declare (type t items))
  (if (atom items)
      nil
    (cons (enquote (car items))
          (enquote-list (cdr items)))))

(defun symbolic-length (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      (prog2$ (cw "Note: unable to get symbolic length of term ~x0.~%" term)
              0)
    (if (quotep term)
        (len (unquote term))
      (if (call-of 'cons term)
          (+ 1 (symbolic-length (farg2 term)))
        (prog2$ (cw "Note: unable to get symbolic length of term ~x0.~%" term)
                0)))))

;; Returns a list of elements
(defun symbolic-elements (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (quotep term) ; includes the case when term is 'nil
      (enquote-list (unquote term))
    (if (call-of 'cons term)
        (cons (farg1 term)
              (symbolic-elements (farg2 term)))
      (cw "Note: unable to get symbolic elements of term ~x0.~%" term))))

(defun symbolic-car (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (quotep term)
      (if (consp (unquote term))
          (enquote (car (unquote term)))
        (cw "Note: unable to get symbolic car of term ~x0.~%" term))
    (if (call-of 'cons term)
        (farg1 term)
      (cw "Note: unable to get symbolic car of term ~x0.~%" term))))

(defun symbolic-cdr (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (quotep term)
      (if (consp (unquote term))
          (enquote (cdr (unquote term)))
        (cw "Note: unable to get symbolic cdr of term ~x0.~%" term))
    (if (call-of 'cons term)
        (farg2 term)
      (cw "Note: unable to get symbolic cdr of term ~x0.~%" term))))

;; Returns a list
(defun symbolic-strip-cars (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      (cw "Note: unable to get symbolic strip-cars of term ~x0.~%" term)
    (if (quotep term) ; includes the case when term is 'nil
        (if (alistp (unquote term))
            (enquote-list (strip-cars (unquote term)))
          (cw "Note: unable to get symbolic strip-cars of term ~x0.~%" term))
      (let ((fn (ffn-symb term)))
        (if (eq 'cons fn)
            (let ((pair (farg1 term)))
              (cons (symbolic-car pair)
                    (symbolic-strip-cars (farg2 term))))
          (if (eq 'acons fn)
              (cons (farg1 term)
                    (symbolic-strip-cars (farg3 term)))
            (if (eq 'pairlis$ fn)
                (symbolic-elements (farg1 term))
              (if (eq 'pairlis2 fn)
                  (take (symbolic-length (farg2 term))
                        (symbolic-elements (farg1 term)))
                (cw "Note: unable to get symbolic strip-cars of term ~x0.~%" term)))))))))

;;test: (SYMBOLIC-STRIP-CARS '(CONS (CONS '#\0 'BLAH) 'NIL))

(defun symbolic-strip-cdrs (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      (cw "Note: unable to get symbolic strip-cdrs of term ~x0.~%" term)
    (if (quotep term) ; includes the case when term is 'nil
        (if (alistp (unquote term))
            (enquote-list (strip-cdrs (unquote term)))
          (cw "Note: unable to get symbolic strip-cdrs of term ~x0.~%" term))
      (let ((fn (ffn-symb term)))
        (if (eq 'cons fn)
            (let ((pair (farg1 term)))
              (cons (symbolic-cdr pair)
                    (symbolic-strip-cdrs (farg2 term))))
          (if (eq 'acons fn)
              (cons (farg2 term)
                    (symbolic-strip-cdrs (farg3 term)))
            (if (eq 'pairlis$ fn)
                (take (symbolic-length (farg1 term))
                      (symbolic-elements (farg2 term)))
              (if (eq 'pairlis2 fn)
                  (symbolic-elements (farg2 term))
                (cw "Note: unable to get symbolic strip-cdrs of term ~x0.~%" term)))))))))

(defun char-to-nat (char)
  (declare (xargs :guard (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
  (case char
    (#\0 0)
    (#\1 1)
    (#\2 2)
    (#\3 3)
    (#\4 4)
    (#\5 5)
    (#\6 6)
    (#\7 7)
    (#\8 8)
    (#\9 9)))

(defun max-val-of-chars (chars)
  (if (endp chars)
      -1
    (max (char-to-nat (first chars))
         (max-val-of-chars (rest chars)))))

(defun my-prefixp (chars1 chars2)
  (and (<= (len chars1) (len chars2))
       (equal chars1 (take (len chars1) chars2))))

(defun check-first-arg-as-ctx (form fn-being-checked)
  (let ((ctx (farg1 form)))
    (and (quotep ctx)
         (symbolp (unquote ctx))
         (not (eq (unquote ctx) fn-being-checked))
         ;; Suppress warning if ctx is a prefix of the function (e.g., ctx of foo inside foo-fn):
         (let ((ctx-chars (coerce (symbol-name (unquote ctx)) 'list))
               (fn-being-checked-chars (coerce (symbol-name fn-being-checked) 'list)))
           (not (my-prefixp ctx-chars fn-being-checked-chars)))
         ;; Suppress warning for context from assert, STATE-GLOBAL-LET*, etc:
         (not (member-eq (unquote ctx) '(ASSERT$ STATE-GLOBAL-LET*)))
         (cw "(Context ~x0 used in ~x1 for ~x2.)~%~%" ctx fn-being-checked (ffn-symb form)))))

(defun check-keys-of-alist-wrt-format-string (string alist fn-being-checked ctx call)
  (let* ((args-mentioned (args-in-format-string string)) ;these are chars
         (alist-keys (symbolic-strip-cars alist))
         (quoted-args-mentioned (enquote-list args-mentioned)))
    (prog2$ (if (not (subsetp-equal quoted-args-mentioned alist-keys))
                (cw "(Questionable call of ~x0 detected in ~x1: ~x2. Missing args? Mentioned args are ~x3 but alist keys are ~x4)~%~%" ctx fn-being-checked call quoted-args-mentioned alist-keys)
              nil)
            (if (not (subsetp-equal alist-keys quoted-args-mentioned))
                (cw "(Questionable call of ~x0 detected in ~x1: ~x2. Extra args? Mentioned args are ~x3 but alist keys are ~x4)~%~%" ctx fn-being-checked call quoted-args-mentioned alist-keys)
              nil))))

(defun check-vals-of-alist-wrt-format-string (string alist fn-being-checked ctx call)
  (let* ((args-mentioned (args-in-format-string string)) ;these are chars
         (max-arg-mentioned (max-val-of-chars args-mentioned))
         (alist-vals (symbolic-strip-cdrs alist))
         (len-vals (len alist-vals)))
    (if (<= len-vals max-arg-mentioned)
        (cw "(Questionable call of ~x0 detected in ~x1: ~x2.  Not enough args given?)~%~%" ctx fn-being-checked call)
      nil)))

(defun check-call-of-fmt-function (call fn-being-checked)
  (let ((string (farg1 call)))
    (and (quotep string)
         (let ((string (unquote string))
               (alist (farg2 call)))
           ;; we check the vals of the alist since the keys are always the digits 0 through 9:
           (check-vals-of-alist-wrt-format-string string alist fn-being-checked 'fmt-to-comment-window/cw call)))))

(defun check-call-of-hard-error (call fn-being-checked)
  (prog2$ (check-first-arg-as-ctx call fn-being-checked)
          (let ((string (farg2 call)))
            (and (quotep string)
                 (let ((string (unquote string))
                       (alist (farg3 call)))
                   (check-keys-of-alist-wrt-format-string string alist fn-being-checked 'hard-error call))))))

(defun check-call-of-illegal (call fn-being-checked)
  (prog2$ (check-first-arg-as-ctx call fn-being-checked)
          (let ((string (farg2 call)))
            (and (quotep string)
                 (let ((string (unquote string))
                       (alist (farg3 call)))
                   (check-keys-of-alist-wrt-format-string string alist fn-being-checked 'illegal call))))))

(defun filter-subst (subst vars)
  (if (endp subst)
      nil
    (let ((pair (first subst)))
      (if (member-eq (car pair) vars)
          (cons pair (filter-subst (rest subst) vars))
        (filter-subst (rest subst) vars)))))

;; Check for (if x y z) where X is known non-nil or known-nil by type-set.
(defun check-call-of-if (term subst fn-being-checked state)
   (declare (xargs :guard (pseudo-termp term)
                   :mode :program
                   :stobjs state))
   (let* ((orig-test (farg1 term))
          (test (my-sublis-var subst orig-test))
          )
     (mv-let (type-set ttree)
       (type-set test nil nil nil (ens state) (w state) nil nil nil)
       (declare (ignore ttree))
       (let* ((decoded-ts (decode-type-set type-set))
              (test-knownp (or (= *ts-nil* type-set) ;check for nil
                               (= 0 (logand *ts-nil* type-set)) ;check for non-nil
                               ))
              (reportp (and test-knownp
                            ;; Suppress calls of integerp that
                            ;; are know to be true since these
                            ;; often arise from things like
                            ;; (the unsigned-byte x):
                            ;; (not (and (eql type-set *TS-T*)
                            ;;           (call-of 'integerp test)))
                            )))
         (progn$ ;; (progn$ (cw "(In ~x0:~%" fn-being-checked)
                 ;;         (cw "  Test: ~x0~%" test)
                 ;;         (cw "  Type: ~x0)~%" decoded-ts))
          (if reportp
              (let* ((test-vars (all-vars orig-test))
                     (relevant-subst (filter-subst subst test-vars)))
                (progn$ (cw "(Resolvable IF-test in ~x0:~%" fn-being-checked)
                        (cw "  Test: ~x0~%" orig-test)
                        (cw "  Type: ~x0~%" decoded-ts)
                        (cw "  Term: ~x0~%" term)
                        (cw "  Relevant subst: ~x0)~%~%" relevant-subst)))
            nil))))))

;; TODO: Also use guard information and info from overarching IFs
(defun check-call-of-equal (term subst fn-being-checked state)
  (declare (xargs :guard (pseudo-termp term)
                  :mode :program
                  :stobjs state)
           (ignore subst) ;todo: use?
           )
  (b* ((arg1 (farg1 term))
       (arg2 (farg2 term))
       ((mv type-set1 &)
        (type-set arg1 nil nil nil (ens state) (w state) nil nil nil))
       ((mv type-set2 &)
        (type-set arg2 nil nil nil (ens state) (w state) nil nil nil))
       ;;(decoded-ts1 (decode-type-set type-set1))
       ;;(decoded-ts2 (decode-type-set type-set2))
       (arg1-symbolp (ts-subsetp type-set1 *ts-symbol*))
       (arg2-symbolp (ts-subsetp type-set2 *ts-symbol*))
       (arg1-numberp (ts-subsetp type-set1 *ts-acl2-number*))
       (arg2-numberp (ts-subsetp type-set2 *ts-acl2-number*))
       (arg1-eqlablep (or arg1-symbolp
                          arg1-numberp
                          (ts-subsetp type-set1 *ts-character*)))
       (arg2-eqlablep (or arg2-symbolp
                          arg2-numberp
                          (ts-subsetp type-set2 *ts-character*))))
    (progn$ (if arg1-symbolp
                (if arg2-symbolp
                    (cw "(In ~x0, equal test ~x1 could be EQ since both args, ~x2 and ~x3, are known to be symbols.)~%~%"
                        fn-being-checked term arg1 arg2)
                  (cw "(In ~x0, equal test ~x1 could be EQ since arg 1, ~x2, is known to be a symbol.)~%~%"
                      fn-being-checked term arg1))
              (if arg2-symbolp
                  (cw "(In ~x0, equal test ~x1 could be EQ since arg 2, ~x2, is known to be a symbol.)~%~%"
                      fn-being-checked term arg2)
                nil))
            (and arg1-numberp
                 arg2-numberp
                 (cw "(In ~x0, equal test ~x1 could be = since both args, ~x2 and ~x3, are known to be numbers.)~%~%"
                     fn-being-checked term arg1 arg2))
            (and (not arg1-symbolp)
                 (not arg2-symbolp)
                 (not (and arg1-numberp
                           arg2-numberp))
                 (if arg1-eqlablep
                     (if arg2-eqlablep
                         (cw "(In ~x0, equal test ~x1 could be EQL since both args, ~x2 and ~x3, are known to be numbers, symbols, or characters.)~%~%"
                             fn-being-checked term arg1 arg2)
                       (cw "(In ~x0, equal test ~x1 could be EQL since arg 1, ~x2, is known to be a number, symbol, or character.)~%~%"
                           fn-being-checked term arg1))
                   (if arg2-eqlablep
                       (cw "(In ~x0, equal test ~x1 could be EQL since arg 2, ~x2, is known to be a number, symbol, or character.)~%~%"
                           fn-being-checked term arg2)
                     nil))))))

;; The subst used when lambdas are encountered
;; TODO: Track and use the context from overarching IF tests.
(mutual-recursion
 (defun check-term (term subst fn-being-checked state)
   (declare (xargs :guard (pseudo-termp term)
                   :mode :program
                   :stobjs state))
   (if (variablep term)
       nil
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           nil
         (if (member-eq fn '(the-check ;suppress checks done for (the ...)
                             check-dcl-guardian ;used in b*?
                             ))
             nil
           (prog2$ (check-terms (fargs term) subst fn-being-checked state)
                   ;; TODO: Use the subst for these?
                   (if (member-eq fn '(fmt fms fmt1 fmt-to-comment-window))
                       (check-call-of-fmt-function term fn-being-checked)
                     (if (eq fn 'equal)
                         (check-call-of-equal term subst fn-being-checked state)
                       (if (eq fn 'hard-error)
                           (check-call-of-hard-error term fn-being-checked)
                         (if (eq fn 'illegal)
                             (check-call-of-illegal term fn-being-checked)
                           (if (eq 'if fn)
                               (check-call-of-if term subst fn-being-checked state)
                             (if (consp fn) ;check for lambda
                                 (check-term (lambda-body fn)
                                             ;; new subst, since we are in a lambda body
                                             (pairlis$ (lambda-formals fn)
                                                       (my-sublis-var-lst subst (fargs term)))
                                             fn-being-checked state)
                               (and (quote-listp (fargs term))
                                    (cw "(Ground term ~x0 in ~x1.)~%~%" term fn-being-checked))))))))))))))

 (defun check-terms (terms subst fn-being-checked state)
   (declare (xargs :guard (and (true-listp terms)
                               (pseudo-term-listp terms))
                   :stobjs state))
   (if (endp terms)
       nil
     (prog2$ (check-term (car terms) subst fn-being-checked state)
             (check-terms (cdr terms) subst fn-being-checked state)))))

(defun check-defun (fn state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let* ((body (fn-body fn t (w state)))
         (formals (fn-formals fn (w state)))
         (event (my-get-event fn (w state)))
         (declares (and (defun-or-mutual-recursion-formp event)
                        (get-declares-from-event fn event)))
         (xargs (get-xargs-from-declares declares))
         (guard-debug-res (assoc-keyword :guard-debug xargs)))
    (progn$ (and guard-debug-res
                 (cw "(~x0 has a :guard-debug xarg, ~x1.)~%~%" fn (second guard-debug-res)))
            (check-term body (pairlis$ formals formals) fn state))))

(defun check-defuns (fns state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (atom fns)
      nil
    (let* ((fn (first fns)))
      (prog2$ (check-defun fn state)
              (check-defuns (rest fns) state)))))

(defun all-defuns-in-world (wrld acc)
  (declare (xargs; :stobjs state
                  :mode :program))
  (if (atom wrld)
      (reverse acc)
    (let* ((entry (first wrld))
           (symb (car entry))
           (prop (cadr entry)))
      (if (eq prop 'unnormalized-body)
          (all-defuns-in-world (rest wrld) (cons symb acc))
        (all-defuns-in-world (rest wrld) acc)))))

(defun check-all-defuns-fn (state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let* ((wrld (w state))
         (all-defuns (all-defuns-in-world wrld nil)))
    (prog2$ (cw "Applying linter:~%~%")
            (check-defuns all-defuns state))))

;; Call this macro to check every defun in the current ACL2 world.
(defmacro check-all-defuns ()
  '(check-all-defuns-fn state))
