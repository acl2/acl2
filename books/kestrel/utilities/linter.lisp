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

;; Usage: Include the linter first, then the books to be checked.  Then call
;; (run-linter).  Use option :check :all to check the linter itself, any books
;; included before the linter, and the ACL2 system.  Otherwise, such things are
;; not checked.

;; The linter detects:
;;
;; - Uses of format strings where too few or too many values are given.  The
;; former is almost certainly an error.  The latter may indicate an error.
;;
;; - Uses of context arguments (quoted symbols) passed to things like
;; hard-error that may be wrong (e.g., copied and pasted from another function).
;;
;; - Explicit :guard-debug xargs, presumably left behind after debugging.
;; Leaving :guard-debug t can probably slow down guard proofs.
;;
;; - Equality tests (calls EQ, EQL, or =) that seem to be ill-guarded (e.g.,
;; calling EQ on things that are known to be non-symbols).
;;
;; - Equality tests (calls of EQUAL or EQL) that could be optimized to faster,
;; more specific, tests.
;;
;; - Ground terms in functions that could perhaps be computed ahead of time.
;;
;; - Calls of IF where the test is provably always nil or always non-nil.
;;
;; - Calls of IF where both branches are the same.
;;
;; - Theorems whose hyps contradict or where a hyp is implied by the others.

;; NOTE: There is another lint tool in books/tools/lint.lisp.  It checks for
;; different things.

;; TODO: Check for a hyp of , which is almost certainly an error.

;; TODO: Look for theorem names of the form theorem-for-XXX from make-flag

;; TODO: Look for hyps and guard conjuncts that are known true or false by type-set.

;; TODO: Print terms (such as if-tests) as untranslated terms somehow?

;; TODO: Detect a LET above an IF that is used in only 1 branch

;; TODO: Detect a LET* that could simply be a LET.

;; TODO: Detect a B* that could simply be a LET or LET* (maybe)

;; TODO: Add option to diable checking for the acl2 system itself.

;; TODO: Add support for supressing more kinds of reports.

;; TODO: Suppress reasoning-based checks (like those involving types) on :program mode functions.

(include-book "format-strings")
(include-book "quote")
(include-book "my-get-event")
(include-book "defun-forms")
(include-book "world")
(include-book "conjuncts-and-disjuncts")
(include-book "kestrel/terms-light/sublis-var-simple" :dir :system)
(include-book "tools/prove-dollar" :dir :system)
(include-book "book-of-event")

     ;move?
;; TODO: Maybe print paths relative to the cbd?
(defun describe-event-location (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))
                  :mode :program))
  (let ((loc (book-of-event name wrld)))
    (if (not loc)
        "Checking" ;todo: ensure this doesn't happen?
      (if (eq :built-in loc)
          "Checking built-in event"
        (if (eq :top-level loc)
            "Checking top-level event"
          (concatenate 'string loc " checking"))))))

;; Returns (mv defun-names defthm-nams)
(defun defuns-and-defthms-in-world (world triple-to-stop-at whole-world defuns-acc defthms-acc)
  (declare (xargs :guard (and (plist-worldp world)
                              (plist-worldp whole-world)
                              (true-listp defuns-acc)
                              (true-listp defthms-acc))))
  (if (endp world)
      (mv defuns-acc defthms-acc) ; oldest ones come first
    (let ((triple (first world)))
      (if (equal triple triple-to-stop-at)
          (prog2$ (cw "~%Note: Not checking anything in the linter itself, any books included before the linter, or the ACL2 system itself.  To override, use linter option :check :all.~%~%")
                  (mv (reverse defuns-acc)
                      (reverse defthms-acc)))
        (let ((symb (car triple))
              (prop (cadr triple)))
          (if (and (eq prop 'unnormalized-body)
                   (fgetprop symb 'unnormalized-body nil whole-world) ;todo: hack: make sure the function is still defined (why does this sometimes fail?)
                   )
              (defuns-and-defthms-in-world (rest world) triple-to-stop-at whole-world (cons symb defuns-acc) defthms-acc)
            (if (eq prop 'theorem)
                (defuns-and-defthms-in-world (rest world) triple-to-stop-at whole-world defuns-acc (cons symb defthms-acc))
              (defuns-and-defthms-in-world (rest world) triple-to-stop-at whole-world defuns-acc defthms-acc))))))))

;dup
(defun enquote-list (items)
  (declare (xargs :guard t))
  (if (atom items)
      nil
    (cons (enquote (car items))
          (enquote-list (cdr items)))))

(defun symbolic-length (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      (prog2$ (cw "Note: unable to get symbolic length of term ~x0.~%" term)
              0)
    (if (fquotep term)
        (len (unquote term))
      (if (eq 'cons (ffn-symb term))
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

;; (defun symbolic-strip-cdrs (term)
;;   (declare (xargs :guard (pseudo-termp term)))
;;   (if (variablep term)
;;       (cw "Note: unable to get symbolic strip-cdrs of term ~x0.~%" term)
;;     (if (quotep term) ; includes the case when term is 'nil
;;         (if (alistp (unquote term))
;;             (enquote-list (strip-cdrs (unquote term)))
;;           (cw "Note: unable to get symbolic strip-cdrs of term ~x0.~%" term))
;;       (let ((fn (ffn-symb term)))
;;         (if (eq 'cons fn)
;;             (let ((pair (farg1 term)))
;;               (cons (symbolic-cdr pair)
;;                     (symbolic-strip-cdrs (farg2 term))))
;;           (if (eq 'acons fn)
;;               (cons (farg2 term)
;;                     (symbolic-strip-cdrs (farg3 term)))
;;             (if (eq 'pairlis$ fn)
;;                 (take (symbolic-length (farg1 term))
;;                       (symbolic-elements (farg2 term)))
;;               (if (eq 'pairlis2 fn)
;;                   (symbolic-elements (farg2 term))
;;                 (cw "Note: unable to get symbolic strip-cdrs of term ~x0.~%" term)))))))))

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

;; Represent a symbol, including its package, as a string.
;; TODO: Does this exist somewhere?
(defun symbol-to-string (sym)
  (declare (xargs :guard (symbolp sym)))
  (let ((package-name (symbol-package-name sym)))
    (if (equal "ACL2" package-name)
        (symbol-name sym)
      (concatenate 'string package-name "::" (symbol-name sym)))))

;; Either a symbol (meaning we're checking the body of that function) or a string describing what we are checking.
(defun thing-being-checkedp (thing)
  (declare (xargs :guard t))
  (or (symbolp thing)
      (stringp thing)))

(defun thing-being-checked-to-string (thing)
  (declare (xargs :guard (thing-being-checkedp thing)))
  (if (symbolp thing)
      (symbol-to-string thing)
    thing))

(defun check-first-arg-as-ctx (form thing-being-checked)
  (let ((ctx (farg1 form)))
    (and (quotep ctx)
         (symbolp (unquote ctx))
         (symbolp thing-being-checked)
         (not (eq (unquote ctx) thing-being-checked))
         ;; Suppress warning if ctx is a prefix of the function (e.g., ctx of foo inside foo-fn):
         (let ((ctx-chars (coerce (symbol-name (unquote ctx)) 'list))
               (thing-being-checked-chars (coerce (symbol-name thing-being-checked) 'list)))
           (not (my-prefixp ctx-chars thing-being-checked-chars)))
         ;; Suppress warning for context from ASSERT, STATE-GLOBAL-LET*, etc:
         (not (member-eq (unquote ctx) '(assert$ state-global-let*)))
         (cw "(In ~s0,~% context ~x1 is used in call of ~x2.)~%~%" (thing-being-checked-to-string thing-being-checked) ctx (ffn-symb form)))))

(defun check-keys-of-alist-wrt-format-string (string alist thing-being-checked call)
  (let* ((args-mentioned (args-in-format-string string)) ;these are chars
         (alist-keys (symbolic-strip-cars alist))
         (quoted-args-mentioned (enquote-list args-mentioned)))
    (progn$ (if (not (no-duplicatesp alist-keys))
                (cw "(In ~s0,~% questionable format string use in ~x1. Duplicate keys in alist: ~x2)~%~%" (thing-being-checked-to-string thing-being-checked) call alist-keys)
              nil)
     (if (not (subsetp-equal quoted-args-mentioned alist-keys))
                (cw "(In ~s0,~% questionable format string use in ~x1. Missing args? Mentioned args are ~x2 but alist keys are ~x3)~%~%" (thing-being-checked-to-string thing-being-checked) call quoted-args-mentioned alist-keys)
              nil)
            (if (not (subsetp-equal alist-keys quoted-args-mentioned))
                (cw "(In ~s0,~% questionable format string use in ~x1. Extra args? Mentioned args are ~x2 but alist keys are ~x3)~%~%" (thing-being-checked-to-string thing-being-checked) call quoted-args-mentioned alist-keys)
              nil))))

;; (defun check-vals-of-alist-wrt-format-string (string alist thing-being-checked call)
;;   (let* ((args-mentioned (args-in-format-string string)) ;these are chars
;;          (max-arg-mentioned (max-val-of-chars args-mentioned))
;;          (alist-vals (symbolic-strip-cdrs alist))
;;          (len-vals (len alist-vals)))
;;     (if (<= len-vals max-arg-mentioned)
;;         (cw "(In ~s0,~% questionable format string use in ~x1. Not enough args given?)~%~%" (thing-being-checked-to-string thing-being-checked) call)
;;       nil)))

(defun check-call-of-fmt-function (call thing-being-checked)
  (let ((string (farg1 call)))
    (and (quotep string)
         (let ((string (unquote string))
               (alist (farg2 call)))
           ;; we check the vals of the alist since the keys are always the digits 0 through 9:
           (check-keys-of-alist-wrt-format-string string alist thing-being-checked call)))))

(defun check-call-of-hard-error (call thing-being-checked suppress)
  (prog2$ (and (not (member-eq :context suppress))
               (check-first-arg-as-ctx call thing-being-checked))
          (let ((string (farg2 call)))
            (and (quotep string)
                 (let ((string (unquote string))
                       (alist (farg3 call)))
                   (check-keys-of-alist-wrt-format-string string alist thing-being-checked call))))))

(defun check-call-of-illegal (call thing-being-checked suppress)
  (prog2$ (and (not (member-eq :context suppress))
               (check-first-arg-as-ctx call thing-being-checked))
          (let ((string (farg2 call)))
            (and (quotep string)
                 (let ((string (unquote string))
                       (alist (farg3 call)))
                   (check-keys-of-alist-wrt-format-string string alist thing-being-checked call))))))

;; For a call of EQUAL, report an issue if EQ, EQL, or = could be used instead.
(defun check-call-of-equal (term ; let-bound vars have been replaced in this
                            orig-term
                            type-alist thing-being-checked
                            suppress
                            state)
  (declare (xargs :guard (pseudo-termp term)
                  :mode :program
                  :stobjs state))
  (prog2$
   (and (not (member-eq :equal-self suppress))
        (equal (farg1 term) (farg2 term))
        ;; substitution may have occured, so the args of term may not actually be idential forms
        (cw "(In ~s0,~% EQUAL test ~x1 compares a value with an identical value.)~%~%" (thing-being-checked-to-string thing-being-checked) orig-term))
   (and (not (member-eq :equality-variant suppress))
        (b* ((arg1 (farg1 term))
             (arg2 (farg2 term))
             ((mv type-set1 &)
              (type-set arg1 nil nil type-alist (ens state) (w state) nil nil nil))
             ((mv type-set2 &)
              (type-set arg2 nil nil type-alist (ens state) (w state) nil nil nil))
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
                          (cw "(In ~s0,~% EQUAL test ~x1 could use EQ since both arguments are known to be symbols.)~%~%"
                              (thing-being-checked-to-string thing-being-checked) orig-term)
                        (cw "(In ~s0,~% EQUAL test ~x1 could use EQ since ~x2 is known to be a symbol.)~%~%"
                            (thing-being-checked-to-string thing-being-checked) orig-term arg1))
                    (if arg2-symbolp
                        (cw "(In ~s0,~% EQUAL test ~x1 could use EQ since ~x2 is known to be a symbol.)~%~%"
                            (thing-being-checked-to-string thing-being-checked) orig-term arg2)
                      nil))
                  (and arg1-numberp
                       arg2-numberp
                       (cw "(In ~s0,~% EQUAL test ~x1 could use = since both arguments are known to be numbers.)~%~%"
                           (thing-being-checked-to-string thing-being-checked) orig-term))
                  (and (not arg1-symbolp)
                       (not arg2-symbolp)
                       (not (and arg1-numberp
                                 arg2-numberp))
                       (if arg1-eqlablep
                           (if arg2-eqlablep
                               (cw "(In ~s0,~% EQUAL test ~x1 could use EQL since both arguments are known to be numbers, symbols, or characters.)~%~%"
                                   (thing-being-checked-to-string thing-being-checked) orig-term)
                             (cw "(In ~s0,~% EQUAL test ~x1 could use EQL since ~x2 is known to be a number, symbol, or character.)~%~%"
                                 (thing-being-checked-to-string thing-being-checked) orig-term arg1))
                         (if arg2-eqlablep
                             (cw "(In ~s0,~% EQUAL test ~x1 could use EQL since ~x2 is known to be a number, symbol, or character.)~%~%"
                                 (thing-being-checked-to-string thing-being-checked) orig-term arg2)
                           nil))))))))

;; For a call of EQL, report an issue if both arguments are known to be
;; non-eqlable.  Also report if EQ or = could be used instead.
(defun check-call-of-eql (term ; let-bound vars have been replaced in this
                          orig-term
                          type-alist thing-being-checked suppress state)
  (declare (xargs :guard (pseudo-termp term)
                  :mode :program
                  :stobjs state))
  (prog2$
   (and (not (member-eq :equal-self suppress))
        (equal (farg1 term) (farg2 term))
        ;; substitution may have occured, so the args of term may not actually be idential forms
        (cw "(In ~s0,~% EQL test ~x1 compares a value with an identical value.)~%~%" (thing-being-checked-to-string thing-being-checked) orig-term))
   (and (not (member-eq :equality-variant suppress))
        (b* ((arg1 (farg1 term))
             (arg2 (farg2 term))
             ((mv type-set1 &)
              (type-set arg1 nil nil type-alist (ens state) (w state) nil nil nil))
             ((mv type-set2 &)
              (type-set arg2 nil nil type-alist (ens state) (w state) nil nil nil))
             ;;(decoded-ts1 (decode-type-set type-set1))
             ;;(decoded-ts2 (decode-type-set type-set2))
             (arg1-symbolp (ts-subsetp type-set1 *ts-symbol*))
             (arg2-symbolp (ts-subsetp type-set2 *ts-symbol*))
             (arg1-numberp (ts-subsetp type-set1 *ts-acl2-number*))
             (arg2-numberp (ts-subsetp type-set2 *ts-acl2-number*))
             (ts-eqlable (ts-union *ts-symbol*
                                   (ts-union *ts-character*
                                             *ts-acl2-number*))))
          (progn$ (if arg1-symbolp
                      (if arg2-symbolp
                          (cw "(In ~s0,~% EQL test ~x1 could use EQ since both arguments are known to be symbols.)~%~%"
                              (thing-being-checked-to-string thing-being-checked) orig-term)
                        (cw "(In ~s0,~% EQL test ~x1 could use EQ since ~x2 is known to be a symbol.)~%~%"
                            (thing-being-checked-to-string thing-being-checked) orig-term arg1))
                    (if arg2-symbolp
                        (cw "(In ~s0,~% EQL test ~x1 could use EQ since ~x2 is known to be a symbol.)~%~%"
                            (thing-being-checked-to-string thing-being-checked) orig-term arg2)
                      nil))
                  (and arg1-numberp
                       arg2-numberp
                       (cw "(In ~s0,~% EQL test ~x1 could use = since both arguments are known to be numbers.)~%~%"
                           (thing-being-checked-to-string thing-being-checked) orig-term))
                  (and (ts-disjointp type-set1 ts-eqlable)
                       (ts-disjointp type-set2 ts-eqlable)
                       (cw "(In ~s0,~% ill-guarded call ~x1 since both ~x2 and ~x3 are not numbers, symbols, or characters.)~%~%"
                           (thing-being-checked-to-string thing-being-checked) orig-term arg1 arg2)))))))

;; For a call of EQ, report an issue if both arguments are known to be non-symbols.
(defun check-call-of-eq (term ; let-bound vars have been replaced in this
                         orig-term
                         type-alist thing-being-checked suppress state)
  (declare (xargs :guard (pseudo-termp term)
                  :mode :program
                  :stobjs state))
  (prog2$
   (and (not (member-eq :equal-self suppress))
        (equal (farg1 term) (farg2 term))
        ;; substitution may have occured, so the args of term may not actually be idential forms
        (cw "(In ~s0,~% EQ test ~x1 compares a value with an identical value.)~%~%" (thing-being-checked-to-string thing-being-checked) orig-term))
   (and (not (member-eq :equality-variant suppress))
        (b* ((arg1 (farg1 term))
             (arg2 (farg2 term))
             ((mv type-set1 &)
              (type-set arg1 nil nil type-alist (ens state) (w state) nil nil nil))
             ((mv type-set2 &)
              (type-set arg2 nil nil type-alist (ens state) (w state) nil nil nil))
             ;;(decoded-ts1 (decode-type-set type-set1))
             ;;(decoded-ts2 (decode-type-set type-set2))
             )
          (progn$ (and (ts-disjointp type-set1 *ts-symbol*)
                       (ts-disjointp type-set2 *ts-symbol*)
                       (cw "(In ~s0,~% ill-guarded call ~x1 since both ~x2 and ~x3 are not symbols.)~%~%"
                           (thing-being-checked-to-string thing-being-checked) orig-term arg1 arg2)))))))

;; For a call of =, report an issue if either argument is known to be a non-number.
(defun check-call-of-= (term ; let-bound vars have been replaced in this
                        orig-term
                        type-alist thing-being-checked suppress state)
  (declare (xargs :guard (pseudo-termp term)
                  :mode :program
                  :stobjs state))
  (prog2$
   (and (not (member-eq :equal-self suppress))
        (equal (farg1 term) (farg2 term))
        ;; substitution may have occured, so the args of term may not actually be idential forms
        (cw "(In ~s0,~% = test ~x1 compares a value with an identical value.)~%~%" (thing-being-checked-to-string thing-being-checked) orig-term))
   (and (not (member-eq :equality-variant suppress))
        (b* ((arg1 (farg1 term))
             (arg2 (farg2 term))
             ((mv type-set1 &)
              (type-set arg1 nil nil type-alist (ens state) (w state) nil nil nil))
             ((mv type-set2 &)
              (type-set arg2 nil nil type-alist (ens state) (w state) nil nil nil))
             ;;(decoded-ts1 (decode-type-set type-set1))
             ;;(decoded-ts2 (decode-type-set type-set2))
             )
          (progn$ (and (ts-disjointp type-set1 *ts-acl2-number*)
                       (cw "(In ~s0,~% ill-guarded call ~x1 since ~x2 is not a number.)~%~%"
                           (thing-being-checked-to-string thing-being-checked) orig-term arg1))
                  (and (ts-disjointp type-set2 *ts-acl2-number*)
                       (cw "(In ~s0,~% ill-guarded call ~x1 since ~x2 is not a number.)~%~%"
                           (thing-being-checked-to-string thing-being-checked) orig-term arg2)))))))

(defun filter-subst (subst vars)
  (if (endp subst)
      nil
    (let ((pair (first subst)))
      (if (member-eq (car pair) vars)
          (cons pair (filter-subst (rest subst) vars))
        (filter-subst (rest subst) vars)))))

;; Recognize the translated form of mbt, possibly with not(s) wrapped around it.
(defun possibly-negated-mbtp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      nil
    (case (ffn-symb term)
      (not (possibly-negated-mbtp (farg1 term)))
      (return-last (and (equal (farg1 term) ''mbe1-raw)
                        (equal (farg2 term) ''t)))
      (t nil))))

;; Try to resolve TERM wrt SUBST, assuming the information in the TYPE-ALIST.
;; Returns :true, :false, or nil (could not resolve).
(defun try-to-resolve (term subst type-alist state)
  (declare (xargs :stobjs state
                  :mode :program))
  (and
   ;; It's not surprising for an MBT (or its negation), so we suppress that:
   (not (possibly-negated-mbtp term))
   (b* (
        ;; Apply the subst before checking:
        (term (sublis-var-simple subst term))
        ;; Get the type:
        ((mv type-set &)
         (type-set term nil nil type-alist (ens state) (w state) nil nil nil))
        ;; (decoded-ts (decode-type-set type-set))
        ;; (reportp (and term-knownp
        ;;               ;; Suppress calls of integerp that
        ;;               ;; are known to be true since these
        ;;               ;; often arise from things like
        ;;               ;; (the unsigned-byte x):
        ;;               ;; (not (and (eql type-set *TS-T*)
        ;;               ;;           (call-of 'integerp term)))
        ;;               ))
        )
     (if (= *ts-nil* type-set)
         :false
       (if (= 0 (logand *ts-nil* type-set)) ;check for non-nil
           :true
         nil ; could not resolve
         )))))

;; The subst includes bindings of vars from overarching lambdas.
;; TODO: Track and use the context from overarching IF tests.
(mutual-recursion
 ;; For a call of IF, report an issue if the test is known non-nil or known-nil (by type-set).
 (defun lint-call-of-if (term subst type-alist iff-flag thing-being-checked suppress state)
   (declare (xargs :guard (pseudo-termp term)
                   :mode :program
                   :stobjs state))
   (progn$
    (and (not (member-eq :resolvable-test suppress))
         (let* ((test (farg1 term))
                (res (try-to-resolve test subst type-alist state)))
           (case res
             (:true (and (not (or (call-of 'synp test)  ; syntaxp and bind-free hyps are known true, but that is not interesting
                                  (call-of 'axe-syntaxp test)))
                         (progn$
                          (cw "(In ~s0,~% the IF test in ~x1 is known to be true~%" (thing-being-checked-to-string thing-being-checked) term)
                          (cw "  Type-alist: ~x0~%" (decode-type-alist type-alist))
                          (let ((relevant-subst (filter-subst subst (all-vars test))))
                            (if relevant-subst
                                (cw "  Relevant substitutions ~x0)~%~%" relevant-subst)
                              (cw ")~%~%"))))))
             (:false (progn$
                      (cw "(In ~s0,~% the IF test in ~x1 is known to be false~%" (thing-being-checked-to-string thing-being-checked) term)
                      (cw "  Type-alist: ~x0~%" (decode-type-alist type-alist))
                      (let ((relevant-subst (filter-subst subst (all-vars test))))
                        (if relevant-subst
                            (cw "  Relevant substitutions ~x0)~%~%" relevant-subst)
                          (cw ")~%~%")))))
             (nil nil))))
    ;; Check the test recursively:
    (lint-term (farg1 term) subst type-alist
                nil ; we use nil here because we handle the test above
                thing-being-checked suppress state)
    (b* (((mv & & then-type-alist else-type-alist &)
          (assume-true-false (farg1 term) nil nil nil type-alist (ens state) (w state) nil nil nil)))
      (prog2$
       ;; check the then-branch:
       (if (equal (farg1 term) (farg2 term))
           nil ;; for (if x x y) don't check x twice.  this can come from (or x y).
         (if (quotep (farg2 term))
             nil ; don't check constant if-branches (very common to implement ands or ors)
           (lint-term (farg2 term) subst then-type-alist
                       iff-flag ; lets us catch branches that are resolvable but not constants, assuming the whole IF is in an IFF context
                       thing-being-checked suppress state)))
       ;; check the else-branch:
       (if (quotep (farg3 term))
           nil ; don't check constant if-branches (very common to implement ands or ors)
         (lint-term (farg3 term) subst else-type-alist
                     iff-flag ; lets us catch branches that are resolvable but not constants, assuming the whole IF is in an IFF context
                     thing-being-checked suppress state))))
    (and (equal (farg2 term) (farg3 term))
         (cw "(In ~s0,~% both branches of ~x1 are the same.)~%~%" (thing-being-checked-to-string thing-being-checked) term))))

 ;; add constant-surprising arg...
 (defun lint-term (term subst type-alist iff-flag thing-being-checked suppress state)
   (declare (xargs :guard (pseudo-termp term)
                   :mode :program
                   :stobjs state))
   (prog2$
    ;; If we are in an IFF context, check whether the term is known to be nil or non-nil:
    (and (not (member-eq :resolvable-test suppress))
         iff-flag
         (let ((res (try-to-resolve term subst type-alist state)))
           (case res
             (:true
              (progn$ (cw "(In ~s0,~% ~x1 is known to be true and is used in an IFF context~%" (thing-being-checked-to-string thing-being-checked) term)
                      (cw "  Type-alist: ~x0~%" (decode-type-alist type-alist))
                      (let ((relevant-subst (filter-subst subst (all-vars term))))
                        (if relevant-subst
                            (cw "  Relevant substitutions ~x0)~%~%" relevant-subst)
                          (cw ")~%~%")))))
             (:false
              (progn$ (cw "(In ~s0,~% ~x1 is known to be false and is used in an IFF context~%" (thing-being-checked-to-string thing-being-checked) term)
                      (cw "  Type-alist: ~x0~%" (decode-type-alist type-alist))
                      (let ((relevant-subst (filter-subst subst (all-vars term))))
                        (if relevant-subst
                            (cw "  Relevant substitutions ~x0)~%~%" relevant-subst)
                          (cw ")~%~%")))))
             (nil nil))))
    (if (variablep term)
        nil
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            nil
          (if (member-eq fn '(the-check ;suppress checks done for (the ...)
                              check-dcl-guardian ;used in b*?
                              ))
              nil
            (if (eq 'if fn) ; separate because we process the args differently
                (lint-call-of-if term subst type-alist iff-flag thing-being-checked suppress state)
              (prog2$ (lint-terms (fargs term) subst type-alist
                                   nil ; iff-flag
                                   thing-being-checked suppress state)
                      ;; TODO: Use the subst for these?
                      (if (member-eq fn '(fmt fms fmt1 fmt-to-comment-window))
                          (check-call-of-fmt-function term thing-being-checked)
                        (if (eq fn 'equal)
                            (check-call-of-equal (sublis-var-simple subst term) term type-alist thing-being-checked suppress state)
                          (if (eq fn 'eql)
                              (check-call-of-eql (sublis-var-simple subst term) term type-alist thing-being-checked suppress state)
                            (if (eq fn 'eq)
                                (check-call-of-eq (sublis-var-simple subst term) term type-alist thing-being-checked suppress state)
                              (if (eq fn '=)
                                  (check-call-of-= (sublis-var-simple subst term) term type-alist thing-being-checked suppress state)
                                (if (eq fn 'hard-error)
                                    (check-call-of-hard-error term thing-being-checked suppress)
                                  (if (eq fn 'illegal)
                                      (check-call-of-illegal term thing-being-checked suppress)
                                    (if (consp fn) ;check for lambda
                                        (lint-term (lambda-body fn)
                                                    ;; new subst, since we are in a lambda body
                                                    (pairlis$ (lambda-formals fn)
                                                              (sublis-var-simple-lst subst (fargs term)))
                                                    type-alist iff-flag thing-being-checked suppress state)
                                      (and (not (member-eq :ground-term suppress))
                                           (not (eq 'synp (ffn-symb term))) ; synp calls are usually ground terms
                                           (quote-listp (fargs term))
                                           (cw "(In ~s0,~% ground term ~x1 is present.)~%~%" (thing-being-checked-to-string thing-being-checked) term))))))))))))))))))

 (defun lint-terms (terms subst type-alist iff-flag thing-being-checked suppress state)
   (declare (xargs :guard (and (true-listp terms)
                               (pseudo-term-listp terms))
                   :stobjs state))
   (if (endp terms)
       nil
     (prog2$ (lint-term (car terms) subst type-alist iff-flag thing-being-checked suppress state)
             (lint-terms (cdr terms) subst type-alist iff-flag thing-being-checked suppress state)))))

;; Returns state.
(defun check-for-contradiction (ctx description term step-limit state)
  (declare (xargs :guard (and (stringp description)
                              (pseudo-termp term)
                              (natp step-limit)
                              )
                  :stobjs state
                  :mode :program))
  (b* (((mv erp res state)
        (prove$ `(not ,term) :step-limit step-limit))
       ((when erp)
        (er hard? 'check-for-contradiction "Error checking for contradiction in ~s0: ~X12." description term nil)
        state))
    (if res
        (prog2$ (cw "(In ~x0,~% ~s1 ~x2 is provably contradictory.)~%" ctx description term)
                state)
      state)))

;; Returns state.
(defun lint-defun (fn assume-guards suppress step-limit state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* ((body (fn-body fn t (w state)))
       ;; (formals (fn-formals fn (w state)))
       (event (my-get-event fn (w state)))
       (declares (and (defun-or-mutual-recursion-formp event)
                      (get-declares-from-event fn event)))
       (xargs (get-xargs-from-declares declares))
       (guard-debug-res (assoc-keyword :guard-debug xargs))
       (guard (fn-guard fn (w state)))
       ;; Initialize the type-alist by assuming the function's guard:
       ((mv & & type-alist & &)
        (if assume-guards
            (assume-true-false guard nil nil nil nil (ens state) (w state) nil nil nil)
          ;; Start with a type-alist of nil since we are not assuming guards:
          (mv nil nil nil nil nil))))
    (progn$ (and (not (member-eq :guard-debug suppress))
                 guard-debug-res
                 (cw "(~x0 has a :guard-debug xarg, ~x1.)~%~%" fn (second guard-debug-res)))
            (and (not (equal guard *t*)) ;; a guard of T is resolvable but uninterseting
                 (lint-term guard
                             nil ;empty substitution
                             nil ;type-alist
                             t   ;iff-flag
                             (concatenate 'string "guard of " (symbol-to-string fn))
                             suppress state))
            (lint-term body
                        nil ;empty substitution
                        type-alist
                        nil ;iff-flag
                        fn
                        suppress state)
            (let ((state (check-for-contradiction fn "guard" guard step-limit state)))
              state))))

;; Returns state.
(defun lint-defuns (fns assume-guards suppress skip-fns step-limit state)
  (declare (xargs :stobjs state
                  :guard (and ;todo: more
                          (symbol-listp skip-fns))
                  :mode :program))
  (if (atom fns)
      state
    (let* ((fn (first fns))
           (checkp (not (member-eq fn skip-fns)))
           (state (if checkp
                      (progn$ (cw "~s0 ~x1.~%" (describe-event-location fn (w state)) fn)
                              (lint-defun fn assume-guards suppress step-limit state))
                    state)))
      (lint-defuns (rest fns) assume-guards suppress skip-fns step-limit state))))

;; Returns (mv hyps conc).
(defun get-hyps-and-conc (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (call-of 'implies term)
      (mv-let (hyps1 conc)
        (get-hyps-and-conc (farg2 term))
        (mv (append (get-conjuncts (farg1 term))
                    hyps1)
            conc))
    ;; todo: handle lambdas
    (mv nil term)))

;; Check whether any of the TERMS is implied by the ALL-TERMS, excluding itself
;; Returns state.
(defun check-for-implied-terms-aux (ctx description terms all-terms step-limit state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (endp terms)
      state
    (b* ((term (first terms))
         ;; skip syntaxp, bind-free, axe-syntaxp, etc:
         ((when (or (call-of 'synp term)
                    (call-of 'axe-syntaxp term)
                    (call-of 'axe-bind-free term)))
          (check-for-implied-terms-aux ctx description (rest terms) all-terms step-limit state))
         (rest-terms (remove-equal term all-terms))
         ((mv erp res state)
          (prove$ `(implies ,(make-conjunction-from-list rest-terms) ,term) :step-limit step-limit))
         ((when erp)
          (er hard? 'check-for-implied-terms-aux "Error checking for implication in ~s0 in ~x1." description ctx)
          state)
         (- (and res (cw "(In ~x0,~% ~s1 ~x2 is provably implied by others.)~%" ctx description term))))
      (check-for-implied-terms-aux ctx description (rest terms) all-terms step-limit state))))

;; Checks whether any of the TERMS is implied by the others.  Returns state.
(defun check-for-implied-terms (ctx description terms step-limit state)
  (declare (xargs :stobjs state
                  :mode :program))
  (check-for-implied-terms-aux ctx description terms terms step-limit state))

(defun make-unary-calls (fns arg)
  (if (endp fns)
      nil
    (cons `(,(first fns) ,arg)
          (make-unary-calls (rest fns) arg))))

;; todo: allow weakening to be read from a a table, so we can do things like pfield::fep -> natp
(defund get-weakenings (hyp)
  (and (consp hyp)
       (let ((fn (ffn-symb hyp)))
         (case fn
           ;; TODO: Could try atom for all atoms...
           (bitp (make-unary-calls '(natp integerp rationalp acl2-numberp) (farg1 hyp))) ;todo: try (< 0 ...)
           (posp (make-unary-calls '(natp integerp rationalp acl2-numberp) (farg1 hyp))) ;todo: try (< 0 ...)
           ;; (minusp (make-unary-calls '() (farg1 hyp))) ;todo: try (<= ... 0)
           ;; (plusp (make-unary-calls '() (farg1 hyp))) ;todo: try (<= ... 0)
           (natp (make-unary-calls '(integerp rationalp acl2-numberp) (farg1 hyp))) ;todo: try (<= 0 ...)
           (unsigned-byte-p (make-unary-calls '(natp integerp rationalp acl2-numberp) (farg1 hyp))) ;todo: try (<= 0 ...)
           (signed-byte-p (make-unary-calls '(integerp rationalp acl2-numberp) (farg1 hyp)))
           (integerp (make-unary-calls '(rationalp acl2-numberp) (farg1 hyp)))
           (integer-rangep (make-unary-calls '(integerp rationalp acl2-numberp) (farg1 hyp)))
           (rationalp (make-unary-calls '(acl2-numberp) (farg1 hyp)))
           (real/rationalp (make-unary-calls '(acl2-numberp) (farg1 hyp)))
           (complex-rationalp (make-unary-calls '(acl2-numberp) (farg1 hyp)))
           (symbolp (make-unary-calls '(atom) (farg1 hyp)))
           (null (make-unary-calls '(symbolp atom) (farg1 hyp)))
           (alistp (make-unary-calls '(true-listp) (farg1 hyp)))
           (symbol-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (symbol-alistp (make-unary-calls '(alistp true-listp) (farg1 hyp)))
           (character-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (integer-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (nat-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (rational-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (string-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (keyword-listp (make-unary-calls '(true-listp) (farg1 hyp)))
           (consp (list `(not (symbolp ,(farg1 hyp)))
                        `(not (null ,(farg1 hyp))) ;; or try the naked (farg1 hyp)?
                        ))
           (keywordp (make-unary-calls '(symbolp atom) (farg1 hyp)))
           ;;todo: add many more, or find weakenings from implication theorems
           (< (list `(<= ,(farg1 hyp) ,(farg2 hyp))))
           ;; todo: only do these if the things involved are numbers:
           (equal (list `(<= ,(farg1 hyp) ,(farg2 hyp))
                        `(<= ,(farg2 hyp) ,(farg1 hyp))))
           (otherwise nil)))))

;; Returns state.
(defun try-to-prove-with-some-hyp (ctx hyps other-hyps conclusion original-hyp step-limit state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (endp hyps)
      state
    (b* ((hyp (first hyps))
         ((mv erp res state)
          (prove$ `(implies ,(make-conjunction-from-list (cons hyp other-hyps)) ,conclusion) :step-limit step-limit))
         ((when erp)
          (er hard? 'try-to-prove-with-some-hyp "Error attempting to weaken a hyp ~x0 in ~x1 to ~x2." original-hyp ctx hyp)
          state)
         (- (and res (cw "(In ~x0,~% hyp ~x1 can be provably weakened to ~x2)~%" ctx original-hyp hyp))))
      (try-to-prove-with-some-hyp ctx (rest hyps) other-hyps conclusion original-hyp step-limit state))))


;; Checks whether any of the HYPS can be dropped from ALL-HYPS, while still
;; allowing CONCLUSION to be proved.  Returns state.
(defun check-for-droppable-hyps (ctx hyps all-hyps conclusion step-limit state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (endp hyps)
      state
    (b* ((hyp (first hyps))
         (other-hyps (remove-equal hyp all-hyps))
         ((mv erp res state)
          (prove$ `(implies ,(make-conjunction-from-list other-hyps) ,conclusion) :step-limit step-limit))
         ((when erp)
          (er hard? 'check-for-droppable-hyps "Error attempting to drop hyp ~x0 in ~x1." hyp ctx)
          state)
         (- (and res (cw "(In ~x0,~% hyp ~x1 is provably unnecessary.)~%" ctx hyp)))
         (state (if res
                    state ;; don't try to weaken, since the hyp can be dropped
                  (let* ((weakenings (get-weakenings hyp))
                         (state (try-to-prove-with-some-hyp ctx weakenings other-hyps conclusion hyp step-limit state)))
                    state))))
      (check-for-droppable-hyps ctx (rest hyps) all-hyps conclusion step-limit state))))

;; Returns state.
;; For example, a hyp of (syntaxp (quote x)) is almost certainly an error (should be quotep, not quote).
(defun check-synp-hyp (ctx hyp step-limit state)
  (declare (xargs :guard (and ;; (symbolp ctx)
                          (pseudo-termp hyp)
                          (call-of 'synp hyp))
                  :stobjs state
                  :mode :program))
  (if (equal *nil* (farg1 hyp))     ;; (synp 'nil <form> '(if <term> 't 'nil))
      (if (and (quotep (farg3 hyp)) ;always true?
               (pseudo-termp (unquote (farg3 hyp)))
               (call-of 'if (unquote (farg3 hyp)))
               (equal *t* (farg2 (unquote (farg3 hyp))))
               (equal *nil* (farg3 (unquote (farg3 hyp))))
               )
          (let* ((core-term (farg1 (unquote (farg3 hyp)))))
            (if (not (logic-fnsp core-term (w state)))
                (prog2$ (cw "(Skipping checking syntaxp hyp ~x0 in ~x1 because it contains :program mode functions.)~%" hyp ctx)
                        state)
              (let ((conjuncts (get-conjuncts core-term)))
                (check-for-implied-terms ctx
                                         "syntaxp conjunct"
                                         conjuncts step-limit state))))
        (prog2$ (er hard? 'check-synp-hyp "unexpected form of synp: ~x0." hyp)
                state))
    state))

;; Returns state.
(defun check-hyps (ctx hyps all-hyps step-limit state)
  (declare (xargs :stobjs state
                  :mode :program)
           (irrelevant all-hyps) ;todo
           )
  (if (endp hyps)
      state
    (b* ((hyp (first hyps))
         (state (if (call-of 'synp hyp)
                    (check-synp-hyp ctx hyp step-limit state)
                  state)))
      (check-hyps ctx (rest hyps) all-hyps step-limit state))))

(defun drop-calls-of (fn terms)
  (if (endp terms)
      nil
    (if (call-of fn (first terms))
        (drop-calls-of fn (rest terms))
      (cons (first terms) (drop-calls-of fn (rest terms))))))

;; Returns state.
(defun lint-defthm (name ;assume-guards
                    suppress step-limit state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* ((body (defthm-body name (w state)))
       ;;optimize this?
       (untouchable-fns-in-body (intersection-eq (all-fnnames body)
                                                 (global-val 'untouchable-fns (w state))))
       ((when untouchable-fns-in-body)
        (prog2$ (cw "(Skipping checking of ~x0 because it mentions untouchable fns ~x1.)~%" name untouchable-fns-in-body)
                state))
       ((mv hyps conclusion)
        (get-hyps-and-conc body))
       (state (check-hyps name
                          hyps
                          hyps
                          step-limit
                          state))
       ;; check the hyps and conc individually:
       ;; Check the hyps, including checking for resolvable tests, ground terms ,etc:
       (- (lint-terms hyps
                      nil ;empty substitution
                      nil ;type-alist
                      nil ;iff-flag todo
                      name
                      suppress state))
       ;; Check the conclusion, including checking for ground terms ,etc:
       (- (lint-term conclusion
                     nil ;empty substitution
                     nil ;type-alist
                     nil ;iff-flag todo
                     name
                     (cons :resolvable-test suppress) ; don't report clearly true conjuncts in the conclusion (what about true disjuncts?)
                     state))
       (non-synp-hyps (drop-calls-of 'synp hyps))
       (non-synp-hyps (drop-calls-of 'axe-syntaxp non-synp-hyps))
       (non-synp-hyps (drop-calls-of 'axe-bind-free non-synp-hyps))
       ;; Check for contradictory hyps:
       (state (check-for-contradiction name
                                       "hyp"
                                       (make-conjunction-from-list non-synp-hyps)
                                       step-limit
                                       state))
       ;; todo: check for duplicate hyps
       ;; Check for hyps that are implied by others:
       (state (check-for-implied-terms name
                                       "hyp"
                                       non-synp-hyps
                                       step-limit
                                       state))
       ;; Check for hyps that can be dropped:
       (state (check-for-droppable-hyps name non-synp-hyps non-synp-hyps conclusion step-limit state)))
    state))

;; Returns state.
(defun lint-defthms (names ;assume-guards
                     suppress
                     names-to-skip
                     step-limit
                     state)
  (declare (xargs :stobjs state
                  :guard (and ;todo: more
                          (symbol-listp names-to-skip)
                          )
                  :mode :program))
  (if (atom names)
      state
    (let* ((name (first names))
           (checkp (not (member-eq name names-to-skip)))
           (state (if checkp
                      (progn$ (cw "~s0 ~x1.~%" (describe-event-location name (w state)) name)
                              (lint-defthm name ;assume-guards
                                           suppress step-limit state))
                    state)))
      (lint-defthms (rest names) ;assume-guards
                    suppress names-to-skip step-limit state))))


;todo: add support for more here
(defconst *warning-types*
  '(:ground-term
    :guard-debug
    :equality-variant
    :context
    :resolvable-test
    :equal-self))

;; Returns state
(defun run-linter-fn (event-range assume-guards suppress skip-fns check-defuns check-defthms step-limit state)
  (declare (xargs :stobjs state
                  :guard (and (member-eq event-range '(:after-linter :all))
                              (booleanp assume-guards)
                              (subsetp-eq suppress *warning-types*)
                              (symbol-listp skip-fns)
                              (booleanp check-defuns)
                              (booleanp check-defthms)
                              (natp step-limit))
                  :mode :program))
  (b* ((state (set-fmt-hard-right-margin 140 state))
       (state (set-fmt-soft-right-margin 140 state))
       (world (w state))
       (triple-to-stop-at (if (eq event-range :after-linter)
                              '(end-of-linter label . t)
                            nil))
       ((mv all-defuns all-defthms) (defuns-and-defthms-in-world world triple-to-stop-at world nil nil))
       (state (if check-defuns
                  (prog2$ (cw "Applying linter to ~x0 defuns:~%~%" (len all-defuns))
                          (lint-defuns all-defuns assume-guards suppress skip-fns step-limit state))
                state))
       (state (if check-defthms
                  (prog2$ (cw "~%Applying linter to ~x0 defthms:~%~%" (len all-defthms))
                          (lint-defthms all-defthms ; assume-guards
                                         suppress
                                         nil ;todo
                                         step-limit
                                         state))
                state)))
    state))

;; Call this macro to check every defun in the current ACL2 world.
(defmacro run-linter (&key (event-range ':after-linter) ;; either :after-linter (check only events introduced after the linter was included) or :all
                           (suppress '(:ground-term :context)) ;; types of check to skip
                           (assume-guards 't) ;; whether to assume guards when analyzing function bodies
                           (skip-fns 'nil) ;; functions to skip checking
                           (check-defuns 't)
                           (check-defthms 't)
                           (step-limit '1000)
                           )
  `(run-linter-fn ',event-range ',assume-guards ',suppress ',skip-fns ',check-defuns ',check-defthms ',step-limit state))

(deflabel end-of-linter)

;; to check theorems:
;; (include-book "kestrel/utilities/linter" :dir :system)
;; ... include your books here...
;; (set-ignore-ok t)
;; (acl2::run-linter :event-range :all :check-defuns nil :step-limit 100000 :suppress (:context :equality-variant :ground-term))
