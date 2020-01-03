; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; A nice challenge would be to verify guards in this book.

(in-package "ACL2")

(include-book "pseudo-good-worldp") ; :logic mode macro-args-structurep etc.

(include-book "verified-termination-and-guards") ; :logic mode er-cmp-fn

(include-book "kestrel") ; :logic mode macro-args

(verify-termination warning-off-p1) ; and guards

(verify-termination warning1-cw) ; and guards

(verify-termination duplicate-keys-action) ; and guards

(local ; could be useful towards verifying guards
 (defthm keyword-value-listp-remove-keyword
   (implies (keyword-value-listp x)
            (keyword-value-listp (remove-keyword key x)))))

(local ; could be useful towards verifying guards
 (defthm keyword-value-listp-cddr-assoc-keyword
   (implies (keyword-value-listp x)
            (keyword-value-listp (cddr (assoc-keyword key x))))))

(defun bind-macro-args-keys1 (args actuals allow-flg alist form wrld
                                   state-vars)

; We need parameter state-vars because of the call of warning$-cw1 below.

  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-keysp args nil)
                              (keyword-value-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (symbolp (car form))
                              (plist-worldp wrld)
                              (symbol-alistp
                               (table-alist 'duplicate-keys-action-table
                                            wrld))
                              (weak-state-vars-p state-vars))
                  :verify-guards nil))
  (cond ((endp args)
         (cond ((or (null actuals) allow-flg)
                (value-cmp alist))
               (t (er-cmp *macro-expansion-ctx*
                          "Illegal key/value args ~x0 in macro expansion of ~
                           ~x1.  The argument list for ~x2 is ~%~F3."
                          actuals form
                          (car form)
                          (macro-args (car form) wrld)))))
        ((eq (car args) '&allow-other-keys)
         (value-cmp alist))
        (t (let* ((formal (cond ((atom (car args))
                                 (car args))
                                ((atom (caar args))
                                 (caar args))
                                (t (cadr (caar args)))))
                  (key (cond ((atom (car args))
                              (intern (symbol-name (car args))
                                      "KEYWORD"))
                             ((atom (car (car args)))
                              (intern (symbol-name (caar args))
                                      "KEYWORD"))
                             (t (caaar args))))
                  (tl (assoc-keyword key actuals))
                  (alist (cond ((and (consp (car args))
                                     (= 3 (length (car args))))
                                (cons (cons (caddr (car args))
                                            (not (null tl)))
                                      alist))
                               (t alist)))
                  (name (car form))
                  (duplicate-keys-action
                   (and (assoc-keyword key (cddr tl))
                        (duplicate-keys-action name wrld)))
                  (er-or-warn-string
                   "The keyword argument ~x0 occurs twice in ~x1.  This ~
                    situation is explicitly allowed in Common Lisp (see ~
                    CLTL2, page 80) but it often suggests a mistake was ~
                    made.~@2  See :DOC set-duplicate-keys-action."))
             (prog2$
              (and (eq duplicate-keys-action :warning)
                   (warning$-cw1 *macro-expansion-ctx* "Duplicate-Keys"
                                 er-or-warn-string
                                 key
                                 form
                                 "  The leftmost value for ~x0 is used."))
              (cond
               ((eq duplicate-keys-action :error)
                (er-cmp *macro-expansion-ctx*
                        er-or-warn-string
                        key form ""))
               (t
                (bind-macro-args-keys1
                 (cdr args)
                 (remove-keyword key actuals)
                 allow-flg
                 (cons (cons formal
                             (cond (tl (cadr tl))
                                   ((atom (car args))
                                    nil)
                                   ((> (length (car args)) 1)
                                    (cadr (cadr (car args))))
                                   (t nil)))
                       alist)
                 form wrld state-vars))))))))

(defun chk-length-and-keys (actuals form wrld)
  (declare (xargs :guard (and (true-listp actuals)
                              (true-listp form)
                              (symbolp (car form))
                              (plist-worldp wrld))
                  :measure (acl2-count actuals)))
  (cond ((endp actuals)
         (value-cmp nil))
        ((null (cdr actuals))
         (er-cmp *macro-expansion-ctx*
                 "A non-even key/value arglist was encountered while macro ~
                  expanding ~x0.  The argument list for ~x1 is ~%~F2."
                 form
                 (car form)
                 (macro-args (car form) wrld)))
        ((keywordp (car actuals))
         (chk-length-and-keys (cddr actuals) form wrld))
        (t (er-cmp *macro-expansion-ctx*
                   "A non-keyword was encountered while macro expanding ~x0 ~
                    where a keyword was expected.  The formal parameters list ~
                    for ~x1 is ~%~F2."
                   form
                   (car form)
                   (macro-args (car form) wrld)))))

(defun bind-macro-args-keys (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-keysp args nil)
                              (true-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))
                  :verify-guards nil))
  (er-progn-cmp
   (chk-length-and-keys actuals form wrld)
   (let ((tl (assoc-keyword :allow-other-keys actuals)))
     (er-progn-cmp
      (cond ((assoc-keyword :allow-other-keys (cdr tl))
             (er-cmp *macro-expansion-ctx*
                     "ACL2 prohibits multiple :allow-other-keys because ~
                      implementations differ significantly concerning which ~
                      value to take."))
            (t (value-cmp nil)))
      (bind-macro-args-keys1
       args actuals
       (and tl (cadr tl))
       alist form wrld state-vars)))))

(defun bind-macro-args-after-rest (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-after-restp args)
                              (true-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))
                  :verify-guards nil))
  (cond
   ((endp args) (value-cmp alist))
   ((eq (car args) '&key)
    (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
   (t (er-cmp *macro-expansion-ctx*
              "Only keywords and values may follow &rest or &body; error in ~
               macro expansion of ~x0."
              form))))

(defun bind-macro-args-optional (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-optionalp args)
                              (true-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))
                  :verify-guards nil))
  (cond ((endp args)
         (cond ((null actuals)
                (value-cmp alist))
               (t (er-cmp *macro-expansion-ctx*
                          "Wrong number of args in macro expansion of ~x0."
                          form))))
        ((eq (car args) '&key)
         (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
        ((member (car args) '(&rest &body))
         (bind-macro-args-after-rest
          (cddr args) actuals
          (cons (cons (cadr args) actuals) alist)
          form wrld state-vars))
        ((symbolp (car args))
         (bind-macro-args-optional
          (cdr args) (cdr actuals)
          (cons (cons (car args) (car actuals))
                alist)
          form wrld state-vars))
        (t (let ((alist (cond ((equal (length (car args)) 3)
                               (cons (cons (caddr (car args))
                                           (not (null actuals)))
                                     alist))
                              (t alist))))
             (bind-macro-args-optional
              (cdr args) (cdr actuals)
              (cons (cons (car (car args))
                          (cond (actuals (car actuals))
                                ((>= (length (car args)) 2)
                                 (cadr (cadr (car args))))
                                (t nil)))
                    alist)
              form wrld state-vars)))))

(defun bind-macro-args1 (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist1p args)
                              (true-listp form)
                              (symbol-alistp alist)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))
                  :verify-guards nil))
  (cond ((endp args)
         (cond ((null actuals)
                (value-cmp alist))
               (t (er-cmp *macro-expansion-ctx*
                      "Wrong number of args in macro expansion of ~x0."
                      form))))
        ((member-eq (car args) '(&rest &body))
         (bind-macro-args-after-rest
          (cddr args) actuals
          (cons (cons (cadr args) actuals) alist)
          form wrld state-vars))
        ((eq (car args) '&optional)
         (bind-macro-args-optional (cdr args) actuals alist form wrld
                                   state-vars))
        ((eq (car args) '&key)
         (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
        ((null actuals)
         (er-cmp *macro-expansion-ctx*
             "Wrong number of args in macro expansion of ~x0."
             form))
        (t (bind-macro-args1 (cdr args) (cdr actuals)
                             (cons (cons (car args) (car actuals))
                                   alist)
                             form wrld state-vars))))

(defun bind-macro-args (args form wrld state-vars)
  (declare (xargs :guard (and (macro-args-structurep args)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))
                  :verify-guards nil))
  (cond ((and (consp args)
              (eq (car args) '&whole))
         (bind-macro-args1 (cddr args) (cdr form)
                           (list (cons (cadr args) form))
                           form wrld state-vars))
        (t (bind-macro-args1 args (cdr form) nil form wrld state-vars))))
