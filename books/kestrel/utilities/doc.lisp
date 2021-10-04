; Utilities for generating xdoc documentation
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "std/util/bstar" :dir :system)
(include-book "macro-args")
(include-book "strings") ; for n-string-append and newline-string
(include-book "kestrel/utilities/keyword-value-lists2" :dir :system) ;for lookup-keyword
(include-book "kestrel/strings-light/downcase" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)

(local (in-theory (disable mv-nth)))

;; ;; Skips all strings at the front of the list ITEMS.
;; (defund skip-leading-strings (items)
;;   (declare (xargs :guard t))
;;   (if (atom items)
;;       items
;;     (if (stringp (first items))
;;         (skip-leading-strings (rest items))
;;       items)))

;; (defthm true-listp-of-skip-leading-strings
;;   (equal (true-listp (skip-leading-strings items))
;;          (true-listp items))
;;   :hints (("Goal" :in-theory (enable skip-leading-strings))))

;; (defthm len-of-skip-leading-strings-bound
;;   (<= (len (skip-leading-strings items)) (len items))
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable skip-leading-strings))))

;;Returns a string
(defun xdoc-make-paragraphs (strings)
  (declare (xargs :guard (string-listp strings)))
  (if (endp strings)
      ""
    (n-string-append "<p>" (first strings) "</p>" (newline-string)
                     (xdoc-make-paragraphs (rest strings)))))

(defun object-to-string (obj package)
  (declare (xargs :guard (stringp package)
                  :mode :program))
  (mv-let (col string)
    (fmt1-to-string "~x0" (acons #\0 obj nil) 0 :fmt-control-alist (acons 'acl2::current-package package nil))
    (declare (ignore col))
    string))

;; ;;Returns (mv keys-and-vals other-forms)
;; (defun get-keyword-value-pairs (forms)
;;   (if (endp forms)
;;       (mv nil nil)
;;     (if (keywordp (car forms))
;;         (if (not (consp (cdr forms)))
;;             (mv (er hard 'get-keyword-value-pairs "Missing value for key ~x0." (car forms))
;;                 nil)
;;           (mv-let (keys-and-vals other-forms)
;;             (get-keyword-value-pairs (rest (rest forms)))
;;             (mv (cons (car forms)
;;                       (cons (cadr forms)
;;                             keys-and-vals))
;;                 other-forms)))
;;       (mv nil forms))))

;; ;;test: (GET-KEYWORD-VALUE-PAIRS '(:foo 3 :bar 4 (declare x)))

;; ;;Returns (mv declares rest)
(defun get-declares (forms)
  (if (endp forms)
      (mv nil nil)
    (if (and (consp (car forms))
             (eq 'declare (caar forms)))
        (mv-let (declares rest)
          (get-declares (rest forms))
          (mv (cons (car forms)
                    declares)
              rest))
      (mv nil forms))))

(defun len-of-longest-macro-formal (macro-args longest)
  (if (endp macro-args)
      longest
    (let* ((arg (first macro-args))
           (len (if (symbolp arg)
                    (length (symbol-name arg))
                  (length (symbol-name (car arg))))))
      (len-of-longest-macro-formal (rest macro-args) (max longest len)))))

(defconst *xdoc-general-form-header* "<h3>General Form:</h3>")
(defconst *xdoc-general-form-header-with-spacing*
  (n-string-append *xdoc-general-form-header*
                   (newline-string)
                   (newline-string)))

;; todo: or call these Arguments?  But other xdoc uses "Inputs".
(defconst *xdoc-inputs-header* "<h3>Inputs:</h3>")
(defconst *xdoc-inputs-header-with-spacing*
  (n-string-append *xdoc-inputs-header*
                   (newline-string)
                   (newline-string)))

(defconst *xdoc-description-header* "<h3>Description:</h3>")
(defconst *xdoc-description-header-with-spacing*
  (n-string-append (newline-string)
                   (newline-string)
                   *xdoc-description-header*
                   (newline-string)
                   (newline-string)))

;; Returns a string representing the given STRINGS within @({...}) to make them be printed as code.
(defun xdoc-within-code-fn (strings)
  (declare (xargs :guard (string-listp strings)))
  (string-append-lst (cons "@({"
                           (append strings
                                   (list "})")))))

;; Returns a string representing the given STRINGS within @({...}) to make them be printed as code.
(defmacro xdoc-within-code (&rest strings)
  `(xdoc-within-code-fn (list ,@strings)))

;; Returns a string
(defund xdoc-for-macro-general-form-required-arg (macro-arg indent-space firstp)
  (declare (xargs :guard (and (macro-argp macro-arg)
                              (stringp indent-space)
                              (booleanp firstp))))
  (if (not (symbolp macro-arg))
      (prog2$ (er hard? 'xdoc-for-macro-general-form-required-arg "Required macro arg ~x0 is not a symbol." macro-arg)
              "")
    (n-string-append (if firstp "" indent-space)
                     (string-downcase-gen (symbol-name macro-arg))
                     (newline-string))))

;; Returns a string
(defun xdoc-for-macro-general-form-required-args (macro-args indent-space firstp)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (booleanp firstp))))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-general-form-required-arg (first macro-args) indent-space firstp)
                   (xdoc-for-macro-general-form-required-args (rest macro-args) indent-space nil))))

;; Returns a string
(defun xdoc-for-macro-general-form-optional-arg (macro-arg indent-space firstp max-len package)
  (declare (xargs :guard (and (macro-argp macro-arg)
                              (stringp indent-space)
                              (booleanp firstp)
                              (natp max-len)
                              (stringp package))
                  :mode :program ; because we call object-to-string
                  ))
  (mv-let (name default)
    (keyword-or-optional-arg-name-and-default macro-arg)
    (let* ((name (string-downcase (symbol-name name)))
           (name (n-string-append "[" name "]"))
           (num-spaces-before-comment (+ 1 (- max-len (length name))))
           (space-before-comment (string-append-lst (make-list num-spaces-before-comment :initial-element " "))))
      (n-string-append (if firstp "" indent-space)
                       name
                       space-before-comment
                       "; default "
                       (string-downcase (object-to-string default package))
                       (newline-string)))))

;; Returns a string
(defun xdoc-for-macro-general-form-optional-args (macro-args indent-space firstp max-len package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (booleanp firstp)
                              (natp max-len)
                              (stringp package))
                  :mode :program))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-general-form-optional-arg (first macro-args) indent-space firstp max-len package)
                   (xdoc-for-macro-general-form-optional-args (rest macro-args) indent-space nil max-len package))))

;; Returns a string
(defun xdoc-for-macro-general-form-keyword-arg (macro-arg indent-space firstp max-len package)
  (declare (xargs :guard (and (macro-argp macro-arg)
                              (stringp indent-space)
                              (booleanp firstp)
                              (natp max-len)
                              (stringp package))
                  :mode :program ; because we call object-to-string
                  ))
  (mv-let (name default)
    (keyword-or-optional-arg-name-and-default macro-arg)
    (let* ((name (string-downcase (symbol-name name)))
           (name (n-string-append ":" name))
           (num-spaces-before-comment (+ 1 (- max-len (length name))))
           (space-before-comment (string-append-lst (make-list num-spaces-before-comment :initial-element " "))))
      (n-string-append (if firstp "" indent-space)
                       name
                       space-before-comment
                       "; default "
                       (string-downcase (object-to-string default package))
                       (newline-string)))))

;; Returns a string
(defun xdoc-for-macro-general-form-keyword-args (macro-args indent-space firstp max-len package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (booleanp firstp)
                              (natp max-len)
                              (stringp package))
                  :mode :program))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-general-form-keyword-arg (first macro-args) indent-space firstp max-len package)
                   (xdoc-for-macro-general-form-keyword-args (rest macro-args) indent-space nil max-len package))))

;; Returns a string
;; TODO: Consider leaving in the &items here...
(defun xdoc-for-macro-general-form-args (macro-args indent-space package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (stringp package))
                  :mode :program))
  (b* (((mv required-args optional-args keyword-args)
        (extract-required-and-optional-and-keyword-args macro-args))
       (max-len (max (len-of-longest-macro-formal required-args 0)
                     (max (+ 1 (len-of-longest-macro-formal keyword-args 0)) ; plus 1 for the :
                          (+ 2 (len-of-longest-macro-formal keyword-args 0)) ; plus 2 for the []
                          ))))
    (n-string-append (xdoc-for-macro-general-form-required-args required-args indent-space t)
                     (if optional-args
                         (n-string-append indent-space
                                          "&optional"
                                          (newline-string))
                       "")
                     (xdoc-for-macro-general-form-optional-args optional-args indent-space (not required-args) max-len package)
                     (if keyword-args
                         (n-string-append indent-space
                                          "&key"
                                          (newline-string))
                       "")
                     (xdoc-for-macro-general-form-keyword-args keyword-args indent-space
                                                               (and (not required-args)
                                                                    (not optional-args))
                                                               max-len package))))

;; Returns a string
(defun xdoc-for-macro-general-form (name macro-args package)
  (declare (xargs :mode :program
                  :guard (and (symbolp name)
                              (stringp package))))
  (let* ((name-string (string-downcase (symbol-name name)))
         (name-len (length name-string))
         (indent-space (string-append-lst (make-list (+ 2 name-len) :initial-element " "))))
    (concatenate 'string
                 *xdoc-general-form-header-with-spacing*
                 (xdoc-within-code "(" name-string " "
                                   (xdoc-for-macro-general-form-args macro-args indent-space package)
                                   indent-space
                                   ")"))))

;; Recognize an alist from arg names to non-empty lists of strings (description paragraphs).
;; Example:
;; ((arg1 "string")
;;  (arg2 "stringa" "stringb"))
(defun macro-arg-descriptionsp (arg-descriptions)
  (declare (xargs :guard t
                  :measure (len arg-descriptions)))
  (if (atom arg-descriptions)
      (null arg-descriptions)
    (let ((item (first arg-descriptions)))
      (and (true-listp item)
           (<= 2 (len item)) ; must have an arg name and at least one string description
           (symbolp (first item))
           (string-listp (cdr item))
           (macro-arg-descriptionsp (rest arg-descriptions))))))

(defthm macro-arg-descriptionsp-forward-to-symbol-alistp
  (implies (macro-arg-descriptionsp arg-descriptions)
           (symbol-alistp arg-descriptions))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable macro-arg-descriptionsp))))

;; Returns a string
(defun xdoc-for-macro-required-arg (macro-arg arg-descriptions)
  (declare (xargs :guard (and (symbolp macro-arg)
                              (macro-arg-descriptionsp arg-descriptions))))
  (if (not (symbolp macro-arg))
      (er hard 'xdoc-for-macro-required-arg "Required macro arg ~x0 is not a symbol." macro-arg)
    (let ((name (string-downcase-gen (symbol-name macro-arg)))
          (description-strings (lookup-eq macro-arg arg-descriptions)))
      (n-string-append "<p>@('" name "') &mdash; (required)</p>" (newline-string)
                       (newline-string)
                       "<blockquote>" (newline-string)
                       (xdoc-make-paragraphs description-strings)
                       "</blockquote>" (newline-string)
                       (newline-string)))))

;; Returns a string
(defun xdoc-for-macro-required-args (macro-args arg-descriptions)
  (declare (xargs :guard (and (symbol-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions))))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-required-arg (first macro-args) arg-descriptions)
                   (xdoc-for-macro-required-args (rest macro-args) arg-descriptions))))

;; Returns a string
(defun xdoc-for-macro-optional-arg (macro-arg arg-descriptions package)
  (declare (xargs :guard (and (stringp package)
                              (macro-arg-descriptionsp arg-descriptions)
                              (macro-argp macro-arg))
                  :mode :program))
  (let* ((name (if (symbolp macro-arg)
                   macro-arg
                 (first macro-arg)))
         (name-to-lookup name)
         (description-strings (lookup-eq name-to-lookup arg-descriptions))
         ;; add the brackets, since this is an optional arg:
         (name (n-string-append "[" (string-downcase (symbol-name name)) "]"))
         (default (if (symbolp macro-arg)
                      nil
                    (if (< 2 (len macro-arg))
                        nil
                      ;;todo: ensure it's quoted?:
                      (unquote (second macro-arg)))))
         (default (string-downcase (object-to-string default package))))
    (n-string-append "<p>@('" name "') &mdash; default @('" default "')</p>" (newline-string)
                     (newline-string)
                     "<blockquote>" (newline-string)
                     (xdoc-make-paragraphs description-strings)
                     "</blockquote>" (newline-string)
                     (newline-string))))

;; Returns a string
(defun xdoc-for-macro-optional-args (macro-args arg-descriptions package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions)
                              (stringp package))
                  :mode :program))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-optional-arg (first macro-args) arg-descriptions package)
                   (xdoc-for-macro-optional-args (rest macro-args) arg-descriptions package))))

;; Returns a string
(defun xdoc-for-macro-keyword-arg (macro-arg arg-descriptions package)
  (declare (xargs :guard (and (stringp package)
                              (macro-arg-descriptionsp arg-descriptions)
                              (macro-argp macro-arg))
                  :mode :program))
  (let* ((name (if (symbolp macro-arg)  ;note that name will not be a keyword here
                   macro-arg
                 (first macro-arg)))
         (name-to-lookup name) ;(intern (symbol-name name) "KEYWORD") ;since this is a keyword arg
         (description-strings (lookup-eq name-to-lookup arg-descriptions))
         ;; add the colon, since this is a keyword arg:
         (name (string-append ":" (string-downcase (symbol-name name))))
         (default (if (symbolp macro-arg)
                      nil
                    (if (< 2 (len macro-arg))
                        nil
                      ;;todo: ensure it's quoted?:
                      (unquote (second macro-arg)))))
         (default (string-downcase (object-to-string default package))))
    (n-string-append "<p>@('" name "') &mdash; default @('" default "')</p>" (newline-string)
                     (newline-string)
                     "<blockquote>" (newline-string)
                     (xdoc-make-paragraphs description-strings)
                     "</blockquote>" (newline-string)
                     (newline-string))))

;; Returns a string
(defun xdoc-for-macro-keyword-args (macro-args arg-descriptions package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions)
                              (stringp package))
                  :mode :program))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-keyword-arg (first macro-args) arg-descriptions package)
                   (xdoc-for-macro-keyword-args (rest macro-args) arg-descriptions package))))

;; Returns a string
(defun xdoc-for-macro-args (macro-args arg-descriptions package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions)
                              (stringp package))
                  :mode :program))
  (b* (((mv required-args optional-args keyword-args) ;todo: handle optional args?
        (extract-required-and-optional-and-keyword-args macro-args)))
    (concatenate 'string
                 *xdoc-inputs-header-with-spacing*
                 (xdoc-for-macro-required-args required-args arg-descriptions)
                 (xdoc-for-macro-optional-args optional-args arg-descriptions package)
                 (xdoc-for-macro-keyword-args keyword-args arg-descriptions package))))

;; Returns a defxdoc form.
;; TODO: Check that there are no args in ARG-DESCRIPTIONS that are not among the MACRO-ARGS.
;; TODO: Think about all the & things that can occur in the macro-args
(defund defxdoc-for-macro-fn (name    ; the name of the macro being documented
                              macro-args ; the formals of the macro
                              parents
                              short ; a form that evaluates to a string or to nil
                              arg-descriptions ; todo: can we allow these to contain forms to be evaluated?
                              description ; either nil or a form that evaluates to a string
                              )
  (declare (xargs :guard (and (symbolp name)
                              (macro-arg-listp macro-args)
                              (symbol-listp parents)
                              (macro-arg-descriptionsp arg-descriptions))
                  :mode :program))
  (b* ((macro-arg-names (macro-arg-names macro-args))
       (described-arg-names (strip-cars arg-descriptions))
       ((when (not (subsetp-eq described-arg-names macro-arg-names)))
        (er hard? 'defxdoc-for-macro-fn "Descriptions given for arguments, ~x0, that are not among the macro args, ~x1."
            (set-difference-eq described-arg-names macro-arg-names)
            macro-args))
       ((when (not (subsetp-eq macro-arg-names described-arg-names)))
        (er hard? 'defxdoc-for-macro-fn "No descriptions given for macro arguments, ~x0."
            (set-difference-eq macro-arg-names described-arg-names)
            macro-args))
       ;; The xdoc seems to be created in this package:
       (package (symbol-package-name name)))
    `(defxdoc ,name
       ,@(and short `(:short ,short))
       ,@(and parents `(:parents ,parents))
       :long (n-string-append
              ;; Document the general form (args and defaults):
              ,(xdoc-for-macro-general-form name macro-args package)
              ;;(newline-string)
              ,(xdoc-for-macro-args macro-args arg-descriptions package)
              ;; Include the description section, if supplied:
              ,@(and description
                     (list *xdoc-description-header-with-spacing*
                           description))))))

(defmacro defxdoc-for-macro (name ; the name of the macro being documented
                             macro-args ; the formals of the macro, todo: allow extracting these from the world?
                             parents
                             short ; a form that evaluates to a string or to nil
                             arg-descriptions ; todo: can we allow these to contain forms to be evaluated?
                             description ; a form that evaluates to a string or to nil
                             )
  (defxdoc-for-macro-fn name macro-args parents short arg-descriptions description))

;; Returns a progn including the original defmacro and a defxdoc form
(defun defmacrodoc-fn (name macro-args rest)
  (declare (xargs :mode :program
                  :guard (symbolp name) ; todo: add more guard conjuncts
                  ))
  (b* (((mv declares rest) ;first come optional declares (no legacy doc strings)
        (get-declares rest))
       (body (first rest))      ;then the body
       (xdoc-stuff (rest rest)) ;then xdoc stuff, as keys alternating with values
       ((when (not (keyword-value-listp xdoc-stuff)))
        (er hard 'defmacrodoc "Ill-formed xdoc args (should be a keyword-value-list): ~x0" xdoc-stuff))
       (allowed-keys '(:parents :short :description :args))
       ((when (not (subsetp-eq (keyword-value-list-keys xdoc-stuff) allowed-keys)))
        (er hard 'defmacrodoc "Bad keys in ~x0 (allowed keys are ~x1)" xdoc-stuff allowed-keys))
       (parents (lookup-keyword :parents xdoc-stuff))
       (short (lookup-keyword :short xdoc-stuff))
       (description (lookup-keyword :description xdoc-stuff))
       (arg-descriptions (lookup-keyword :args xdoc-stuff)) ;; repetitions of the pattern: symbol followed by 1 or more strings describing it
       ((when (not short))
        (er hard 'defmacrodoc "No :short supplied for ~x0" name))
       ((when (and macro-args
                   (not arg-descriptions)))
        (er hard 'defmacrodoc "No :args supplied for ~x0 (should contain descriptions of the macro args)" name)))
    `(progn (defmacro ,name ,macro-args ,@declares ,body)
            ,(defxdoc-for-macro-fn name macro-args parents short arg-descriptions description))))

;; This is like defmacro, except it allows (after the macro's body), the
;; inclusion of :short and :parents (for generating xdoc) as well as the
;; special keyword options :args, which describes the arguments of the macro and
;; is used to generate xdoc, and :description, which describes what the macro
;; does and is included in the :long xdoc section.
(defmacro defmacrodoc (name macro-args &rest rest)
  ;; This previously used make-event to avoid a problem with calling FLPR in safe mode via fmt1-to-string.
  (defmacrodoc-fn name macro-args rest))

;; See tests in doc-tests.lisp.
