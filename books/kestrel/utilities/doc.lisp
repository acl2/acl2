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

;; Returns (mv required-args keyword-args)
(defun split-macro-args (macro-args)
  (if (endp macro-args)
      (mv nil nil)
      (if (eq '&key (first macro-args))
          (mv nil (rest macro-args))
        (mv-let (required-args keyword-args)
          (split-macro-args (rest macro-args))
          (mv (cons (first macro-args) required-args)
              keyword-args)))))

;; test: (SPLIT-MACRO-ARGS '(foo bar &key baz (baz2 'nil)))

(defun len-of-longest-macro-formal (macro-args longest)
  (if (endp macro-args)
      longest
    (let* ((arg (first macro-args))
           (len (if (symbolp arg)
                    (length (symbol-name arg))
                  (length (symbol-name (car arg))))))
      (len-of-longest-macro-formal (rest macro-args) (max longest len)))))

(defconst *xdoc-general-form-header* "<h3>General Form:</h3>")
(defconst *xdoc-inputs-header* "<h3>Inputs:</h3>")
(defconst *xdoc-description-header* "<h3>Description:</h3>")

;; Returns a string representing the given STRINGS within @({...}) to make then be printed as code.
(defun xdoc-within-code-fn (strings)
  (declare (xargs :guard (string-listp strings)))
  (string-append-lst (cons "@({"
                           (append strings
                                   (list "})")))))

;; Returns a string representing the given STRINGS within @({...}) to make then be printed as code.
(defmacro xdoc-within-code (&rest strings)
  `(xdoc-within-code-fn (list ,@strings)))

(defun maybe-skip-whole-arg (macro-args)
  (if (and (consp macro-args)
           (eq '&whole (first macro-args)))
      (cddr macro-args)
    macro-args))

;; Returns a string
(defund xdoc-for-macro-required-arg-general-form (macro-arg indent-space firstp)
  (declare (xargs :guard (and (macro-argp macro-arg)
                              (stringp indent-space)
                              (booleanp firstp))))
  (if (not (symbolp macro-arg))
      (prog2$ (er hard? 'xdoc-for-macro-required-arg-general-form "Required macro arg ~x0 is not a symbol." macro-arg)
              "")
    (n-string-append (if firstp "" indent-space)
                     (string-downcase-gen (symbol-name macro-arg))
                     (newline-string))))

;; Returns a string
(defun xdoc-for-macro-required-args-general-form (macro-args indent-space firstp)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (booleanp firstp))))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-required-arg-general-form (first macro-args) indent-space firstp)
                   (xdoc-for-macro-required-args-general-form (rest macro-args) indent-space nil))))

;; Returns a string
(defun xdoc-for-macro-keyword-arg-general-form (macro-arg indent-space firstp max-len package)
  (declare (xargs :guard (and (macro-argp macro-arg)
                              (stringp indent-space)
                              (booleanp firstp)
                              (natp max-len)
                              (stringp package))
                  :mode :program))
  (if (symbolp macro-arg)
      (let* ((name (string-downcase (symbol-name macro-arg)))
             (name (n-string-append ":" name)))
        ;;todo: think about this case (is nil the default)?
        (n-string-append (if firstp "" indent-space)
                         name
                         (newline-string)))
    ;; todo: check the form here:
    (let* ((name (first macro-arg))
           (name (string-downcase (symbol-name name)))
           (name (n-string-append ":" name))
           (default (if (< (len macro-arg) 2)
                        nil
                      ;;todo: ensure it's quoted?:
                      (unquote (second macro-arg))))  ;todo: sometimes a keyword arg has a third thing (suppliedp?)?
           (num-spaces-before-comment (+ 1 (- max-len (length name))))
           (space-before-comment (string-append-lst (make-list num-spaces-before-comment :initial-element " ")))
           )
      (n-string-append (if firstp "" indent-space)
                       name
                       space-before-comment "; default "
                       (string-downcase (object-to-string default package))
                       (newline-string)
                       ))))

;; Returns a string
(defun xdoc-for-macro-keyword-args-general-form (macro-args indent-space firstp max-len package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (booleanp firstp)
                              (natp max-len)
                              (stringp package))
                  :mode :program))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-keyword-arg-general-form (first macro-args) indent-space firstp max-len package)
                   (xdoc-for-macro-keyword-args-general-form (rest macro-args) indent-space nil max-len package))))


;; Returns a string
(defun xdoc-for-macro-args-general-form (macro-args indent-space package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (stringp indent-space)
                              (stringp package))
                  :mode :program))
  (b* ((macro-args (maybe-skip-whole-arg macro-args)) ;skip &whole
       ((mv required-args keyword-args) ;todo: handle optional args?  &rest? what else?
        (split-macro-args macro-args))
       (max-len (max (len-of-longest-macro-formal required-args 0)
                     (+ 1 (len-of-longest-macro-formal keyword-args 0))))) ;plus 1 for the :
    (n-string-append (xdoc-for-macro-required-args-general-form required-args indent-space t)
                     (if keyword-args
                         (n-string-append indent-space
                                          "&key"
                                          (newline-string))
                       "")
                     (xdoc-for-macro-keyword-args-general-form keyword-args indent-space (not required-args) max-len package))))


;; Returns a string
(defun xdoc-for-macro-general-form (name macro-args package)
  (declare (xargs :mode :program
                  :guard (and (symbolp name)
                              (stringp package))))
  (let* ((name-string (string-downcase (symbol-name name)))
         (name-len (length name-string))
         (indent-space (string-append-lst (make-list (+ 2 name-len) :initial-element " "))))
    (concatenate 'string
                 *xdoc-general-form-header*
                 (newline-string)
                 (newline-string)
                 (xdoc-within-code "(" name-string " "
                                   (xdoc-for-macro-args-general-form macro-args indent-space package)
                                   indent-space
                                   ")"))))

(defund skip-strings (items)
  (declare (xargs :guard t))
  (if (atom items)
      items
    (if (stringp (first items))
        (skip-strings (rest items))
      items)))

(defthm true-listp-of-skip-strings
  (equal (true-listp (skip-strings items))
         (true-listp items))
  :hints (("Goal" :in-theory (enable skip-strings))))

(defthm len-of-skip-strings-bound
  (<= (len (skip-strings items)) (len items))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable skip-strings))))

;; Recognize a list of symbols and strings, where there is first a symbol, then 0
;; or more strings, and then that pattern repeats.
(defun macro-arg-descriptionsp (arg-descriptions)
  (declare (xargs :guard t
                  :measure (len arg-descriptions)))
  (if (atom arg-descriptions)
      (null arg-descriptions)
    (and (symbolp (first arg-descriptions))
         (macro-arg-descriptionsp (skip-strings (rest arg-descriptions))))))

(defthm macro-arg-descriptionsp-forward-to-true-listp
  (implies (macro-arg-descriptionsp arg-descriptions)
           (true-listp arg-descriptions))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable macro-arg-descriptionsp))))


(defun strings-before-next-symbol (arg-descriptions)
  (declare (xargs :guard (true-listp arg-descriptions)))
  (if (endp arg-descriptions)
      nil
    (let ((item (first arg-descriptions)))
      (if (symbolp item)
          nil
        (if (stringp item)
            (cons item (strings-before-next-symbol (rest arg-descriptions)))
          (er hard? 'strings-before-next-symbol "Unexpected thing, ~x0, in macro input description." item))))))

(defthm strings-listp-of-strings-before-next-symbol
  (string-listp (strings-before-next-symbol arg-descriptions))
  :hints (("Goal" :in-theory (enable strings-before-next-symbol))))

;; Returns a list of strings
(defun get-description-strings (symbol arg-descriptions)
  (declare (xargs :guard (and (symbolp symbol)
                              (macro-arg-descriptionsp arg-descriptions))
                  :measure (len arg-descriptions)))
  (if (endp arg-descriptions)
      (er hard? 'get-description-strings "No description found for macro arg ~x0." symbol)
    (if (not (symbolp (first arg-descriptions)))
        (er hard? 'get-description-strings "Unexpected thing in input descriptions: ~x0 (expected a symbol)." (first arg-descriptions))
      (if (eq symbol (first arg-descriptions))
          (strings-before-next-symbol (rest arg-descriptions))
        (get-description-strings symbol (skip-strings (rest arg-descriptions)))))))

(defthm string-listp-of-get-description-strings
  (implies (and (symbolp symbol)
                (macro-arg-descriptionsp arg-descriptions))
           (string-listp (get-description-strings symbol arg-descriptions)))
  :hints (("Goal" :in-theory (enable get-description-strings))))

;; Returns a string
(defun xdoc-for-macro-required-input (macro-arg arg-descriptions)
  (declare (xargs :guard (and (symbolp macro-arg)
                              (macro-arg-descriptionsp arg-descriptions))))
  (if (not (symbolp macro-arg))
      (er hard 'xdoc-for-macro-required-input "Required macro arg ~x0 is not a symbol." macro-arg)
    (let ((name (string-downcase-gen (symbol-name macro-arg)))
          (description-strings (get-description-strings macro-arg arg-descriptions)))
      (n-string-append "<p>@('" name "')</p>" (newline-string)
                       (newline-string)
                       "<blockquote>" (newline-string)
                       (xdoc-make-paragraphs description-strings)
                       "</blockquote>" (newline-string)
                       (newline-string)))))

;; Returns a string
(defun xdoc-for-macro-required-inputs (macro-args arg-descriptions)
  (declare (xargs :guard (and (symbol-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions))))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-required-input (first macro-args) arg-descriptions)
                   (xdoc-for-macro-required-inputs (rest macro-args) arg-descriptions))))

;; Returns a string
(defun xdoc-for-macro-keyword-input (macro-arg arg-descriptions package)
  (declare (xargs :guard (and (stringp package)
                              (macro-arg-descriptionsp arg-descriptions)
                              (macro-argp macro-arg))
                  :mode :program))
  (let* ((name (if (symbolp macro-arg)  ;note that name will not be a keyword here
                   macro-arg
                 (first macro-arg)))
         (name-to-lookup (intern (symbol-name name) "KEYWORD")) ;since this is a keyword arg
         (description-strings (get-description-strings name-to-lookup arg-descriptions))
         (name (string-append ":" (string-downcase (symbol-name name))))
         (default (if (symbolp macro-arg)
                      nil
                    (if (< 2 (len macro-arg))
                        nil
                      ;;todo: ensure it's quoted?:
                      (unquote (second macro-arg)))))
         (default (string-downcase (object-to-string default package))))
    (n-string-append "<p>@('" name "')  &mdash; default @('" default "')</p>" (newline-string)
                     (newline-string)
                     "<blockquote>" (newline-string)
                     (xdoc-make-paragraphs description-strings)
                     "</blockquote>" (newline-string)
                     (newline-string))))

;; Returns a string
(defun xdoc-for-macro-keyword-inputs (macro-args arg-descriptions package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions)
                              (stringp package))
                  :mode :program))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-keyword-input (first macro-args) arg-descriptions package)
                   (xdoc-for-macro-keyword-inputs (rest macro-args) arg-descriptions package))))

;; Returns a string
(defun xdoc-for-macro-inputs (macro-args arg-descriptions package)
  (declare (xargs :guard (and (macro-arg-listp macro-args)
                              (macro-arg-descriptionsp arg-descriptions)
                              (stringp package))
                  :mode :program))
  (b* ((macro-args (maybe-skip-whole-arg macro-args)) ;skip &whole
       ((mv required-args keyword-args) ;todo: handle optional args?  &rest? what else?
        (split-macro-args macro-args)))
    (concatenate 'string
                 *xdoc-inputs-header*
                 (newline-string)
                 (newline-string)
                 (xdoc-for-macro-required-inputs required-args arg-descriptions)
                 (xdoc-for-macro-keyword-inputs keyword-args arg-descriptions package))))

;; Returns a defxdoc form.
(defund defxdoc-for-macro (name macro-args package parents short arg-descriptions description)
  (declare (xargs :guard (and (symbolp name)
                              (macro-arg-listp macro-args)
                              (stringp package)
                              (symbol-listp parents)
                              (or (stringp short)
                                  (null short))
                              (macro-arg-descriptionsp arg-descriptions)
                              ;; (or (stringp description) ;todo: gen?
                              ;;     (null description))
                              )
                  :mode :program))
  `(defxdoc ,name
     ,@(and short `(:short ,short))
     ,@(and parents `(:parents ,parents))
     :long (n-string-append
            ;; Document the general form (args and defaults):
            ,(xdoc-for-macro-general-form name macro-args package)
            ;;(newline-string)
            ;; Document each input (todo: call these "args"):
            ,(xdoc-for-macro-inputs macro-args arg-descriptions package)
            ;; Include the description section, if supplied:
            ,(if description
                 `(n-string-append (newline-string)
                                   (newline-string)
                                   *xdoc-description-header*
                                   (newline-string)
                                   (newline-string)
                                   ,description)
               ""))))

;; Returns a progn including the original defmacro and a defxdoc form
(defun defmacrodoc-fn (name macro-args rest)
  (declare (xargs :mode :program
                  :guard (symbolp name) ; todo: add more guard conjuncts
                  ))
  (b* (((mv declares rest) ;first come optional declares (no legacy doc strings)
        (get-declares rest))
       (body (first rest))      ;then the body
       (xdoc-stuff (rest rest)) ;then xdoc stuff, as keys alternating with values
       (parents (lookup-keyword :parents xdoc-stuff))
       (short (lookup-keyword :short xdoc-stuff))
       (description (lookup-keyword :description xdoc-stuff))
       (arg-descriptions (lookup-keyword :inputs xdoc-stuff)) ;; repetitions of the pattern: symbol followed by 1 or more strings describing it
       ((when (not short))
        (er hard 'defmacrodoc "No :short supplied for ~x0" name))
       ((when (and macro-args
                   (not arg-descriptions)))
        (er hard 'defmacrodoc "No :input supplied for ~x0" name))
       ;; The xdoc seems to be created in this package:
       (package (symbol-package-name name)))
    `(progn (defmacro ,name ,macro-args ,@declares ,body)
            ,(defxdoc-for-macro name macro-args package parents short arg-descriptions description))))

;; This is like defmacro, except it allows (after the macro's body), the
;; inclusion of :short and :parents (for generating xdoc) as well as the
;; special keyword options :inputs, which describes the inputs of the macro and
;; is used to generate xdoc, and :description, which describes what the macro
;; does and is included in the :long xdoc section.
(defmacro defmacrodoc (name macro-args &rest rest)
  ;; This previously used make-event to avoid a problem with calling FLPR in safe mode via fmt1-to-string.
  (defmacrodoc-fn name macro-args rest))

;; See tests in doc-tests.lisp.
