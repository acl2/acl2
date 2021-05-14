; Utilities for generating xdoc documentation
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "std/util/bstar" :dir :system)
(include-book "strings") ; for n-string-append and newline-string
(include-book "kestrel/utilities/keyword-value-lists2" :dir :system) ;for lookup-keyword

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

;; Returns a string representing the given STINGS within @({...}) to make then be printed as code.
(defun xdoc-within-code-fn (strings)
  (declare (xargs :guard (string-listp strings)))
  (string-append-lst (cons "@({"
                           (append strings
                                   (list "})")))))

;; Returns a string representing the given STINGS within @({...}) to make then be printed as code.
(defmacro xdoc-within-code (&rest strings)
  `(xdoc-within-code-fn (list ,@strings)))

(defun maybe-skip-whole-arg (macro-args)
  (if (and (consp macro-args)
           (eq '&whole (first macro-args)))
      (cddr macro-args)
    macro-args))

;; Returns a string
(defun xdoc-for-macro-required-arg-general-form (macro-arg indent-space firstp)
  (if (not (symbolp macro-arg))
      (er hard 'xdoc-for-macro-required-arg-general-form "Required macro arg ~x0 is not a symbol." macro-arg)
    (n-string-append (if firstp "" indent-space)
                     (string-downcase (symbol-name macro-arg))
                     (newline-string))))

;; Returns a string
(defun xdoc-for-macro-required-args-general-form (macro-args indent-space firstp)
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-required-arg-general-form (first macro-args) indent-space firstp)
                   (xdoc-for-macro-required-args-general-form (rest macro-args) indent-space nil))))

;; Returns a string
(defun xdoc-for-macro-keyword-arg-general-form (macro-arg indent-space firstp max-len package)
  (declare (xargs :mode :program
                  :guard (stringp package)))
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
  (declare (xargs :mode :program
                  :guard (stringp package)))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-keyword-arg-general-form (first macro-args) indent-space firstp max-len package)
                   (xdoc-for-macro-keyword-args-general-form (rest macro-args) indent-space nil max-len package))))


;; Returns a string
(defun xdoc-for-macro-args-general-form (macro-args indent-space package)
  (declare (xargs :mode :program
                  :guard (stringp package)))
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
                  :guard (stringp package)))
  (let* ((name (string-downcase (symbol-name name)))
         (name-len (length name))
         (indent-space (string-append-lst (make-list (+ 2 name-len) :initial-element " "))))
    (concatenate 'string
                 *xdoc-general-form-header*
                 (newline-string)
                 (newline-string)
                 (xdoc-within-code "(" name " "
                                   (xdoc-for-macro-args-general-form macro-args indent-space package)
                                   indent-space
                                   ")"))))

(defun strings-before-next-symbol (input-descriptions)
  (if (endp input-descriptions)
      nil
    (let ((item (first input-descriptions)))
      (if (symbolp item)
          nil
        (if (stringp item)
            (cons item (strings-before-next-symbol (rest input-descriptions)))
          (er hard 'strings-before-next-symbol "Unexpected thing, ~x0, in macro input description." item))))))

(defun skip-strings (items)
  (if (endp items)
      nil
    (if (stringp (first items))
        (skip-strings (rest items))
      items)))

(defun get-descrption-strings (symbol input-descriptions)
  (if (endp input-descriptions)
      (er hard 'get-descrption-strings "No description found for macro arg ~x0." symbol)
    (if (not (symbolp (first input-descriptions)))
        (er hard 'get-descrption-strings "Unexpected thing in input descriptions: ~x0 (expected a symbol)." (first input-descriptions))
      (if (eq symbol (first input-descriptions))
          (strings-before-next-symbol (rest input-descriptions))
        (get-descrption-strings symbol (skip-strings (rest input-descriptions)))))))

;;Returns a string
(defun xdoc-make-paragraphs (strings)
  (if (endp strings)
      ""
    (n-string-append "<p>" (first strings) "</p>" (newline-string)
                     (xdoc-make-paragraphs (rest strings)))))

;; Returns a string
(defun xdoc-for-macro-required-input (macro-arg input-descriptions)
  (if (not (symbolp macro-arg))
      (er hard 'xdoc-for-macro-required-input "Required macro arg ~x0 is not a symbol." macro-arg)
    (let ((name (string-downcase (symbol-name macro-arg)))
          (description-strings (get-descrption-strings macro-arg input-descriptions)))
      (n-string-append "<p>@('" name "')</p>" (newline-string)
                       (newline-string)
                       "<blockquote>" (newline-string)
                       (xdoc-make-paragraphs description-strings)
                       "</blockquote>" (newline-string)
                       (newline-string)))))

;; Returns a string
(defun xdoc-for-macro-required-inputs (macro-args input-descriptions)
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-required-input (first macro-args) input-descriptions)
                   (xdoc-for-macro-required-inputs (rest macro-args) input-descriptions))))

;; Returns a string
(defun xdoc-for-macro-keyword-input (macro-arg input-descriptions package)
  (declare (xargs :mode :program
                  :guard (stringp package)))
  (let* ((name (if (symbolp macro-arg)  ;note that name will not be a keyword here
                   macro-arg
                 (first macro-arg)))
         (name-to-lookup (intern (symbol-name name) "KEYWORD")) ;since this is a keyword arg
         (description-strings (get-descrption-strings name-to-lookup input-descriptions))
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
(defun xdoc-for-macro-keyword-inputs (macro-args input-descriptions package)
  (declare (xargs :mode :program
                  :guard (stringp package)))
  (if (endp macro-args)
      ""
    (string-append (xdoc-for-macro-keyword-input (first macro-args) input-descriptions package)
                   (xdoc-for-macro-keyword-inputs (rest macro-args) input-descriptions package))))

;; Returns a string
(defun xdoc-for-macro-inputs (macro-args input-descriptions package)
  (declare (xargs :mode :program
                  :guard (stringp package)))
  (b* ((macro-args (maybe-skip-whole-arg macro-args)) ;skip &whole
       ((mv required-args keyword-args) ;todo: handle optional args?  &rest? what else?
        (split-macro-args macro-args)))
    (concatenate 'string
                 *xdoc-inputs-header*
                 (newline-string)
                 (newline-string)
                 (xdoc-for-macro-required-inputs required-args input-descriptions)
                 (xdoc-for-macro-keyword-inputs keyword-args input-descriptions package))))

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
       (long (lookup-keyword :long xdoc-stuff))
       (input-descriptions (lookup-keyword :inputs xdoc-stuff)) ;; repetitions of the pattern: symbol followed by 1 or more strings describing it
       ((when (not short))
        (er hard 'defmacrodoc "No :short supplied for ~x0" name))
       ((when (and macro-args
                   (not input-descriptions)))
        (er hard 'defmacrodoc "No :input supplied for ~x0" name))
       ;; The xdoc seems to be created in this package:
       (package (symbol-package-name name)))
    `(progn (defmacro ,name ,macro-args ,@declares ,body)
            (defxdoc ,name
              ,@(and short `(:short ,short))
              ,@(and parents `(:parents ,parents))
              :long (n-string-append
                     ,(xdoc-for-macro-general-form name macro-args package)
                     ;;(newline-string)
                     ,(xdoc-for-macro-inputs macro-args input-descriptions package)
                     (newline-string)
                     (newline-string)
                     ,(if long
                          `(n-string-append *xdoc-description-header*
                                           (newline-string)
                                           (newline-string)
                                           ,long)
                        ""))))))

(defmacro defmacrodoc (name macro-args &rest rest)
  ;; This previously used make-event to avoid a problem with calling FLPR in safe mode via fmt1-to-string.
  (defmacrodoc-fn name macro-args rest))

;; See tests in doc-tests.lisp.
