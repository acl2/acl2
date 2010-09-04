#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;;====================================================================
;;
;; The def::doc wrapper around defdoc.  We really need to understand
;; better how package names work with documentation.  It would also
;; be good to know how to generate .html files from documentation.
;;
;;====================================================================

(defmacro def::doc (name &key (section 'nil) (one-liner '"") (notes '"") (details 'nil))
  (let ((section (or (and section (if (symbolp section) (symbol-name section) section)) (symbol-name name)))
	(details (or details (symbol-name name))))
    (let ((doc `(concatenate 'string 

":Doc-Section " ,section "
"
,one-liner
"~/"
,notes
"~/"
,details
"
"

)))
      `(make-event
	`(DEFDOC ,',name ,,doc)))))


;;====================================================================
;;
;; Here are some functions for constructing fancy documentation.
;; Perhaps we shouldn just put documentation support into a separate
;; "doc" package.
;;
;;====================================================================

(defmacro docstring (&rest args)
  `(concatenate 'string ,@args))

(defun href (x)
  (concatenate 'string "~il[" x "]"))

(defun docref (x)
  (concatenate 'string "~l[" x "]"))

(defun \n () "~nl[]")

(defun verbatim (x)
  (concatenate 'string "~bv[]" x "~ev[]"))

(defun quoted (x)
  (concatenate 'string "~bq[]" x "~eq[]"))

;;====================================================================
;;
;; Here is an example of using "document" to document itself,
;; including the use of some fancy features.  Use :doc def::doc
;; to see how ACL2 renders the following documentation.
;;
;; We should probably document the fancy documentation strings, too.
;;
;;====================================================================

(def::doc def::doc
  
  :section def::doc
  
  :one-liner "A simple macro for easing the documentation process"
  
  :details (docstring
"

  The def::doc macro eases the process of constructing documentation
strings for ACL2 symbols. "(docref"doc")".  Macro keywords are used to
identify content for each of the primary documentation elements:

"(verbatim"
:section     Either a symbol or string identifying the section
:one-liner   A simple one-line overview of the symbol
:notes       Notes related to this symbol
:details     Documentation details about the symbol
")
(\n) ;; Note how this newline appears in the output of :doc ..
"
  The string arguments used by the macro can be computed, allowing the
user to use functions as abbreviations for common and unwieldly
documentation constructs.
"
))

