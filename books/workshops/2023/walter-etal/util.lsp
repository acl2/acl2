(load "package.lsp")

(in-package :util)
(ql:quickload :fare-quasiquote-readtable)

(deftype optional-number ()
  `(or number null))

(defmacro assoc-== (item alist)
  `(assoc ,item ,alist :test #'equal))

;; Replace to-replace with replace-with inside of x, recursively if x is a cons.
(defun replace-in (x to-replace replace-with)
  (if (equal x to-replace)
      replace-with
    (trivia:match x
                  ((type cons) (cons
                                (replace-in (car x) to-replace replace-with)
                                (replace-in (cdr x) to-replace replace-with)))
                  (otherwise x))))

(defun replace-in* (x replacements)
  (if (endp replacements)
      x
    (replace-in* (replace-in x (car (car replacements)) (cdr (car replacements)))
                 (cdr replacements))))

;; these two functions are adapted from Ben's startup.lisp for inv game
(declaim (ftype (function (list) string) concat-syms))
(defun concat-syms (syms)
  (if (endp syms)
      ""
    (concatenate 'string (symbol-name (car syms))
                 (concat-syms (cdr syms)))))

;; Concatenate all of the symbols in syms together, and then intern them in the given package
(declaim (ftype (function (t list) symbol) concat-syms-in-package))
(defun concat-syms-in-package (pkg syms)
  (intern (concat-syms syms) pkg))

(declaim (ftype (function (t symbol) symbol) intern-sym-in-package))
(defun intern-sym-in-package (pkg sym)
  (intern (symbol-name sym) pkg))

(declaim (ftype (function (string t) t) read-in-package))
(defun read-in-package (str pkg)
  (named-readtables:in-readtable :fare-quasiquote)
  (let* ((*package* (find-package pkg))
         (res (read-from-string str)))
    (named-readtables:in-readtable :standard)
    (replace-in* res '((fare-quasiquote::quote . common-lisp::quote)
                       (fare-quasiquote::list . common-lisp::list)))))

(defun append-all (l)
  (if (endp l)
      nil
    (append (car l) (append-all (cdr l)))))

;; https://raw.githubusercontent.com/spyrosoft/common-lisp-testing-grounds/c4ff87439b0a451edf0591a8d1e96adfa7b971a5/ansi-common-lisp/read-file-into-string.lisp
(defun read-file-into-string (file-path)
  (with-open-file (file-stream file-path)
                  (let ((file-contents (make-string (file-length file-stream))))
                    (read-sequence file-contents file-stream)
                    file-contents)))

(defun rem-dupes (xs)
  (remove-duplicates xs :test #'equal))

(defun has-duplicates? (l)
  (cond ((endp l) (values nil nil))
        ((member (car l) (cdr l) :test #'equal) (values t (car l)))
        (t (has-duplicates? (cdr l)))))

(defmacro errorp (form)
  `(typep ,form 'error))

(defvar *whitespaces* '(#\Space #\Newline #\Backspace #\Tab
                        #\Linefeed #\Page #\Return #\Rubout))

;; ============ From cl-str ============
(declaim (ftype (function (string) string) str-trim))
(defun str-trim (s)
  "Remove whitespaces at the beginning and end of s.
@begin[lang=lisp](code)
(trim \"  foo \") ;; => \"foo\"
@end(code)"
  (string-trim *whitespaces* s))

(declaim (ftype (function (&rest string) string) str-concat))
(defun str-concat (&rest strings)
  "Join all the string arguments into one string."
  (apply #'concatenate 'string strings))

(declaim (ftype (function (string string &key (:ignore-case boolean)) boolean) str-ends-with?))
(defun str-ends-with? (end s &key (ignore-case *ignore-case*))
  "Return t if s ends with the substring 'end', nil otherwise."
  (when (>= (length s) (length end))
    (let ((fn (if ignore-case #'string-equal #'string=)))
      (funcall fn s end :start1 (- (length s) (length end))))))
;; =====================================
