;; 2023
;; Author: Stephen Westfold

;; Works with acl2-mode, but not essential
;; (require 'acl2-mode)

;; Always use spaces for indentation
(setq indent-tabs-mode nil)

;; If using electric indent mode, indent in strings
(defun electric-indent-in-string (ch)
  (and (equal ch ?\C-j)
       (nth 8 (syntax-ppss))            ; in string
       'do-indent))

(add-hook 'electric-indent-functions 'electric-indent-in-string)

(defcustom indent-first-function-arg 1
  "Amount to indent first argument of a function relative to function"
  :type 'integer
  :group 'customize)
;; This gives indentation like:
;;   (pseudo-termp
;;     (list* x1 ...
;; To get the previous default behavior set this to 0:
;;   (pseudo-termp
;;    (list* x1 ...

(defun toggle-indent-first-function-arg (arg)
  (interactive "P")
  (setq indent-first-function-arg
        (or arg
            (if (equal indent-first-function-arg 0)
                1
              0))))
(defcustom indent-close-paren-to-open nil
  "Indent line beginning with close paren to position of matching open paren"
  :type 'boolean
  :group 'customize)
;; This give indentation like:
;;   (let ((x y))
;;      (foo x)
;;      ;; (old-foo x)
;;      )
;; Setting this to T gives:
;;   (let ((x y))
;;      (foo x)
;;      ;; (old-foo x)
;;      )

(defun toggle-indent-close-paren-to-open ()
  (interactive)
  (setq indent-close-paren-to-open (not indent-close-paren-to-open)))

;; This is mainly relevant for :hints
(defcustom indent-string-headed-list t
  "Controls indentation in list with string head. T: Indent to first element; NIL: no indent"
  :type 'boolean
  :group 'customize)
;; This is mainly for :hints
;; This default gives 
;;  :hints ((“Goal” :use (:instance foo)
;;                  :in-theory (disable foo)))
;; Setting it to NIL gives
;;  :hints ((“Goal” :use (:instance foo)
;;           :in-theory (disable foo)))

(defun toggle-indent-string-headed-list (arg)
  (interactive "P")
  (setq indent-string-headed-list
        (or arg
            (not indent-string-headed-list))))

(defcustom indent-def-beginning-functions-like-defun t
  "Functions that begin with def are indented like defuns by default."
  :type 'boolean
  :group 'customize)

(defun toggle-indent-def-beginning-functions-like-defun ()
  (interactive)
  (setq indent-def-beginning-functions-like-defun (not indent-def-beginning-functions-like-defun)))

(defcustom specform-distinguished-args-indent 2
  "Minimum extra amount to indent distinguished (initial) arguments of specforms"
  :type 'integer
  :group 'customize)

;; Not sure if this is necessary
(defcustom indent-def-column-limit 40
  "If function name begins with def and occurs in lesser column, indent like a defun"
  :type 'integer
  :group 'customize)

;; Set by calculate-lisp-indent
(defvar calculate-lisp-indent-last-sexp)

(defun strip-package (identifier)
  (let ((pkg-found (string-match ":+" identifier)))
    (and pkg-found
         (not (equal (match-end 0) (length identifier)))
         (substring identifier (match-end 0)))))

;; Tries to determine that..
(defun list-not-a-functionp (state)
  (let* ((containing-open-paren-posns (elt state 9))
         (containing-paren-pos (and (consp containing-open-paren-posns)
                                    (car (last containing-open-paren-posns 2))))
         ;; (beginning-line-pos (save-excursion (beginning-of-line)
         ;;                                     (point)))
         )
    (or (and containing-paren-pos
             ;(>= containing-paren-pos beginning-line-pos)
             (save-excursion (goto-char containing-paren-pos)
                             (looking-at "\\((defun\\|(define\\|(e/d\\)"))))))

;; Modified from lisp-indent-specform
(defun acl2-indent-specform (count state indent-point normal-indent)
  (let ((containing-form-start (elt state 1))
        (i count)
        body-indent containing-form-column)
    ;; Move to the start of containing form, calculate indentation
    ;; to use for body forms (> count), and move past the
    ;; function symbol.  lisp-indent-function guarantees that there is at
    ;; least one word or symbol character following open paren of containing
    ;; form.
    (goto-char containing-form-start)
    (setq containing-form-column (current-column))
    (setq body-indent (+ lisp-body-indent containing-form-column))
    (forward-char 1)
    (forward-sexp 1)
    ;; Now find the start of the last form.
    (parse-partial-sexp (point) indent-point 1 t)
    (while (and (< (point) indent-point)
                (condition-case ()
                    (progn
                      (setq count (1- count))
                      (forward-sexp 1)
                      (parse-partial-sexp (point) indent-point 1 t))
                  (error nil))))
    ;; Point is sitting on first character of last (or count) sexp.
    (if (> count 0)
        (list (max normal-indent
                   (+ body-indent specform-distinguished-args-indent))
              containing-form-start)
      ;; A body form.  Use body-indent if there are no
      ;; distinguished forms and this is the first undistinguished form,
      ;; or if this is the first undistinguished form and the preceding
      ;; distinguished form has indentation at least as great as body-indent.
      (if (or (and (= i 0) (<= count 0))
              (and (<= count 0) (<= body-indent normal-indent)))
          body-indent
        normal-indent))))

;; Modified for list beginning with a keyword
;; This could easily replace the standard version in acl2-mode.el
(defun acl2-indent-function (indent-point state)
  (let ((normal-indent (current-column)))
    (goto-char (1+ (elt state 1)))
    (parse-partial-sexp (point) calculate-lisp-indent-last-sexp 0 t)
    (if (looking-at "\\s<")
        normal-indent
      (if (and (elt state 2)
               (not (or (looking-at "\\sw\\|\\s_\\||")
                        (and indent-string-headed-list
                             (looking-at "\"")))))
          ;; car of form doesn't seem to be a symbol or string
          (progn
            (if (not (> (save-excursion (forward-line 1) (point))
                        calculate-lisp-indent-last-sexp))
                (progn (goto-char calculate-lisp-indent-last-sexp)
                       (beginning-of-line)
                       (parse-partial-sexp (point) calculate-lisp-indent-last-sexp 0 t)))
            ;; Indent under the list or under the first sexp on the same
            ;; line as calculate-lisp-indent-last-sexp.  Note that first 
            ;; thing on that line has to be complete sexp since we are
            ;; inside the innermost containing sexp.
            (backward-prefix-chars)
            (current-column))
        (let* ((car-indent (current-column))
               (function (buffer-substring (point)
					   (progn (forward-sexp 1) (point))))
               (function (or (and (> (length function) 0)
                                  (not (equal (elt function 0) ?:))
                                  ;; Ignore package unless begins with "def"
                                  (not (string-match "\\`def" function))
                                  (strip-package function))
                             function))
               (function-sym (intern-soft function))
	       method)
	  (setq method (or (get function-sym 'acl2-indent-hook)
			   (get function-sym 'lisp-indent-function)
			   ;; sjw: Not sure that 'lisp-indent-hook is a thing
			   (get function-sym 'lisp-indent-hook)
                           (let ((lcase-function-sym (intern-soft (downcase function))))
                             (or (get lcase-function-sym 'acl2-indent-hook)
                                 (get lcase-function-sym 'lisp-indent-function)))))
	  (cond ((or (eq method 'defun)
		     (and (null method)
                          indent-def-beginning-functions-like-defun
			  indent-def-column-limit                 ; helpful?
                          (< car-indent indent-def-column-limit)
			  (string-match "\\`def" function)))
	         (lisp-indent-defform state indent-point))
	        ((integerp method)
	         (acl2-indent-specform method state
				       indent-point normal-indent))
	        (method
		 (funcall method indent-point state))
                ((and (> (length function)
                         0)
                      (or (equal (elt function 0) ?:)     ; list begins with a keyword
                          (save-excursion (goto-char (- (elt state 1) 1))
                                          (looking-at "'("))       ; List of items
                          ))
                 (save-excursion (goto-char (1+ (elt state 1))) (current-column)))
                ((> (save-excursion (forward-line 1) (point))
                    (elt state 2))      ; The line after (elt state 2)
                 (cond ((or (= (+ 1 (elt state 1)) (elt state 2))
                            ;; Special case where item is something like foo::|fie|
                            (save-excursion (goto-char (elt state 1))
                                            (forward-char 1)
                                            (forward-sexp 1)
                                            (and (eq (char-after) ?\|)
                                                 (= (point) (elt state 2)))))
                        (if (list-not-a-functionp state)
                            car-indent
                          ;; First argument of ordinary function on a new line
                          (+ car-indent indent-first-function-arg)))
                       ((save-excursion (goto-char (elt state 1))
                                        (forward-char 1)
                                        (forward-sexp 1)
                                        (eq (char-after) ?\|))
                        ;;  Special case where (elt state 1) is something like (foo::|fie| x
                        (forward-sexp 1)
                        (skip-chars-forward " \t")
                        (current-column))))))))))

(defun preceding-double-quote-column (pos)
  (save-excursion
    (goto-char pos)
    (and (re-search-backward "[^\\]\"" nil t)
         (+ 2 (current-column)))))

(defun indentation-from-previous-line-comment ()
  (save-excursion
    (forward-line -1)
    (and (re-search-forward "\\s<"
                            (save-excursion (end-of-line 1))
                            t)
         (progn (backward-char)
                (looking-at ";[^;]"))
         (current-column))))

;; lisp-ppss is not in Emacs 24
(defvar *old-emacs* (not (fboundp 'lisp-ppss)))

(require 'cl-macs)

(when *old-emacs*            ; Old emacs: try to define necessary new fns
  (defun lisp-ppss (&optional pos)
    "Return Parse-Partial-Sexp State at POS, defaulting to point.
     Like `syntax-ppss' but includes the character address of the last
     complete sexp in the innermost containing list at position
     2 (counting from 0).  This is important for Lisp indentation."
  (unless pos (setq pos (point)))
  (let ((pss (syntax-ppss pos)))
    (if (nth 9 pss)
        (let ((sexp-start (car (last (nth 9 pss)))))
          (parse-partial-sexp sexp-start pos nil nil (syntax-ppss sexp-start)))
      pss)))

  (cl-defstruct (lisp-indent-state
                  (:constructor nil)
                  (:constructor lisp-indent-initial-state
                   (&aux (ppss (lisp-ppss))
                         (ppss-point (point))
                         (stack (make-list (1+ (car ppss)) nil)))))
    stack ;; Cached indentation, per depth.
    ppss
    ppss-point)

  (defun lisp-indent-calc-next (state)
    "Move to next line and return calculated indent for it.
STATE is updated by side effect, the first state should be
created by `lisp-indent-initial-state'.  This function may move
by more than one line to cross a string literal."
    (let* ((indent-stack (lisp-indent-state-stack state))
           (ppss (lisp-indent-state-ppss state))
           (ppss-point (lisp-indent-state-ppss-point state))
           (indent-depth (car ppss))    ; Corresponding to indent-stack.
           (depth indent-depth))
      ;; Parse this line so we can learn the state to indent the
      ;; next line.
      (while (let ((last-sexp (nth 2 ppss)))
               (setq ppss (parse-partial-sexp
                            ppss-point (progn (end-of-line) (point))
                            nil nil ppss))
               ;; Preserve last sexp of state (position 2) for
               ;; `calculate-lisp-indent', if we're at the same depth.
               (if (and (not (nth 2 ppss)) (= depth (car ppss)))
                   (setf (nth 2 ppss) last-sexp)
                 (setq last-sexp (nth 2 ppss)))
               (setq depth (car ppss))
               ;; Skip over newlines within strings.
               (and (not (eobp)) (nth 3 ppss)))
        (let ((string-start (nth 8 ppss)))
          (setq ppss (parse-partial-sexp (point) (point-max)
                                         nil nil ppss 'syntax-table))
          (setf (nth 2 ppss) string-start) ; Finished a complete string.
          (setq depth (car ppss)))
        (setq ppss-point (point)))
      (setq ppss-point (point))
      (let* ((depth-delta (- depth indent-depth)))
        (cond ((< depth-delta 0)
               (setq indent-stack (nthcdr (- depth-delta) indent-stack)))
              ((> depth-delta 0)
               (setq indent-stack (nconc (make-list depth-delta nil)
                                         indent-stack)))))
      (prog1
          (let (indent)
            (cond ((= (forward-line 1) 1)
                   ;; Can't move to the next line, apparently end of buffer.
                   nil)
                  ((null indent-stack)
                   ;; Negative depth, probably some kind of syntax
                   ;; error.  Reset the state.
                   (setq ppss (parse-partial-sexp (point) (point))))
                  ((car indent-stack))
                  ((integerp (setq indent (calculate-lisp-indent (elt ppss 1))))
                   (setf (car indent-stack) indent))
                  ((consp indent)       ; (COLUMN CONTAINING-SEXP-START)
                   (car indent))
                  ;; This only happens if we're in a string, but the
                  ;; loop should always skip over strings (unless we hit
                  ;; end of buffer, which is taken care of by the first
                  ;; clause).
                  (t (error "This shouldn't happen"))))
        (setf (lisp-indent-state-stack state) indent-stack)
        (setf (lisp-indent-state-ppss-point state) ppss-point)
        (setf (lisp-indent-state-ppss state) ppss))))
  )

(defun acl2-indent-line (&optional indent)
  "Indent current line as Lisp code."
  (interactive)
  (let* ((pos (- (point-max) (point)))
         (from-end-of-line (eolp))
         (pps-state (progn (beginning-of-line)
                           (syntax-ppss)))
         (indent (progn (skip-chars-forward " \t")
                        (or (and (nth 8 pps-state)
                                 (preceding-double-quote-column (line-beginning-position)))
                            (and from-end-of-line
                                 indent-close-paren-to-open
                                 (looking-at ")") ; Line up close paren at beginning of line with matching open
                                 (save-excursion (goto-char (elt pps-state 1)) (current-column)))
                            indent
                            (calculate-lisp-indent (if *old-emacs*
                                                       (car (elt (lisp-ppss) 9))
                                                     (lisp-ppss)))))))
    (if (or (null indent)
            (looking-at "\\s<\\s<\\s<")
            (integerp (nth 4 pps-state)))
	;; Don't alter indentation of a ;;; comment line
	;; or a line that starts in a string.
        ;; FIXME: inconsistency: comment-indent moves ;;; to column 0.
	(goto-char (- (point-max) pos))
      (if (looking-at ";[^;(]")
          (indent-line-to (or (indentation-from-previous-line-comment)
                              0))
        (if (listp indent) (setq indent (car indent)))
        (indent-line-to indent)
        ;; If initial point was within line's indentation,
        ;; position after the indentation.  Else stay at same point in text.
        (if (> (- (point-max) pos) (point))
	    (goto-char (- (point-max) pos)))))))

(defun acl2-indent-region (start end)
  "Indent region as Acl2 code, efficiently."
  (save-excursion
    (setq end (copy-marker end))
    (goto-char start)
    (beginning-of-line)
    ;; The default `indent-region-line-by-line' doesn't hold a running
    ;; parse state, which forces each indent call to reparse from the
    ;; beginning.  That has O(n^2) complexity.
    (let* ((parse-state (lisp-indent-initial-state))
           (pr (unless (minibufferp)
                 (make-progress-reporter "Indenting region..." (point) end))))
      (let ((ppss (lisp-indent-state-ppss parse-state)))
        (unless (or (and (bolp) (eolp)) (nth 3 ppss))
          (acl2-indent-line (calculate-lisp-indent (if *old-emacs* (car (elt ppss 9)) ppss)))))
      (let ((indent nil))
        (while (progn (setq indent (lisp-indent-calc-next parse-state))
                      (< (point) end))
          (unless (or (and (bolp) (eolp)) (not indent))
            (skip-chars-forward " \t")
            (acl2-indent-line (if (eolp)
                                  0     ; Remove whitespace if nothing else
                                (or (and indent-close-paren-to-open
                                         (looking-at ")") ; Line up close paren at beginning of line with matching open
                                         (save-excursion (goto-char (elt (progn (beginning-of-line)
                                                                                (syntax-ppss)) 1))
                                                         (current-column)))
                                    indent))))
          (and pr (progress-reporter-update pr (point)))))
      (and pr (progress-reporter-done pr))
      (move-marker end nil))))

(defun indent-region-including-strings ()
  (interactive)
  (indent-region-line-by-line (region-beginning) (region-end)))

;; Simpler than version from lisp-mode.el and more consistent with TAB
(defun indent-sexp (&optional arg)
  (interactive "P")
  (mark-sexp arg)
  (indent-region (point) (mark)))

(if (boundp 'acl2-mode-map) 
    (define-key acl2-mode-map [C-tab] 'indent-region-including-strings)
  (if (boundp 'lisp-mode-map)
      (define-key lisp-mode-map [C-tab] 'indent-region-including-strings)))

(defun use-acl2-lisp-indent ()
  (interactive)
  (setq indent-line-function 'acl2-indent-line)
  (setq indent-region-function 'acl2-indent-region)
  (setq lisp-indent-function 'acl2-indent-function))

(add-hook 'acl2-mode-hook 'use-acl2-lisp-indent)
(add-hook 'lisp-mode-hook 'use-acl2-lisp-indent)

(defun normal-function (indent-point state)
  (if (looking-at " ")
      (forward-char 1)
    (goto-char (+ 1 indent-first-function-arg (elt state 1)))
    (current-column)))

;; Common lisp
(put 'defun 'acl2-indent-hook 'defun)
(put 'flet 'acl2-indent-hook 1)
(put 'let* 'acl2-indent-hook 1)
(put 'the 'acl2-indent-hook 1)
(put 'case 'acl2-indent-hook 'defun)

;; ACL2
(put 'encapsulate 'acl2-indent-hook 1)
(put 'defstobj 'acl2-indent-hook 1)
(put 'b* 'acl2-indent-hook 1)
(put 'case-match   'acl2-indent-hook 'defun)
(put 'mv-let       'acl2-indent-hook 2) ; Prefer to 'defun
;; This indents like
;; (mv-let (x y)
;;         (fie y)
;;   (+ x y))
;; You can do (put 'mv-let 'acl2-indent-hook 1) to get
;; (mv-let (x y)
;;   (fie y)
;;   (+ x y))

(put 'verify-guards 'acl2-indent-hook 1)

;; Possible additions
;(put 'er-soft+ 'acl2-indent-hook 3)
;(put 'er-soft 'acl2-indent-hook 3)

;; Only necessary if indent-def-beginning-functions-like-defun is nil
(put 'defthm 'acl2-indent-hook 1)
(put 'defthmd 'acl2-indent-hook 1)
(put 'defthm-std 'acl2-indent-hook 1)
(put 'defaxiom 'acl2-indent-hook 1)
(put 'deftheory 'acl2-indent-hook 'defun)
(put 'defstobj 'acl2-indent-hook 1)
(put 'defun 'acl2-indent-hook 'defun)
(put 'defrec 'acl2-indent-hook 1)
(put 'defparameter 'acl2-indent-hook 1)
(put 'defvar 'acl2-indent-hook 1)
(put 'defconstant 'acl2-indent-hook 1)
(put 'defun$ 'acl2-indent-hook 'defun)
(put 'defpkg 'acl2-indent-hook 1)

(put 'defund 'acl2-indent-hook 'defun)
(put 'defvar 'acl2-indent-hook 1)
(put 'defxdoc 'acl2-indent-hook 1)
(put 'defxdoc+ 'acl2-indent-hook 1)
(put 'defconst 'acl2-indent-hook 1)
(put 'defprojection 'acl2-indent-hook 'defun)
(put 'deflist 'acl2-indent-hook 'defun)
(put 'defaggregate 'acl2-indent-hook 1)
(put 'defchoose 'acl2-indent-hook 2)
(put 'defsum 'acl2-indent-hook 1)
(put 'definj 'acl2-indent-hook 1)
(put 'defun-sk 'acl2-indent-hook 'defun)
(put 'defund-sk 'acl2-indent-hook 'defun)
(put 'defmapping 'acl2-indent-hook 1)
(put 'defiso 'acl2-indent-hook 5)
(put 'defsurj 'acl2-indent-hook 1)
(put 'defisar 'acl2-indent-hook 1)
(put 'defubytelist 'acl2-indent-hook 1)
(put 'defsubtype 'acl2-indent-hook 1)
(put 'defresult 'acl2-indent-hook 1)
(put 'defset 'acl2-indent-hook 1)
(put 'defoset 'acl2-indent-hook 1)
(put 'defbyte 'acl2-indent-hook 1)
;; incomplete

;; :hints
(put ':instance 'acl2-indent-hook 'normal-function)
(put ':functional-instance 'acl2-indent-hook 'normal-function)
(put ':termination-theorem 'acl2-indent-hook 'normal-function)

(put ':free 'acl2-indent-hook 'normal-function)
(put ':with 'acl2-indent-hook 'normal-function)
(put ':do-all 'acl2-indent-hook 'normal-function)
(put ':s 'acl2-indent-hook 'normal-function)
(put ':then 'acl2-indent-hook 'normal-function)
(put ':orelse 'acl2-indent-hook 'normal-function)

(put ':rewrite 'acl2-indent-hook 'normal-function)

;; APT
(put 'propagate-iso 'acl2-indent-hook 1)
(put 'simplify 'acl2-indent-hook 'defun)

(put 'generate-extensions2 'common-lisp-indent-function '(nil &body))

;; elisp
(put 'define-skeleton 'acl2-indent-hook 3)
(put 'define-abbrev-table 'acl2-indent-hook 1)

;; Kestrel APT Spec package
(put 'axiom 'acl2-indent-hook 'defun)
(put 'op 'acl2-indent-hook 'defun)
(put 'theorem 'acl2-indent-hook 'defun)
(put 'spec 'acl2-indent-hook 'defun)

;; (get 'IF 'acl2-indent-hook)
;; (get 'if 'lisp-indent-function)

(provide 'acl2-indent)
