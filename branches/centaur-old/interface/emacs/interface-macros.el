;; Macros to uniformly define emacs interface commands.
;; Specifically:

;;  1. Set the menu-bar.
;;  2. Set up a pop-up menu on mouse-3.
;;  3. Set other random key definitions.
;;
;; Originally designed for Acl2.
;; For versions of Emacs post 19 running under X.

(require 'thingatpt)			; (load "thingatpt")	
(require 'mouse)			; (load "mouse")

(provide 'interface-macros)

(defvar mode-menu-alist nil)
(defvar menu-bar-prefix "menu-bar-%s")

(defvar interface-wrapper "%s")
(defvar interface-to-top '(this-line-to-top))

;; Default form for evaluating a generated command. 
;; <command> is replaced by the command string in the menu, and
;; <arg> by the value of the computed argument (or nil) depending on
;; the arg description in the menu.
;; Example: '(inf-acl2-send-string <command> <arg>)

(defvar menu-arg-functions nil)
(defvar interface-menu-function nil)

;; The following two alists allow you to override the defaults 
;; above in the case of particular argument types.
;; Should be list of form ((argtype . expr)), where expr
;; may contain <command> and <arg>  which get replaced as for the
;; above.
(defvar popup-arg-functions nil)
(defvar interface-popup-function nil)

;; The mouse gesture that popup menus are hung off.  I think
;; it is important that this be a DOWN command.

(defvar down-mouse [down-mouse-3])


;; Interface definition form:

;; (define-interface mode mode-map menu-bar menu-bar-remove popup-menu keys)

;; Before the menu-bar, popup-menu or keys are defined we check
;; MODE-MENU-ALIST to see if the map named mode-map requests that functionality.

;; WARNING:  Be sure that if should-i-install, update-mode-menu-alist,
;; remove-mode-menu-alist, define-mode-keys, or extend-hook is changed, then it
;; is also changed in key-interface.el.

(defun should-i-install (mode feature)
  ;; mode is mode-name
  (memq feature (cdr (assoc mode mode-menu-alist))))

(defun update-mode-menu-alist (l)
  (if (not (consp (car l)))
      (setq l (cons l nil)))
  (setq mode-menu-alist 
	(append l (remove-mode-menu-alist mode-menu-alist l))))

(defun remove-mode-menu-alist (alist l)
  (cond ((null alist) l)
	((assoc (car (car alist)) l)
	 (remove-mode-menu-alist (cdr alist) l))
	(t (cons (car alist) (remove-mode-menu-alist (cdr alist) l)))))

;; ----------------------------------------------------------------------
;; MENU
;;
;; menu      ::= (command*)
;; command   ::=    (:entry label string . keywords)
;;               || (:entry label symbol . keywords) ; (fboundp symbol)
;;               || (:keymap label symbol) ; (keymapp (eval symbol))
;;               || (:menu label . menu)
;;               || (:label string)
;; keywords  ::= ([:arg arg] [:to-top] [:unwrapped] :pre :post)
;; arg       ::= symbol || integer || string || sexp ||  click

;; arg may be extended. For example acl2-interface-functions adds event,
;; cd, and command.  The last two stand for command-descriptors.

;; Commands: generate entries in the menu. 
;;  :entry label string : Causes string (wrapped) to be sent to process.
;;  :entry label symbol : Invokes function named symbol.
;;  :menu label . menu  : Recurs on menu defined by menu.
;;  :label string       : Just puts string in menu, for example as documentation
;;                        or to provide a blank line (:label "").
;; Keywords:
;;  a. :TO-TOP instructs the interface to put the current point at the top of
;;     the buffer before executing the command.  Default is to do nothing.
;;  b. Normally the strings in entries are inserted into a "wrapper", the value
;;     of INTERFACE-WRAPPER.  :UNWRAPPED instructs the interface to skip this step.
;;  c. :arg indicates that an argument of the indicated type must
;;     be supplied.
;;  d. :pre indicates an emacs form to be evaled before anything else.
;;  e. :post indicates an emacs form to be evaled after everything else.

(defmacro when (test &rest body) (cons 'if (cons test (list (cons 'progn body)))))

(defun extend-menu-bar (map-name key menu &optional function-prefix)
  "MAP-NAME is keymap name. KEY is a key vector, typically 
\[menu-bar\].  TREE is menu-tree."
  (if (null function-prefix) (setq function-prefix menu-bar-prefix))
  (cond ((not (keymapp (eval map-name))) (error (format "%s is not a keymap name." map-name)))
	((should-i-install map-name 'menu-bar)
	 (let ((map (eval map-name)))
	   (or (lookup-key map key)
               (define-key map key (make-sparse-keymap)))
           (define-menus map key menu function-prefix)))))

(defun define-menus (map key menu prefix)
  ;; key is a vector, e.g. [menu-bar].
  ;; It is the key in map that menu is supposed to hang off.
  ;; So that menus will come out looking like the user typed them in
  ;; we reverse the menu list first.
  (setq menu (reverse menu))
  (while menu
    (let ((entry (car menu)))
      (cond ((not (consp entry)) (error "Ill formed menu-tree")) 
	    ((equal (car entry) ':menu)
	     (let ((label (car (cdr entry)))
		   (menu (cdr (cdr entry))))
	       (define-key map (extend-key-vector key label)
		 (cons label (make-sparse-keymap label)))
	       (define-menus map (extend-key-vector key label) menu (concat prefix "-" label))))
	    ((equal (car entry) ':label)
	     (define-key map (extend-key-vector key (nth 1 entry)) (cons (nth 1 entry) nil)))
	    ((equal (car entry) ':entry)
	     (define-menu-function map key entry prefix))
	    (t (error (format "Bad menu %s" entry)))))
    (setq menu (cdr menu))))

(defun define-menu-function (map key entry prefix)
  (let ((label (nth 1 entry))
	(function (nth 2 entry))
	(function-name (make-function-name prefix (nth 1 entry)))
	(arg (menu-get-arg entry))
	;; TODO. Special purpose.  Need to generalize. 
	(pre  (get-keyword-value ':pre entry))
	(post (get-keyword-value ':post entry))
	(to-top (memq ':to-top entry))
	(wrapped-p (not (memq ':unwrapped entry))))
    (cond ((stringp function)
	   (eval (menu-function function-name arg function to-top wrapped-p nil pre post))
	   (define-key map (extend-key-vector key label) (cons label function-name)))
	  ((not (symbolp function)) (error (format "Bad menu entry %s" entry)))
	  ((fboundp function)
	   (if (or pre post) (error (format "Pre or post not allowed with function: %s" entry)))
	   (define-key map (extend-key-vector key label) (cons label function)))
	  ((keymapp (eval function))
	   (define-key map (extend-key-vector key label) (cons label function)))
	  (t (error (format "Bad menu entry %s" entry))))))

;; ----------------------------------------------------------------------
;; Popup Menus

(defun interface-noop () nil)

;; My simple hack for inserting labels doesn't work if any two labels
;; are the same.  Only the last one shows up.

(defun define-popup-menu (map-name menu-name entries)
  "MAP-NAME is a keymap name.  MENU-NAME must be bound to a menu-tree."
  (let ((map (eval map-name))
	function-name)
    (cond ((not (keymapp map)) (error (format "%s is not a keymap name." map-name)))
	  ((should-i-install map-name 'popup-menu)
	   ;; Initialize-popup-menu defines the function that is called when
	   ;; the mouse button is pressed.  Creates menu named menu-name.
	   (setq function-name (initialize-popup-menu menu-name))
	   (define-key map down-mouse (cons "Doesnt print" function-name))
	   ;; So that menus will come out looking like the user typed them in
	   ;; we reverse the menu list first.
	   (setq entries (reverse entries))
	   (while entries
	     (define-popup-menu-item menu-name (car entries))
	     (setq entries (cdr entries)))))))

(defun define-popup-menu-item (menu-name entry)
  ;; entry ::= (:entry "label" [function or string] . keys)
  (let* ((label (nth 1 entry))
	 (operation (nth 2 entry))
	 (function-name (make-function-name menu-name label))
	 (arg (menu-get-arg entry))
	 ;; TODO. Special purpose.  Need to generalize. 
	 (pre  (get-keyword-value ':pre entry))
	 (post (get-keyword-value ':post entry))
	 (to-top (memq ':to-top entry))
	 (wrapped-p (not (memq ':unwrapped entry))))
    ;;
    (cond ((equal (car entry) ':label)
	   (define-key (eval menu-name) (make-key-vector 'interface-noop)
	     (cons label nil)))
	  ((not (equal (car entry) ':entry))
	   (error (format "%s not allowable entry for popup meunu %s"
			  entry menu-name)))
	  ((stringp operation)
	   ;; Create the function.
	   (eval (menu-function function-name arg operation to-top  wrapped-p 'popup pre post))
	   (put function-name menu-name arg)
	   (define-key (eval menu-name) (make-key-vector function-name) (cons label t)))
	  ((not (symbolp operation))
	   (error (format "Bad popup function in %s" entry)))
	  ((fboundp operation) (setq function-name operation)
	   (if (or pre post) (error (format "Pre or post not allowed with function: %s" entry)))
	   (put function-name menu-name arg)
	   (define-key (eval menu-name) (make-key-vector function-name) (cons label t)))
	  (t (error (format "Undefined popup function in %" entry))))))

(defun initialize-popup-menu (menu-name)
  ;; Defines a menu named (car menu) as a subpart of map.
  ;; Defines the menu select function, MENU-NAME-SELECT, to
  ;; be hung off of a mouse key.
  (let ((function-name (intern (concat (symbol-name menu-name) "-select"))))
    (set menu-name (make-sparse-keymap))
    (define-selection-function function-name menu-name)
    function-name))

(defun define-selection-function (function-name menu-name)
  (eval
   (acl2-substitute
    (list (cons '*menu-select* function-name)
	  (cons '*menu* menu-name))
    '(defun *menu-select* (click)
       "This function is invoked in foo mode by mouse-3"
       (interactive "e")
       ;; replace (new-mouse-position) with click
       (let ((action (x-popup-menu click *menu*))
	     args)
	 (if (consp action) (setq action (car action)))
	 (if (not (symbolp action))
	     (error "MENU ACTION MUST BE A SYMBOLP"))
	 (setq args (get action '*menu*))
	 ;; First case indicates we abandoned the menu without selecting anything.
	 (cond ((null action) nil)
	       ((null args)    (apply action nil))
	       ((numberp args) (apply action (list args)))
	       ((equal args t) (apply action (list t)))
	       ((eq args 'click) (apply action (list click)))
	       ((memq args '(buffer filename line word sentence sexp symbol number list event cd))
		(apply action (list (thing-at-click click args))))
	       ;; Default assumes that the args you have supplied are
	       ;; to be evaled.
	       (t (apply action (mapcar (function eval) args)))))))))
	    
(defun menu-function (name arg command &optional to-top wrapped-p popup pre post)
  (let ((arg-name (defmenu-arg-name arg popup))
	(interactive (defmenu-interactive-arg arg popup))
	body)
    ;; COMMAND must be string.
    (if wrapped-p (setq command (format interface-wrapper command)))
    (setq body (menu-function-body command arg-name popup))
    (append (list 'defun
		  name
		  (if arg-name (list arg-name) ())
		  interactive)
	    (if pre (list pre))
	    (if to-top
		(list interface-to-top
		      body)
		(list body))
	    (if post (list post)))))

(defvar menu-keyword-list '(:arg :to-top :unwrapped :pre :post))

(defun menu-keywordp (x) (memq x menu-keyword-list))

(defun menu-get-arg (l)
  ;; l is an entry.
  ;; form is (:entry label symbol . keys)
  ;; also allow, because it is a mistake made repeatedly,
  ;; (:entry label symbol arg . keys)
  (let ((x (memq ':arg l)))
    (cond (x (nth 1 x))
	  ((and (equal (car l) ':entry)
		(> (length l) 3)
		(not (menu-keywordp (nth 3 l))))
	   (nth 3 l))
	  (t nil))))

(defun get-keyword-value (key l)
  ;; l is an entry.
  ;; form is (:entry label symbol . keys)
  (let ((x (member-equal key (cdr l))))
    (cond (x (nth 1 x))
	  (t nil))))

;; Mouse event naming:

;; [ modifiers ][ number ][ kind ] MOUSE button
;; button    := -1  -2  -3
;; modifiers := C-  M-  H-  s-  A-  S-
;; number    := double-  triple-
;; kind      := drag-  down-  up-

;; Dummy prefix keys and their meanings:

;; mode-line             The mouse was in the mode line of a window.
;; vertical-line         The mouse was in the vertical line separating side-by-side windows.
;; vertical-scroll-bar   The mouse was in a vertical scroll bar.
;; horizontal-scroll-bar The mouse was in a horizontal scroll bar.  Rare.

;; Click accessors
;; (down-mouse-3 (#<window 43 on *scratch*> 236 (53 . 8) 1222667))
;;               |
;;               event-start
;; (#<window 43 on *scratch*> 236 (53 . 8) 1222667)
;;  |                         |   |
;;  posn-window               |   posn-col-row 
;;                            posn-point 


;; ----------------------------------------------------------------------
;; Menu-bar utilities

(defun remove-from-menu-bar (remove map)
  ;; Delete menu-bar items whose labels match the strings in REMOVE.
  (when map
    (mapcar
     (function (lambda (x) (define-key map (extend-key-vector [menu-bar] x) nil)))
     remove)))

;; MENU-BAR-FINAL-ITEMS is a global, honored by all menu-bar
;; presentations.  If the menu-bar contains any element whose car (a
;; SYMBOL) is in it, that element will appear after any not mentioned.
;; The ordering provided by MENU-BAR-FINAL-ITEMS is honored.  
;; (setq  menu-bar-final-items final)


;; ----------------------------------------------------------------------
;; Menu function definition and argument extraction/translation

(defconst menu-arg-name
  '((click click)
    (number number) (integer number)
    (sexp sexp) (sexpr sexp)
    (file file) (filename file) 
    (symbol symbol)))

(defun defmenu-arg-name (x &optional popup)
  (if (assoc x menu-arg-name)
      (car (cdr (assoc x menu-arg-name)))
      x))

(defconst menu-interactive-arg 
  '((click    (interactive "e"))
    (symbol   (interactive (list (read-symbol-with-default))))
    (integer  (interactive (list (read-number-with-default))))
    (number   (interactive (list (read-number-with-default))))
    (file     (interactive "f"))
    (filename (interactive "f"))
    (sexpr    (interactive "X"))
    (sexp     (interactive "X"))))

(defconst popup-menu-interactive-arg 
  '((symbol   (interactive "S"))
    (integer  (interactive "n"))
    (number   (interactive "n"))
    (file     (interactive "f"))
    (filename (interactive "f"))
    (sexpr    (interactive "X"))
    (sexp     (interactive "X"))))
    
(defun defmenu-interactive-arg (kind &optional popup)
  (if (not popup)
      (cond ((null kind) '(interactive))
	    ((assoc kind menu-interactive-arg)
	     (car (cdr (assoc kind menu-interactive-arg))))
	    (t (cond ((stringp kind) (list 'interactive kind))
		     (t (error (format "Don't recognize %s for menu-bar" kind popup))))))
      ;; The way these functions are called precludes any real use
      ;; of the interactive call to obtain the argument.
      ;; BUT, the argument types should match.
      (cond ((null kind) '(interactive))
	    ((assoc kind popup-menu-interactive-arg)
	     (car (cdr (assoc kind popup-menu-interactive-arg))))
	    (t (cond ((stringp kind) (list 'interactive kind))
		     (t (error (format "Don't recognize %s for popups" kind))))))))


;; The basic EMACS wrapper to send a command to the process buffer.
;; Some arg types may require special handling, in which case they
;; are in one or both of the `-arg-functions' alists.

(defun menu-function-body (command arg &optional popup)
  (let ((body (cdr (assoc arg (if popup popup-arg-functions menu-arg-functions)))))
    (if (not body)
	(if popup
	    (setq body interface-popup-function)
	    (setq body interface-menu-function)))
    (subst arg '<arg> (subst command '<command> body))))


;; ----------------------------------------------------------------------
;; Popup Utiliites

(defun new-mouse-position ()
  (let ((x (mouse-position)))
    (list (list (car (cdr x)) (cdr (cdr x))) (car x))))

(defun acl2-substitute (alist form)
  (cond ((not (consp form))
	 (let ((pair (assoc form alist)))
	   (if pair (cdr pair) form)))
	(t (cons (acl2-substitute alist (car form))
		 (acl2-substitute alist (cdr form))))))

(defun subst (new old form)
  (cond ((equal form old) new)
	((not (consp form)) form)
	(t (cons (subst new old (car form))
		 (subst new old (cdr form))))))

(defun this-line-to-top () (interactive) (recenter 0))

;; ----------------------------------------------------------------------
;; Parsing objects out of the emacs buffer.

(defun thing-at-click (click type)
  (save-excursion 
    (select-window (posn-window (event-start click)))
    (goto-char (posn-point (event-start click)))
    (cond ((eq type 'symbol) (symbol-at-point))
	  ((eq type 'number) (number-at-point))
	  ((eq type 'list)   (list-at-point))
	  ((eq type 'sexp)   (find-sexp)(sexp-at-point))
	  ;; Shouldn't be in this file
	  ((eq type 'cd)     (cd-at-cursor)) 
	  ((eq type 'event)  (event-at-cursor))
	  (t (thing-at-point type)))))

(defun find-sexp ()
  (interactive)
  (cond ((looking-at "[ \t\n]+")
	 (re-search-forward "[^ \t\n]" nil nil)(backward-char 1))
	((looking-at ")") (forward-sexp -1))
	((re-search-backward "[ \t\n(\"]" nil nil) (forward-char 1))
	(t nil)))


;; ----------------------------------------------------------------------
;; Making new names and key vectors

(defun extract-menu-name (string)
  (let ((x (string-match "[ -\.]" string)))
    (cond ((null x) string)
	  ((zerop x) 
	   (if (> (length string) 0)
	       (extract-menu-name (substring string 1))
	       (makeup-menu-name)))
	  (t (substring string 0 x)))))

(defvar makeup-index 1)

(defun makeup-menu-name ()
  (let ((s (format nil "BOGUS-~S" makeup-index)))
    (setq makeup-index (+ makeup-index 1))
    s))

(defun make-key-vector (name)
  (if (stringp name)
      (setq name (intern (remove-blanks name))))
  (make-vector 1 name))

(defun extend-key-vector (vector name)
  (if (stringp name)
      (setq name (intern (remove-blanks name))))
  (vconcat vector (make-vector 1 name)))

(defun remove-blanks (name)
  (setq name (copy-sequence name))
  (let ((n (length name))
	(i 0))
    (while (< i n)
      (if (char-equal (aref name i) ?\ )
	  (aset name i ?-))
      (setq i (+ i 1)))
    name))

(defun mk-symbol (a b)
  (cond ((string-match "%" a) (intern (format a b)))
	(t (intern (concat a b)))))

(defun make-function-name (prefix insert)
  (if (vectorp prefix) (setq prefix (aref prefix 0)))
  (if (symbolp prefix) (setq prefix (remove-blanks (symbol-name prefix))))
  (if (symbolp insert) (setq insert (remove-blanks (symbol-name insert))))
  (let ((name (mk-symbol prefix insert)))
    (if (fboundp name)
	(make-function-name "%s-1" name)
	name)))

;; ----------------------------------------------------------------------
;; `Interactive' Read Functions

(defun read-number-with-default ()
  (let* (this-event
	 (x (read-string (format "Event name (default: %d)"
				 (setq this-event (number-at-cursor))))))
    (if (string-equal x "")
	(if (numberp this-event) this-event (error "Not a number"))
	(number-to-string x))))

(defun read-symbol-with-default () 
  (let* (this-event
	 (x (read-string (format "Event name (default: %s)"
		       (setq this-event (symbol-at-cursor))))))
    (if (string-equal x "")
	this-event
	x)))

(defun number-at-cursor ()
  (save-excursion
    (if (looking-at "[ \t\.(]+")
	(goto-char (match-end 0))
	(progn (re-search-backward "[^0-9]" nil t) (forward-char 1)))
    (let ((start (point))
	  max
	  end)
      (setq max (save-excursion (end-of-line) (point)))
      (if (looking-at "[-0-9]+")
	  (if (re-search-forward "[ ()\.\n\t]" max t)
	      (string-to-number (buffer-substring start (- (point) 1)))
	      (string-to-number (buffer-substring start max)))))))

(defun symbol-at-cursor ()
  (save-excursion
    (if (looking-at "[ \t\.(]+")
	(goto-char (match-end 0))
	(progn (re-search-backward "[ \t\.()\n]+" nil t) (forward-char 1)))
    (let ((start (point))
	  max
	  end)
      (setq max (save-excursion (end-of-line) (point)))
      (if (re-search-forward "[ ()\.\n\t]" max t)
	  (buffer-substring start (- (point) 1))
	  (buffer-substring start max)))))

(defun define-mode-keys (mode-map-name mode-map keys)
  ;; An entry in keys may have two forms:
  ;; (key function)     
  ;; (keymap key function)
  ;; The second allows you to create subkeymaps, e.g. Control-Z
  (if (should-i-install mode-map-name 'keys)
      (mapcar
       (function (lambda (x)
		   (if (equal (length x) 2)
		       (define-key mode-map (car x) (car (cdr x)))
		       (if (keymapp (eval (car x)))
			   (define-key (eval (car x)) (car (cdr x)) (car (cdr (cdr x))))
			   (error
			    (format "Keymap %s not defined in mode %s" (car x) (car mode-map)))))))
       keys)))

;; HOOKS

;; All of the necessary hooks are set up by doing
;; (mode-interface-hook "mode").  E.g. (mode-interface-hook "acl2")

(defun extend-hook (hook entry)
  ;; Add an entry onto a mode-hook, being sensitive to the
  ;; stupid Emacs permission for it to be a function or list
  ;; of functions.
  (cond ((null hook) (list entry))
	((symbolp hook) (if (not (equal entry hook)) (list hook entry) hook))
	((not (consp hook)) 
	 (message (format "Strange hook, %s, replaced by %s." hook entry))
	 (list entry))
	((equal (car hook) 'lambda)
	 (list hook entry))
	((member-equal entry hook) hook)
	(t (append hook (list entry)))))

(defmacro define-interface (xxx mode-map-name menu-bar menu-bar-remove popup-menu keys)
  ;; xxx = mode-name, because emacs has some inhibitions about setting mode-name.
  (let ((<mode>-map-set (make-function-name xxx "-map-set"))
	(<mode>-mode-revert-fn (make-function-name xxx "-revert-fn"))
	(<mode>-saved-mode-map (make-function-name xxx "-saved-map"))
	(<mode>-menu-bar-name (make-function-name xxx "-menu-bar"))
	(<mode>-menu-bar-remove-name (make-function-name xxx "-menu-bar-remove"))
	(<mode>-popup-menu-name (make-function-name xxx "-popup-menu"))
	(<mode>-keys-name (make-function-name xxx "-keys"))
	(<mode>-mode-hook (make-function-name xxx "-hook"))
	(<mode>-interface-hook-fn (make-function-name xxx "-interface-hook-fn"))
	(<mode>-prefix-menu (concat (symbol-name xxx) "-menu-"))
	(<mode>-prefix-popup (concat (symbol-name xxx) "-popup-"))
	(<mode>-prefix-keys (concat (symbol-name xxx) "-keys-")))
    (if (equal <mode>-popup-menu-name popup-menu)
	(setq <mode>-popup-menu-name (make-function-name <mode>-popup-menu-name "-2")))
    (acl2-substitute (list (cons '<mode>-map-name   mode-map-name)
			   (cons '<mode>-menu-bar   menu-bar)
			   (cons '<mode>-menu-bar-remove menu-bar-remove)
			   (cons '<mode>-popup-menu popup-menu)
			   (cons '<mode>-keys       keys)
			   (cons '<mode>-menu-bar-name <mode>-menu-bar-name)
			   (cons '<mode>-popup-menu-name <mode>-popup-menu-name)
			   (cons '<mode>-menu-bar-remove-name <mode>-menu-bar-remove-name)
			   (cons '<mode>-keys-name <mode>-keys-name)
			   (cons '<mode>-map-set <mode>-map-set)
			   (cons '<mode>-mode-revert-fn <mode>-mode-revert-fn)
			   (cons '<mode>-saved-mode-map <mode>-saved-mode-map)
			   (cons '<mode>-mode-hook <mode>-mode-hook)
			   (cons '<mode>-interface-hook-fn <mode>-interface-hook-fn)
			   (cons '<mode>-prefix-menu <mode>-prefix-menu)
			   (cons '<mode>-prefix-popup <mode>-prefix-popup)
			   (cons '<mode>-prefix-keys <mode>-prefix-keys))
	'(progn

	   (defconst <mode>-map-set nil)

	   (defconst <mode>-menu-bar-name <mode>-menu-bar)
	   (defconst <mode>-menu-bar-remove-name <mode>-menu-bar-remove)

	   (defun <mode>-mode-revert-fn ()
	     (setq <mode>-map-name <mode>-saved-mode-map)
	     (setq <mode>-map-set nil))

	   (defun <mode>-interface-hook-fn ()
	     (cond ((and (boundp '<mode>-map-name) (not <mode>-map-set))
		    (setq <mode>-saved-mode-map (copy-keymap <mode>-map-name))
		    (remove-from-menu-bar <mode>-menu-bar-remove <mode>-map-name)
		    (extend-menu-bar '<mode>-map-name [menu-bar] <mode>-menu-bar-name
				     <mode>-prefix-menu)
		    (define-popup-menu '<mode>-map-name '<mode>-popup-menu-name 
		                       <mode>-popup-menu)
		    (define-mode-keys '<mode>-map-name <mode>-map-name <mode>-keys)
		    (setq <mode>-map-set t))))

	   (defconst <mode>-mode-hook
	     (if (boundp '<mode>-mode-hook)
		 (extend-hook <mode>-mode-hook '<mode>-interface-hook-fn)
		 '(<mode>-interface-hook-fn)))

	   (<mode>-interface-hook-fn)))))

;; Debugging
;; (defun set-last-click (click) (setq last-click click))
;; (define-menu-item mks-menu "Set last click" 'set-last-click 'click)
;; (x-popup-menu last-click inferior-acl2-mode-popup-menu)
