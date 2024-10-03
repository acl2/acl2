;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; utils.lisp
; Author  Jun Sawada, University of Texas at Austin
;
; ACL2 utility functions and macros.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "absolute-path")
(include-acl2-book "data-structures/utilities")

(u::import-as-macros
 U::A-UNIQUE-SYMBOL-IN-THE-U-PACKAGE
 defloop)

(defloop non-rec-functions (runes world)
  (for ((rune in runes))
       (unless (fgetprop (cadr rune) 'induction-machine nil world)
	 (collect rune))))

(defloop rec-functions (runes world)
  (for ((rune in runes))
       (when (fgetprop (cadr rune) 'induction-machine nil world)
	 (collect rune))))

(defmacro ww (form)
  "With (W state) ..."
  `(LET ((WORLD (W STATE))) ,form))

;Example
;(ww (non-rec-functions (definition-theory (current-theory :here)) world))

;Example
; (deftheory test (non-rec-functions (theory 'table-def) world))
;
; Macro ld-up-to fast loads ACL2 events in a file to a specified point. 
;  (ld-up-to "<filename>" <event_name>  {:speed <speed> })
; This command loads ACL2 file <filename> to the point where
; <event_name> is first defined. 

; Since ld-up-to skips proofs of the theorems in a loaded file by
; default, a user can quickly reach the state where he or she wants
; to work in.  <even_name> can be any symbol newly defined by the
; event at the desired breaking point.  For instance, a label
; defined by deflabel can be used as well.  Keyword :all can be
; specified when the user want to load the whole file.

; 
; The user can specify loading speed using keyword :speed
;  :speed 0  Does not skip proofs. The slowest way to load a file.
;  :speed 1  Skips proofs, but performs other checks on theorems.
;            Ld-up-to loads files at this speed by default.
;  :speed 2  Skips proofs and other checks on theorems.  Warning
;            will not be printed out.  It also skips events local to
;            the ACL2 file.

; Example
;  (ld-up-to "invariants-def.lisp" invariants)
;   This command loads ACL2 file invariant-def.lisp until it finds the
;   definition of function invariants. 
;
;  (ld-up-to "invariants-def.lisp" :all :speed 2)
;   this command load the all events in invariants-def.lisp except
;   events local to the ACL2 book.
(defmacro ld-up-to (file event &key (speed '1))
  (let ((skip-proofs-flag (if (equal speed 0) nil
			      (if (equal speed 1) t ''include-book))))
    `(ld ,file :ld-pre-eval-filter ',event
      :ld-skip-proofsp ,skip-proofs-flag)))

; Macro refresh rolls back ACL2 history and reloads ACL2 events fast.
;
; (refresh <filename> {:back-to <event1>} {:up-to <event2>} {:speed <speed>})
;
; Refresh first undoes events back to the point where <event1> was
; defined, then it loads ACL2 file <filename> up to the point where
; <event2> is newly defined.  When previously executed ACL2 events
; like definitions and theorems are modified, the current world of ACL2
; is corrupted and a user may want to restart the ACL2 from scratch.
; However, restarting ACL2 takes a long time especially if many books
; are loaded.  Refresh helps to reload modified files and get the
; newest state of ACL2 world quickly.  It only undoes to the point
; where symbol <event1> is defined, and then loads file <filename>,
; skipping proofs by default.  Since refresh loads ACL2 books included
; by <filename>, usually the user only has to specify the top ACL2 book.
; <event1> can be a symbol defined in an included book, and refresh
; undoes the include-book of the included book.  If :back-to
; keyword is not supplied, refresh undoes all user defined events.  If
; :up-to keyword is not given, it load all events in <filename>.  So
; (refresh <filename>) is equivalent to (refresh <filename> :back-to 1
; :up-to :all).  <event1> can be a number designating an event.
; 
; The user can also specify loading speed using keyword :speed
;  :speed 0  Does not skip proofs. The slowest way to load a file.
;  :speed 1  Skips proofs, but performs other checks on theorems.
;            Ld-up-to loads files at this speed by default.
;  :speed 2  Skips proofs and other checks on theorems.  Warning
;            will not be printed out.  It also skips events local to
;            the ACL2 file.

(defmacro refresh (file &key (back-to '1) (up-to ':all) (speed '1))
  (let ((skip-proofs-flag (if (equal speed 0) nil
			      (if (equal speed 1) t ''include-book))))
    `(ld '((ubt! ',back-to) (ld ,file :ld-pre-eval-filter ',up-to
			     :ld-skip-proofsp ,skip-proofs-flag)))))

;;;;;;;
; A computed hint
;;;;;;
(defmacro use-hint-always (hint)
  `',hint)

; When-found is a macro to supply a computational hint.  When term is
; found in the goal clause, hint is invoked.  An example usage follows:
;  :hints ((when-found (FETCHED-INST MT (MT-FINAL-ISA MT)
;				    (MT-IN-SPECULTV? MT))
;		      (:cases ((b1p (MT-IN-SPECULTV? MT))))))
;
(defmacro when-found (term hint)
  `(and (occur-lst ',term clause) ',hint))

(defun multiple-occur-check (terms)
  (if (endp terms)
      nil
      (if (endp (cdr terms))
	  `(occur-lst ',(car terms) clause)
	  `(and (occur-lst ',(car terms) clause)
	    ,(multiple-occur-check (cdr terms))))))
		
(defmacro when-found-multiple (terms hint)
  `(and ,(multiple-occur-check terms) ',hint))

(defmacro show-hint (hint &optional marker)
  (cond
   ((and (consp hint)
         (stringp (car hint)))
    hint)
   (t
    `(let ((marker ,marker)
           (ans ,(if (symbolp hint)
                     `(,hint id clause world)
                   hint)))
       (if ans
           (prog2$
            (cw "~%***** Computed Hint~#0~[~/ (from hint ~x1)~]~%~x2~%~%"
                (if (null marker) 0 1)
                marker
                (cons (string-for-tilde-@-clause-id-phrase id)
                      ans))
            ans)
         nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pattern match functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; do not check if x is a cons.
(defun fmeta-varp (x)
  (and (equal (car x) '@) (symbolp (cadr x))))

(defun fmeta-var-name (x) (cadr x))

(defmacro mv2-or (first second)
  `(mv-let (flg val) ,first
    (if flg (mv flg val) ,second)))

(program)
; restriction on pattern matching. 
;  We don't look into quoted constants.  Quoted constants should be literally
; equal to the pattern or match to a meta-variable as it is.
; Pattern Match returns the substitution for the outer-most matching pattern.
; There may be more than two subterms that match the same pattern.
(mutual-recursion
(defun pattern-match (pattern term subst)
  (cond ((variablep pattern)
	 (if (eq pattern term) (mv t subst) (mv nil nil)))
	((fquotep pattern)
	 (if (equal pattern term) (mv t subst) (mv nil nil)))
	((fmeta-varp pattern)
	 (let ((inst (assoc-eq (fmeta-var-name pattern) subst)))
	   (if inst
	       (if (equal term (cdr inst)) (mv t subst) (mv nil nil))
	       (mv t (cons (cons (fmeta-var-name pattern) term) subst)))))
	((and (not (variablep term))
	      (not (fquotep term))
	      (eq (ffn-symb pattern) (ffn-symb term)))
	 (pattern-match-lst (fargs pattern) (fargs term) subst))
	(t (mv nil nil))))
	 
(defun pattern-match-lst (patterns terms subst)
  (cond ((and (null patterns) (null terms))
	 (mv t subst))
	((or (null patterns) (null terms)) (mv nil nil))
	(t (mv-let (flg new-subst)
		   (pattern-match (car patterns) (car terms) subst)
	      (if flg
		  (pattern-match-lst (cdr patterns) (cdr terms) new-subst)
		  (mv nil nil))))))
)
      

(mutual-recursion
(defun pattern-occur (pattern term subst)
  (if (or (variablep term) (fquotep term))
      (pattern-match pattern term subst)
      (mv2-or (pattern-match pattern term subst)
	      (pattern-occur-lst pattern (fargs term) subst))))

(defun pattern-occur-lst (patterns args subst)
  (cond ((null args) (mv nil nil))
	(t (mv2-or (pattern-occur patterns (car args) subst)
		   (pattern-occur-lst patterns (cdr args) subst)))))
)
    
(mutual-recursion
(defun subst-meta (pattern subst)
  (cond ((or (variablep pattern) (fquotep pattern))
	 pattern)
	((fmeta-varp pattern)
	 (let ((inst (assoc-eq (fmeta-var-name pattern) subst)))
	   (if inst (cdr inst) pattern)))
	(t (cons (ffn-symb pattern) (subst-meta-lst (fargs pattern) subst)))))

(defun subst-meta-lst (patterns subst)
  (if (null patterns)
      nil
      (cons (subst-meta (car patterns) subst)
	    (subst-meta-lst (cdr patterns) subst))))
)

(defmacro when-pattern-found (term hint)
  `(mv-let (flg subst) (pattern-occur-lst ',term clause nil)
    (if flg (subst-meta ',hint subst) nil)))

(defun multiple-pattern-check (terms)
  (if (endp terms)
      nil
      (if (endp (cdr terms))
	  `(pattern-occur-lst ',(car terms) clause nil)
	  `(mv-let (flg subst) ,(multiple-pattern-check (cdr terms))
	    (if flg
		(pattern-occur-lst ',(car terms) clause subst)
		(mv nil nil))))))

		
(defmacro when-multi-pattern-found (terms hint)
  `(mv-let (flg subst) ,(multiple-pattern-check (reverse terms))
    (if flg (subst-meta ',hint subst) nil)))
