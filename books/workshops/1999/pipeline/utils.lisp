(in-package "ACL2")

(include-book "../../../data-structures/utilities")

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
      `(ld ,file :ld-pre-eval-filter ',event :ld-skip-proofsp ,skip-proofs-flag)))


; Macro refresh rolls back ACL2 history and reloads ACL2 events fast.
;
; (refresh <filename> {:back-to <event1>} {:up-to <event2>} {:speed <speed>})
;

; Refresh first undoes events back to the point where <event1> was
; defined, then it loads ACL2 file <filename> up to the point where
; <event2> is newly defined.  When previously executed ACL2 events
; like definition and theorems are modified, the current world of ACL2
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


