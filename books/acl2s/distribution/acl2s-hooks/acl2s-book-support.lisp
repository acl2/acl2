(in-package "ACL2S-HOOKS")

(program)
(set-state-ok t)

;; define (primitive-event-macros) if needed (3.3 or older)
(make-event
 (if (getprop 'primitive-event-macros 'symbol-class nil 'current-acl2-world (w state))
   (value '(value-triple 'primitive-event-macros))
   (value '(defun primitive-event-macros ()
             (declare (xargs :guard t :mode :logic))
             *primitive-event-macros*))))


;; BEGIN-BOOK in acl2s

;ACL2 4.3 seems to have no function named remove-first-pair. 
;so adding it here TODO (remove later)
(DEFUN REMOVE-FIRST-PAIR (KEY L)
  (DECLARE (XARGS :GUARD (AND (SYMBOLP KEY)
                              (SYMBOL-ALISTP L)
                              (ASSOC-EQ KEY L))))
  (COND ((ENDP L) NIL)
        ((EQ KEY (CAAR L)) (CDR L))
        (T (CONS (CAR L)
                 (REMOVE-FIRST-PAIR KEY (CDR L))))))

(defun ttags-seen-without-acl2s (wrld)
  (let* ((seen (global-val 'ttags-seen wrld))
         (seen (remove-first-pair :acl2s-super-history seen))
         (seen (remove-first-pair :acl2s-interaction seen))
         (seen (remove-first-pair :acl2s-protection seen))
         (seen (remove-first-pair :acl2s-markup seen))
         (seen (remove-first-pair :acl2s-trace seen))
         (seen (remove-first-pair 'acl2::defcode seen)))
    seen))

(defun nullify-cdrs (l)
  (cond ((endp l) l)
        ((consp (car l))
         (cons (list (caar l))
               (nullify-cdrs (cdr l))))
        (t
         (cons (car l)
               (nullify-cdrs (cdr l))))))

(make-event
 (if (earlier-acl2-versionp (@ acl2-version) "ACL2 Version 3.3") ; < 3.3
   (value
    '(defmacro acl2s-chk-portcullis (ctx)
       `(mv-let (erp cmds wrld-segs wrld-list state)
                     (get-portcullis-cmds (w state) nil nil nil
                             (cons 'defpkg (primitive-event-macros))
                             ,ctx state)
                     (declare (ignore cmds wrld-segs wrld-list))
                     (mv erp :invisible state))))
   (value
    '(defmacro acl2s-chk-portcullis (ctx)
       `(mv-let (erp cmds wrld-segs state)
                     (get-portcullis-cmds (w state) nil nil
                             (cons 'defpkg (primitive-event-macros))
                             ,ctx state)
                     (declare (ignore cmds wrld-segs))
                     (mv erp :invisible state))))))#|ACL2s-ToDo-Line|#


(defmacro begin-book (&optional (compile-flg 't)
                      &key (defaxioms-okp 'nil)
                           (skip-proofs-okp 'nil)
                           (ttags 'nil)
                           (save-expansion 'nil))
  (declare (xargs :guard (and (booleanp compile-flg)
                              (booleanp defaxioms-okp)
                              (booleanp skip-proofs-okp)
                              (member-eq save-expansion '(t nil :save))))
           (ignore compile-flg defaxioms-okp skip-proofs-okp save-expansion))
  `(cond
    ((getprop 'book-beginning 'acl2::symbol-class nil 'current-acl2-world (w state))
     (er soft 'begin-book
         "Book development has been disabled, probably because this session ~
          mode does not support it."))
    ((getprop 'book-beginning 'acl2::label nil 'current-acl2-world (w state))
     (er soft 'begin-book
         "The book beginning has already been marked."))
    ((not (eq :logic (default-defun-mode (w state))))
     (er soft 'begin-book
         "Default defun mode must be :logic to start a book. ~
          (see :DOC default-defun-mode)"))
    ((ld-skip-proofsp state)
     (er soft 'begin-book
         "ld-skip-proofsp must be nil to start a book.  See :DOC ~
          ld-skip-proofsp."))
    ((f-get-global 'in-local-flg state)
     (er soft 'begin-book
         "begin-book may not be called inside a LOCAL command."))
    ((global-val 'skip-proofs-seen (w state))
     (er soft 'begin-book
         "At least one command in the current ACL2 world was executed ~
          while the value of state global variable '~x0 was not ~
          nil:~|~%  ~y1~%(If you did not explicitly use ~
          set-ld-skip-proofsp or call ld with :ld-skip-proofsp not ~
          nil, then some other function did so, for example, rebuild.) ~
          Beginning a book is therefore not allowed in this world.  If ~
          the intention was for proofs to be skipped for one or more ~
          events in the certification world, consider wrapping those ~
          events explicitly in skip-proofs forms.  See :DOC ~
          skip-proofs."
         'ld-skip-proofsp
         (global-val 'skip-proofs-seen (w state))))
    ((global-val 'redef-seen (w state))
     (er soft 'begin-book
         "At least one command in the current ACL2 world was executed ~
          while the value of state global variable '~x0 was not ~
          nil:~|~%  ~y1~%Beginning a book is therefore not allowed in ~
          this world.  You should undo back through this command."
         'ld-redefinition-action
         (global-val 'redef-seen (w state))))
    ((ttag (w state))
     (er soft 'begin-book
         "It is illegal to begin a book while there is an active ~
          ttag, in this case, ~x0.  Consider undoing the corresponding ~
          defttag event (see :DOC ubt) or else executing ~x1.  See ~
          :DOC defttag."
         (ttag (w state))
         '(defttag nil)))
    ;((certify-book-disabledp state) ;;;Has been removed in ACL2 v4.0
    ; (er soft 'begin-book
    ;     "Begin/Certify-book has been disabled in this session because ~@0."
    ;     (certify-book-disabledp state)))
    
    ;; TODO: check ttags-seen, portcullis, etc.
    (t (er-let*
         ((ttags (chk-well-formed-ttags ',ttags (cbd) 'begin-book state)))
         (mv-let
          (erp pair state)
          (chk-acceptable-ttags1 (ttags-seen-without-acl2s (w state))
                                 nil ttags nil :quiet 'begin-book state)
          (declare (ignore pair))
          (if erp
            (mv-let (col state)
                    (fmx "I recommend using ~x0~%or ~x1~%~%These were probably introduced by loading an ACL2s session ~
                          mode. Passing a :ttag parameter to begin-book acknowledges that your book depends on ACL2s ~
                          extensions that pure ACL2 cannot guarantee are safe/sound.~%"
                         '(begin-book t :ttags :all)
                         `(begin-book t :ttags ,(nullify-cdrs
                                                 (ttags-seen-without-acl2s (w state)))))
                    (declare (ignore col))
                    (mv t :invisible state))
            (er-progn
             (acl2s-chk-portcullis 'begin-book)
             (with-output :off summary
                          (deflabel book-beginning))
             (mv-let (col state)
                     (acl2::fmx "Book beginning point noted.~%~%Next should come an IN-PACKAGE form, such as~%~%(in-package \"ACL2\")~%~%")
                     (mv nil col state))
             (in-package "ACL2")
             (value :invisible))))))))

