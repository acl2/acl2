#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "ACL2S")
(defconst *acl2s-version* "ACL2s Version 1.3.1")

; Common books to all modes.
(include-book "cgen/top" :ttags :all)
(include-book "defunc" :ttags :all)
(include-book "definec" :ttags :all)
(include-book "defintrange" :ttags :all)
(include-book "acl2s-sigs" :ttags :all)

;; (defun allp (x)
;;   (declare (ignore x)
;;            (xargs :guard t))
;;   t)


;(program)

;***** DEFUNT macro for Pete Manolios & Northeastern CSU290 ***** 

(defun defunt-make-sym (s suf)
; Returns the symbol s-suf.
  (declare (xargs :guard (and (symbolp s) (symbolp suf))))
  (fix-intern-in-pkg-of-sym
   (concatenate 'string
                (symbol-name s)
                "-"
                (symbol-name suf))
   s))

(defun defunt-make-code-list (l)
  (if (or (null l)
          (and (consp l)
               (consp (car l))
               (not (eq 'lambda (caar l)))))
    l
    (list l)))

(defun defunt-declarations-prefix (args)
  (if (or (atom args)
          (atom (car args))
          (not (eq 'declare (caar args))))
    nil
    (cons (car args)
          (defunt-declarations-prefix (cdr args)))))

(defun defunt-after-declarations (args)
  (if (or (atom args)
          (atom (car args))
          (not (eq 'declare (caar args))))
    args
    (defunt-after-declarations (cdr args))))


(defmacro defunt (&rest def)
; A function definition that has a declare followed by a list of the
; form ((thm) commands), where commands can be anything that you would
; give to a defthm (look at defthm documentation), specifically it is:
;        :rule-classes rule-classes
;        :instructions instructions
;        :hints        hints
;        :otf-flg      otf-flg
;        :doc          doc-string
    (let* ((name-lst (and (consp def)
                          (symbolp (car def))
                          (list (car def))))
         (ll-lst (and (consp (cdr def))
                      (symbol-listp (cadr def))
                      (list (cadr def))))
         (rst1 (cddr def))
         (doc-lst (and (stringp (car rst1)) (list (car rst1))))
         (rst2 (if (stringp (car rst1)) (cdr rst1) rst1))
         (body-lst (last rst2))
         (rst3 (butlast rst2 1))
         (decls-before-type-thm (defunt-declarations-prefix rst3))
         (thm-stuff (defunt-make-code-list (car rst3)))
         (rst4 (cdr rst3))
         (decls (defunt-declarations-prefix rst4))
         (kruft (defunt-after-declarations rst4)))
    (if (and name-lst
             ll-lst
             body-lst
             thm-stuff
             (not decls-before-type-thm)
             (not kruft))
      (if (consp (car thm-stuff))
        `(progn
          (defun ,@name-lst ,@ll-lst
            ,@doc-lst
            ,@decls
            . ,body-lst)
          (defthm ,(defunt-make-sym (car name-lst) 'type)
            . ,thm-stuff))
        `(er soft 'defunt
             "The type theorem specified to DEFUNT, ~x0, is silly.  You should ~
              specify a more interesting type theorem or just use DEFUN."
             ',(car thm-stuff)))
      `(er soft 'defunt
           "Malformed call to DEFUNT.  Most uses of DEFUNT will take the form~%~%~
            (defunt <name> <params>~%  <type-theorem>~%  <function body>)~%~%~
            where <type-theorem> is either a theorem term or (<theorem-term> <defthm-keyword-args...>) ~
            where <defthm-keyword-args> are keyword arguments to defthm, such as :rule-classes or :hints.~%~%~
            More generally, it may take the form:~%~%~
            (defunt <name> <params>~%  <optional-doc-string>~%  <type-theorem>~%  <optional-declarations...>~%  <function body>)~%"))))

(defmacro acl2-user::defunt (&rest def)
  `(defunt . ,def))

;(logic)


#|
(defmacro acl2s-common-settings ()
`(er-progn
  (assign checkpoint-processors
          (set-difference-eq (@ checkpoint-processors)
                             '(ELIMINATE-DESTRUCTORS-CLAUSE)))
  
  ;;CCG settings
  (set-ccg-print-proofs nil)     
  (set-ccg-inhibit-output-lst
   '(QUERY BASICS PERFORMANCE BUILD/REFINE SIZE-CHANGE))

  ;; PETE: for debugging          
  ;; (acl2::set-guard-checking :nowarn)
  (acl2::set-guard-checking :all)

  (assign acl2::splitter-output nil)

  (set-default-hints
   '((my-nonlinearp-default-hint stable-under-simplificationp hist pspv)
     (acl2s::stage acl2s::negp)
     (acl2s::stage acl2s::posp)
     (acl2s::stage acl2s::natp)
     (acl2s::stage acl2s::non-pos-integerp)
     (acl2s::stage acl2s::neg-ratiop)
     (acl2s::stage acl2s::pos-ratiop)
     (acl2s::stage acl2s::non-neg-ratiop)
     (acl2s::stage acl2s::non-pos-ratiop)
     (acl2s::stage acl2s::ratiop)
     (acl2s::stage acl2s::neg-rationalp)
     (acl2s::stage acl2s::pos-rationalp)
     (acl2s::stage acl2s::non-neg-rationalp)
     (acl2s::stage acl2s::non-pos-rationalp)))

  ;; Other events:
  (set-well-founded-relation l<)
  (if (member-eq 'ruler-extenders-lst
                 (getprop 'put-induction-info 'formals nil
                          'current-acl2-world (w state)))
      (value '(set-ruler-extenders :all))
    (value '(value-triple :invisible)))

  ;;CCG events
  (set-termination-method :ccg)
  (set-ccg-time-limit nil)

  ;;Cgen settings
  (acl2s::acl2s-defaults :set acl2s::testing-enabled t)
  (acl2s::acl2s-defaults :set acl2s::num-trials 500)

  (make-event '(dont-print-thanks-message-override-hint))
  (value '(value-triple :invisible))
  ))
|#


#!ACL2
(defmacro acl2s-common-settings ()
`(progn

   ;; There doesn't seem to be a good way to set guard-checking
   ;; here. Previously, we were doing this inside of the er-progn
   ;; which is inside of the make-event, but while that works for
   ;; set-ccg-print-proofs, etc, it does not work for
   ;; set-guard-checking because it is in
   ;; *protected-system-state-globals* so any changes are reverted
   ;; back to what they were when there is a make-event involved. In
   ;; order to keep this interface, one option is to use progn!, but I
   ;; decided to pull this out from here and put it into
   ;; acl2s-mode.lsp to avoid requiring a trust tag for
   ;; acl2s-common-settings.
   
   ;; How to check (f-get-global 'guard-checking-on state)
   ;; (acl2::set-guard-checking :nowarn)

   ;; (acl2::set-guard-checking :nowarn)
   ;; (acl2::set-guard-checking :all)

  (make-event
   (er-progn
    (assign checkpoint-processors
            (set-difference-eq (@ checkpoint-processors)
                               '(ELIMINATE-DESTRUCTORS-CLAUSE)))
  
    ;;CCG settings
    (set-ccg-print-proofs nil)     
    (set-ccg-inhibit-output-lst
     '(QUERY BASICS PERFORMANCE BUILD/REFINE SIZE-CHANGE))
    (assign acl2::splitter-output nil)
    (value '(value-triple :invisible))))
      
  (set-default-hints
   '((my-nonlinearp-default-hint stable-under-simplificationp hist pspv)
     (acl2s::stage acl2s::negp)
     (acl2s::stage acl2s::posp)
     (acl2s::stage acl2s::natp)
     (acl2s::stage acl2s::non-pos-integerp)
     (acl2s::stage acl2s::neg-ratiop)
     (acl2s::stage acl2s::pos-ratiop)
     (acl2s::stage acl2s::non-neg-ratiop)
     (acl2s::stage acl2s::non-pos-ratiop)
     (acl2s::stage acl2s::ratiop)
     (acl2s::stage acl2s::neg-rationalp)
     (acl2s::stage acl2s::pos-rationalp)
     (acl2s::stage acl2s::non-neg-rationalp)
     (acl2s::stage acl2s::non-pos-rationalp)))

  ;; Other events:
  (set-well-founded-relation l<)
  (make-event ; use ruler-extenders if available
   (if (member-eq 'ruler-extenders-lst
                  (getprop 'put-induction-info 'formals nil
                           'current-acl2-world (w state)))
       (value '(set-ruler-extenders :all))
     (value '(value-triple :invisible))))

  ;;CCG events
  (set-termination-method :ccg)
  (set-ccg-time-limit 300)
  
  (dont-print-thanks-message-override-hint)
   
  ;;Cgen settings
  (acl2s::acl2s-defaults :set acl2s::testing-enabled t)
  (acl2s::acl2s-defaults :set acl2s::num-trials 500)
  (acl2s::acl2s-defaults :set acl2s::use-fixers t)

  ;; Defdata settings
  (acl2s::acl2s-defaults :set acl2s::defdata-aliasing-enabled t)
  ))

#!ACL2
(defmacro acl2s-beginner-settings ()
  `(er-progn
; Non-events:
    (acl2::set-guard-checking :all)

    (set-backchain-limit '(50 100))
    (set-rewrite-stack-limit 500)
    (acl2s-defaults :set cgen-timeout 20)
    (table acl2s::defunc-defaults-table :skip-tests nil :put)
    (table acl2s::defunc-defaults-table :timeout 60 :put)

    (set-irrelevant-formals-ok :warn)
    (set-bogus-mutual-recursion-ok :warn)
    (set-ignore-ok :warn)

    (assign evalable-ld-printingp t)
    (assign evalable-printing-abstractions '(list cons))
    (assign triple-print-prefix "; ")

    ))

#!ACL2
(defmacro acl2s-bare-bones-settings ()
  `(er-progn

    (set-irrelevant-formals-ok :warn)
    (set-bogus-mutual-recursion-ok :warn)
    (set-ignore-ok :warn)

    (set-backchain-limit '(50 100))
    (set-rewrite-stack-limit 500)
    (table acl2s::defunc-defaults-table :skip-tests nil :put)
    (table acl2s::defunc-defaults-table :timeout 60 :put)

    (assign evalable-ld-printingp t)
    (assign evalable-printing-abstractions '(list cons))
    (assign triple-print-prefix "; ")

; Non-events:
    (acl2::set-guard-checking :all)
    ))

#!ACL2
(defmacro acl2s-theorem-proving-beginner-settings ()
  `(er-progn

    (set-backchain-limit '(50 100))
    (set-rewrite-stack-limit 500)

    (set-irrelevant-formals-ok :warn)
    (set-bogus-mutual-recursion-ok :warn)
    (set-ignore-ok :warn)

    (set-guard-checking :all)
    (table acl2s::defunc-defaults-table :skip-tests nil :put)
    (table acl2s::defunc-defaults-table :timeout 60 :put)


;(set-verify-guards-eagerness 0)
    (assign evalable-ld-printingp t)
    (assign evalable-printing-abstractions '(list cons))
    (assign triple-print-prefix "; ")
    ))

