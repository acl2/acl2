#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "ACL2S")
(defconst *acl2s-version* "ACL2s Version 1.3.0")

;; (defun allp (x)
;;   (declare (ignore x)
;;            (xargs :guard t))
;;   t)


(program)


;***** CHECK and CHECK= macros for Peter Dillinger & Pete Manolios & Northeastern CSU290 *****

#|

(defmacro check (form)
  `(with-output
    :stack :push
    :off :all
    (make-event
     (with-output
      :stack :pop
     ; (state-global-let*
     ; ((guard-checking-on :none))
      (er-let*
        ((eval-result (acl2::trans-eval
                       '(if ,form
                          (value nil)
                          (er soft 'check "Check failed (returned NIL)."))
                       'check
                       state t)))
        (if (second eval-result)
          (mv t nil state)
          (value '(value-triple :passed)))))
     :check-expansion t)))

(defmacro check= (form1 form2)
  `(with-output
    :stack :push
    :off :all
    (make-event
     (with-output
      :stack :pop
      ;(state-global-let*
      ;((guard-checking-on :none))
      (er-let*
        ((eval-result1 (acl2::trans-eval ',form1 'check= state t))
         (eval-result2 (acl2::trans-eval ',form2 'check= state t)))
        (cond ((not (equal (car eval-result1)
                           (car eval-result2)))
               (er soft 'check=
                   "Forms return different number or stobj types of ~
                    results; thus, they should not be considered equal."))
              ((not (equal (cdr eval-result1)
                           (cdr eval-result2)))
               (er soft 'check=
                   "Check failed (values not equal).~%First value:  ~x0~%~
                    Second value: ~x1" (cdr eval-result1) (cdr eval-result2)))
              (t
               (value '(value-triple :passed))))))
     :check-expansion t)))

|#

;; Removed the outer with-output forms because check, check= were not 
;; embedded event forms.

(defmacro check (form)
  `(make-event
     (with-output
      :off :all
     ; (state-global-let*
     ; ((guard-checking-on :none))
      (er-let*
        ((eval-result (acl2::trans-eval
                       '(if ,form
                          (value nil)
                          (er soft 'check "Check failed (returned NIL)."))
                       'check
                       state t)))
        (if (second eval-result)
          (mv t nil state)
          (value '(value-triple :passed)))))
     :check-expansion t))

(defmacro check= (form1 form2)
  `(make-event
    (with-output
     :off :all
     (er-let*
      ((eval-result1 (acl2::trans-eval ',form1 'check= state t))
       (eval-result2 (acl2::trans-eval ',form2 'check= state t)))
      (cond ((not (equal (car eval-result1)
                         (car eval-result2)))
             (er soft 'check=
                 "Forms return different number or stobj types of ~
                    results; thus, they should not be considered equal."))
            ((not (equal (cdr eval-result1)
                         (cdr eval-result2)))
             (er soft 'check=
                 "Check failed (values not equal).~%First value:  ~x0~%~
                    Second value: ~x1" (cdr eval-result1) (cdr eval-result2)))
            (t (value '(value-triple :passed))))))
    :check-expansion t))


;***** DEFUNT macro for Pete Manolios & Northeastern CSU290 ***** 

(defun defunt-make-sym (s suf)
; Returns the symbol s-suf.
  (declare (xargs :guard (and (symbolp s) (symbolp suf))))
  (intern-in-package-of-symbol
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



(logic)



;;; When things have stabilized under simplification, enable non-linear
;;; arithmetic for one round (goal being simplified) only.

#!ACL2
(defun my-nonlinearp-default-hint (stable-under-simplificationp hist pspv)
  ;; (declare (xargs :guard (and (consp pspv)
  ;;                 (consp (car pspv))
  ;;                 (consp (caar pspv))
  ;;                 (consp (cdaar pspv))
  ;;                 (consp (cddaar pspv))
  ;;                 (consp (cdr (cddaar pspv)))
  ;;                 (consp (cddr (cddaar pspv)))
  ;;                 (consp (cdddr (cddaar pspv)))
  ;;                 (consp (cddddr (cddaar pspv))))))
  (cond (stable-under-simplificationp
         (if (not (access rewrite-constant
                   (access prove-spec-var pspv :rewrite-constant)
                   :nonlinearp))
       (prog2$
        nil ;;harshrc 14Jan2012- The following gives a nasty error when run inside of ld
        ;; (observation-cw 'my-nonlinearp-default-hint 
        ;;                 "~%~%[Note: We now enable non-linear arithmetic.]~%~%")
        '(:computed-hint-replacement t
                     :nonlinearp t))
           nil))
        ((access rewrite-constant
              (access prove-spec-var pspv :rewrite-constant)
              :nonlinearp)
         (if (and (consp hist)
          (consp (car hist))
          ;; Without this, we would loop forever.  But
          ;; whenever I try to write an explanation, I get
          ;; confused about why it works.  I stumbled across
          ;; this by trial and error and observing the output
          ;; of tracing.  Some day I should figure out what I
          ;; am doing.
          (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
         (prog2$
          nil ;;The following gives a nasty error when run inside of ld
          ;; (observation-cw 'my-nonlinearp-default-hint 
          ;;                 "~%~%[Note: We now disable non-linear arithmetic.]~%~%")
           '(:computed-hint-replacement t
                        :nonlinearp nil))
           nil))
        (t
         nil)))

; Common books to all modes.
(include-book "cgen/top" :ttags :all)
(include-book "defunc" :ttags :all)
(include-book "definec" :ttags :all)
(include-book "defintrange" :ttags :all)

#!ACL2
(defmacro acl2s-common-settings ()
`(progn
  (make-event
   (er-progn
    (assign checkpoint-processors
            (set-difference-eq (@ checkpoint-processors)
                               '(ELIMINATE-DESTRUCTORS-CLAUSE)))
     
    ;;CCG settings
    (set-ccg-print-proofs nil)     
    (set-ccg-inhibit-output-lst
     '(QUERY BASICS PERFORMANCE BUILD/REFINE SIZE-CHANGE))

    ;;Misc
    (set-guard-checking :nowarn)
    (value '(value-triple :invisible))))
   
  (make-event
   (er-progn (assign acl2::splitter-output nil)
             (value '(value-triple nil))))
   
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
  (set-ccg-time-limit nil)

  (dont-print-thanks-message-override-hint)
   
  ;;Cgen settings
  (acl2s::acl2s-defaults :set acl2s::testing-enabled t)
  (acl2s::acl2s-defaults :set acl2s::num-trials 500)

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

