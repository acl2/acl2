; trace-star.lisp - A beginner-friendly variant of trace$.
;
; Peter C. Dillinger, Northeastern University, 2008
; Based on code from Matt Kaufmann

(in-package "ACL2")

(program)
(set-state-ok t)

(include-book "evalable-printing")

(defun trace*-entry (fn)
  `(:fmt
    (msg "~@1~y2"
         (first-trace-printing-column state)
         (cond ((< 1 (@ trace-level))
                "")
               ((not (eq ':none (@ acl2::guard-checking-on)))
                "!! Warning: guard-checking is not :none, so trace    !!~|~t0~
                 !!   output could be misleading or appear incorrect. !!~|~t0~
                 !!   (see :DOC set-guard-checking)                   !!~|~t0")
               ((getprop ',fn 'predefined nil 'current-acl2-world (w state))
                "!! Warning: tracing a built-in function, so trace    !!~|~t0~
                 !!   output could be misleading or appear incorrect. !!~|~t0~
                 !! (Consider writing & using a wrapper function.)    !!~|~t0")
               (t ""))
         (cons ',fn (make-evalable-with-stobjs
                      acl2::arglist
                      (getprop ',fn 'stobjs-in nil 'current-acl2-world (w state)))))))

(defun trace*-exit (fn)
  `(:fmt (msg "~y2~|~t0= ~y1"
              (max (- (first-trace-printing-column state) 2) 0)
              (let ((stobjs-out (getprop ',fn 'stobjs-out '(nil) 'current-acl2-world (w state))))
                (if (and (consp stobjs-out)
                         (endp (cdr stobjs-out)))
                  (car (make-evalable-with-stobjs values stobjs-out))
                  (cons 'mv
                        (make-evalable-with-stobjs values stobjs-out))))
              (cons ',fn (make-evalable-with-stobjs
                          acl2::arglist
                          (getprop ',fn 'stobjs-in nil 'current-acl2-world (w state)))))))

(defun trace*-modify1 (ctx trace-spec)
  (cond
    ((and (consp trace-spec)
          (symbolp (car trace-spec))
          (keyword-value-listp (cdr trace-spec)))
     (let ((fn (car trace-spec)))
       (append trace-spec
               ;; some defaults:
               (list :entry (trace*-entry fn)
                     :exit (trace*-exit fn)
                     :hide nil
                     :evisc-tuple '(list (acl2::trace-evisceration-alist state)
                                         nil nil nil)))))
    ((symbolp trace-spec)
     (trace*-modify1 ctx (list trace-spec)))
    (t (er hard ctx
           "A trace spec must be a symbol or a symbol consed onto an alternating list ~
            of the form (:kwd1 val1 :kwd2 val2 ...).  The trace spec ~x0 is thus ~
            illegal.  See :DOC trace$."
           trace-spec))))

(defun trace*-modify (ctx trace-specs)
  (cond ((endp trace-specs)
         nil)
        (t (cons (trace*-modify1 ctx (car trace-specs))
                 (trace*-modify ctx (cdr trace-specs))))))

(defmacro trace* (&rest trace-specs)
  ":Doc-Section Trace

  trace function evaluations~/

  ~c[Trace*] is a beginner-friendly variant of ~ilc[trace$], the ACL2 tracing
  utility. ~l[trace$] for more documentation and advanced functionality.

  ~c[Trace*] should be used with ~c[:set-guard-checking :none] and should not
  be used to trace built-in functions.

  The log below illustrates the differences between ~c[trace*] and ~c[trace$]:
  ~bv[]
  ACL2 p>
  (defun app (x y)
    (if (endp x)
      y
      (cons (car x) (app (cdr x) y))))
  ...
   APP
  ACL2 p>(trace$ app)
   ((APP))
  ACL2 p>(app (list 1 2) (list 3))
  1> (ACL2_*1*_ACL2::APP (1 2) (3))
    2> (ACL2_*1*_ACL2::APP (2) (3))
      3> (ACL2_*1*_ACL2::APP NIL (3))
      <3 (ACL2_*1*_ACL2::APP (3))
    <2 (ACL2_*1*_ACL2::APP (2 3))
  <1 (ACL2_*1*_ACL2::APP (1 2 3))
  (1 2 3)
  ACL2 p>(trace* app)
   (APP)
  ACL2 p>(app (list 1 2) (list 3))
  1> (APP (LIST 1 2) (LIST 3))
    2> (APP (LIST 2) (LIST 3))
      3> (APP NIL (LIST 3))
      <3 (APP NIL (LIST 3))
       = (LIST 3)
    <2 (APP (LIST 2) (LIST 3))
     = (LIST 2 3)
  <1 (APP (LIST 1 2) (LIST 3))
   = (LIST 1 2 3)
  (1 2 3)
  ACL2 p>
  ~ev[]~/~/"
  `(er-progn (trace$ ,@(trace*-modify 'trace* trace-specs))
             (value ',trace-specs)))

#| test
(logic)

(set-guard-checking :none)

(defun app (x y)
  (if (endp x)
    y
    (cons (car x) (app (cdr x) y))))

(trace$ app)

(app (list 1 2) (list 3))

(trace* app)

(app (list 1 2) (list 3))



(defun fact (n)
  (if (zp n)
      1
    (* n (fact (1- n)))))

(trace$ fact)

(fact 3)

(trace* fact)

(fact 3)

;;; Modification by Matt K. for after ACL2 3.6.1 for early loading of compiled
;;; files (see books/misc/evalable-printing.lisp):

(trace* get-evalable-printing-abstractions)

(get-evalable-printing-abstractions state)

;|#
