(in-package "ACL2")

(program)

(defun deref-macro-name-list (fns macro-aliases)
  (if (endp fns)
      nil
    (cons (deref-macro-name (car fns) macro-aliases)
          (deref-macro-name-list (cdr fns) macro-aliases))))

(defun find-lemmas-fn (fns omit-boot-strap acc wrld-tail wrld)
  (declare (xargs :mode :program))
  (let ((fns (deref-macro-name-list fns (macro-aliases wrld))))
    (if (or (endp wrld-tail)
            (and omit-boot-strap
                 (and (eq (caar wrld-tail) 'command-landmark)
                      (eq (cadar wrld-tail) 'global-value)
                      (equal (access-command-tuple-form (cddar wrld-tail))
                             '(exit-boot-strap-mode)))))
        acc
      (let* ((trip (car wrld-tail))
             (ev-tuple (and (consp trip)
                            (eq (car trip) 'event-landmark)
                            (eq (cadr trip) 'global-value)
                            (cddr trip)))
             (type (and ev-tuple (access-event-tuple-type ev-tuple)))
             (namex (and type (access-event-tuple-namex ev-tuple)))
             (formula (and namex
                           (symbolp namex)
                           (member-eq type '(defthm defaxiom defchoose))
                           (formula namex t wrld))))
        (if (and formula
                 (subsetp-eq fns (all-fnnames formula)))
            (find-lemmas-fn fns omit-boot-strap
                            (cons (access-event-tuple-form ev-tuple) acc)
                            (cdr wrld-tail)
                            wrld)
          (find-lemmas-fn fns omit-boot-strap acc (cdr wrld-tail) wrld))))))

(defmacro find-lemmas (fns &optional (omit-boot-strap 't))
  (declare (xargs :guard (let ((fns (if (and (true-listp fns)
                                             (eq (car fns) 'quote)
                                             (eql (length fns) 2))
                                        (cadr fns)
                                      fns)))
                           (or (symbolp fns)
                               (symbol-listp fns)))))

; (find-lemmas (fn1 fn2 ...)) returns all lemmas in which all of the indicated
; function symbols occur, except those lemmas in the ground-zero world.  In
; order to include those as well, give a second argument of nil:
; (find-lemmas (fn1 fn2 ...) nil).

; If fns is a symbol, then fns is replaced by (list fns).

  (let ((fns (if (and (true-listp fns)
                      (eq (car fns) 'quote)
                      (eql (length fns) 2))
                 (cadr fns)
               fns)))
    (let ((fns (cond
                ((symbolp fns) (list fns))
                ((symbol-listp fns) fns)
                (t (er hard 'find-lemmas
                       "The first argument to find-lemmas must be a symbol or ~
                        a list of symbols, but ~x0 is not."
                       fns)))))
      `(find-lemmas-fn ',fns ',omit-boot-strap nil (w state) (w state)))))
