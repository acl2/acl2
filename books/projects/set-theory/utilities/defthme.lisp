; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Zf::defthme is used much like zf::defthme, except that it tries to do a bit
; automatically and it can print lemmas that would allow that automation to
; complete.  This tool is under development and will probably be documented if
; it proves to be reasonably useful.

(in-package "ACL2")

(defconst *defthme-skip-keywords*
  '(:f :b))

(defun defthme-skip (ctx x)
  (declare (xargs :guard t))
  (cond ((eq x :print)
         :print)
        ((eq x :all)
         *defthme-skip-keywords*)
        ((keywordp x)
         (list x))
        ((and (true-listp x)
              (subsetp-eq x *defthme-skip-keywords*))
         x)
        (t (er hard? ctx
               "Illegal :skip value: ~x0"
               x))))

(defmacro try-cmd (cmd)
  `(make-event
    '(:or ,cmd
          (progn (table try-cmd-table t
                        (cons ',cmd
                              (cdr (assoc-eq t (table-alist 'try-cmd-table
                                                            world)))))
                 (skip-proofs ,cmd)))
    :expansion? ,cmd))

(defun maybe-skip-or-try (k skip try x)
  (declare (xargs :guard (and (member-eq k *defthme-skip-keywords*)
                              (or (eq skip :print)
                                  (true-listp skip))
                              (true-listp try))))
  (cond
   ((eq skip :print)
    x)
   ((member-eq k skip)
    `(skip-proofs ,x))
   ((member-eq k try)
    `(try-cmd ,x))
   (t x)))

(defmacro skipped-in-try-cmd-table ()
  '(value-triple
    (let ((skipped
           (cdr (assoc-eq t (table-alist 'acl2::try-cmd-table (w state))))))
      (if skipped
          (with-output :stack :pop
            (state-global-let*
             ((print-case :downcase))
             (pprogn (fms "----------~%Skipped events:~%----------~%~*0~|"
                          (list (cons #\0 (list ""
                                                "~x*"
                                                "~x*"
                                                "~x*"
                                                skipped)))
                          (standard-co state) state nil)
                     (silent-error state))))
        (value :success)))
    :stobjs-out '(nil nil state)))

(defun make-implies (hyps concl)
  (declare (xargs :guard (true-listp hyps)))
  (cond ((null hyps) concl)
        ((null (cdr hyps))
         `(implies ,(car hyps) ,concl))
        (t
         `(implies (and ,@hyps) ,concl))))

(defmacro zf::defthme (name form
                            &key
                            forward backward
                            skip ; :print, :all, or a sublsit of (:f :b)
                            (var 'zf::elt)
                            (try '(:f :b))
                            verbose
                            (props '(zf::zfc)))
  (declare (xargs :guard (and (symbolp name)
                              (keyword-value-listp forward)
                              (keyword-value-listp backward)
                              (symbol-listp props))))
  (let* ((skip (defthme-skip `(zf::defthme . ,name) skip))
         (sname (symbol-name name))
         (namef (intern-in-package-of-symbol
                 (concatenate 'string sname "-FORWARD")
                 name))
         (nameb (intern-in-package-of-symbol
                 (concatenate 'string sname "-BACKWARD")
                 name)))
    (mv-let (hyps lhs rhs)
      (case-match form
        (('implies ('and . hyps)
                   ('equal lhs rhs))
         (mv hyps lhs rhs))
        (('implies hyp
                   ('equal lhs rhs))
         (mv (list hyp) lhs rhs))
        (('equal lhs rhs)
         (mv nil lhs rhs))
        (& (mv (er hard 'zf::defthme
                   "Unrecognized shape for defthme!")
               nil nil)))
      (let* ((forward
              `(zf::defthmdz ,namef
                            ,(make-implies (append hyps
                                                   `((zf::in ,var ,lhs)))
                                           `(zf::in ,var ,rhs))
                            ,@forward
                            :props ,props))
             (backward
              `(zf::defthmdz ,nameb
                            ,(make-implies (append hyps
                                                   `((zf::in ,var ,rhs)))
                                           `(zf::in ,var ,lhs))
                            ,@backward
                            :props ,props))
             (forms
              `(,(maybe-skip-or-try :f skip try forward)
                ,(maybe-skip-or-try :b skip try backward)
                (zf::defthmz ,name ,form
                             :hints
                             (("Goal"
                               :in-theory (union-theories
                                           '(zf::extensionality
                                             ,namef
                                             ,nameb)
                                           (theory 'minimal-theory))
                               :expand ((zf::subset ,lhs ,rhs)
                                        (zf::subset ,rhs ,lhs))))
                             :props ,props))))
        (cond ((eq skip :print)
               `(pprogn (fms "~*0~|"
                             (list (cons #\0
                                         '(""
                                           "~x*"
                                           "~x*"
                                           "~x*"
                                           ,forms)))
                             (standard-co state) state nil)
                        (value :invisible)))
              (t
               (let ((x `(progn ,@forms
                                (skipped-in-try-cmd-table))))
                 (cond (verbose x)
                       (t `(with-output
                             :stack :push :off :all
                             ,x))))))))))
