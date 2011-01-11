; See profiling.lisp for information on how to use with-profiling.

; We have seen problems on Windows CCL, so we avoid Windows here.  It would be
; great if someone cares to look into this.

(in-package "ACL2")

#+(and ccl (not mswindows))
(let ((ccl-dir (ccl::getenv "CCL_DEFAULT_DIRECTORY"))
      (*readtable* *host-readtable*))
  (assert ccl-dir)
  (let ((prof-dir (concatenate 'string
                               ccl-dir
                               "/contrib/huebner/advice-profiler/")))
    (load (concatenate 'string prof-dir "package.lisp"))
    (load (concatenate 'string prof-dir "profiler.lisp"))))

; May be needed with Linux (gb suggestion):
#+(and ccl (not mswindows))
(ignore-errors (profiler::open-shared-library "librt.so"))

#+(and (not mswindows) (or ccl sbcl))
(defmacro with-profiling-raw (syms form)
  (let ((prof #+ccl 'profiler::profile
              #+sbcl 'sb-profile:profile)
        (unprof #+ccl 'profiler::unprofile
                #+sbcl 'sb-profile:unprofile)
        (reset #+ccl 'profiler::reset
               #+sbcl 'sb-profile:reset)
        (report #+ccl 'profiler::report
                #+sbcl 'sb-profile:report))
    `(let* ((syms ,syms)
            (pkg-p (and (stringp syms)
                        (find-package syms)))
            #+ccl
            (pkg-fns (and pkg-p ; else not needed
                          (profiler::functions-in-package syms nil)))
            (profiled-fns #+ccl profiler::*profiled-functions*
                          #+sbcl (,prof))
            (unprof-fns
             (set-difference-eq
              (cond ((and syms (symbolp syms))
                     (list syms))
                    ((symbol-listp syms)
                     syms)
                    (t             ; package name
                     #+ccl pkg-fns ; optimization over profiled-fns
                     #+sbcl (,prof)))
              profiled-fns)))
       (unwind-protect
           (progn
             (,reset)
             (cond ((and syms (symbolp syms))
                    (eval (list ',prof syms)))
                   ((symbol-listp syms)
                    (eval (cons ',prof syms)))
                   ((not pkg-p)
                    (error
                     "The first argument of with-profiling-raw must ~%~
                      evaluate to a symbol, a true list of symbols, or a ~%~
                      package name.  The argument ~s is thus illegal."
                           syms))
                   (t
                    #+sbcl ; can take a package name
                    (eval (list ',prof syms))
                    #+ccl

; It is tempting to simplify the code below, simply to: (eval (list
; 'profiler::profile-package syms)).  However, that seems to run more slowly
; than this code, at least for the "ACL2" package; and besides, we want to
; print a notice to the user about possibly having to wait.

                    (progn
                      (let ((len (length pkg-fns)))
                        (when (< 100 len)
                          (format
                           t
                           "Profiling ~s functions, which could take awhile.  (We~%~
                      have seen the \"ACL2\" package take about a minute.)~%"
                           len)))
                      (eval (cons 'progn
                                  (loop for fn in pkg-fns collect
                                        (list ',prof fn)))))))
             (our-multiple-value-prog1
              ,form

; If we replace the following call of format with a form that calls any ACL2
; function, consider using protect-mv; see our-multiple-value-prog1.

              (format
               t
               "~%### Evaluation completed.  Computing report....~%~%")))
         (unwind-protect
             (,report)
           (eval (cons ',unprof unprof-fns)))))))

#-(and (not mswindows) (or ccl sbcl))
(defmacro with-profiling-raw (syms form)
  `(with-live-state
    (progn
      ,syms ; evaluate both arguments, not just form
      (case (f-get-global 'host-lisp state)
        ((:ccl :sbcl) state)
        (t (warning$ 'with-profiling nil
                     "The macro WITH-PROFILING does not do any profiling in ~
                      this host Lisp and OS:~|  ~x0 = ~x1.~|  ~x2 = ~x3"
                     '(f-get-global 'host-lisp state)
                     (f-get-global 'host-lisp state)
                     '(os (w state))
                     (os (w state)))))
      (our-multiple-value-prog1
       ,form

; The second warning, below, looks silly when we evaluate a form that doesn't
; have output.  But otherwise, we think it prudent to print it, since warnings
; are easy to miss and something like (with-profiling "ACL2" (mini-proveall))
; could frustrate the user if there isn't a warning at the bottom of the
; window.  Anyhow, we don't expect a lot of use of with-profiling in Lisps for
; which we don't support profiling; the extra warning might actually encourage
; people to avoid such futile attempts.

       ,(protect-mv
         `(warning$
           'with-profiling nil
           "To repeat the warning above:  The macro WITH-PROFILING does not ~
            do any profiling on this host Lisp and platform."))))))
