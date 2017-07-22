; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, October, 2010
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See profiling.lisp for information on how to use with-profiling.

; We have seen problems on Windows CCL, so we avoid Windows here for CCL.  It
; would be great if someone cares to look into this.

(in-package "ACL2")

; May be needed with Linux (gb suggestion):
#+(and ccl (not mswindows))
(ignore-errors (profiler::open-shared-library "librt.so"))

#+(or (and (not mswindows) ccl) sbcl)
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

(defmacro with-profiling-no-op-warning (macro-name supported-lisps form)
  `(let ((state *the-live-state*))
     (case (f-get-global 'host-lisp state)
       (,supported-lisps state)
       (t (warning$ ',macro-name nil
                    "The macro ~x0 does not do any profiling in this host ~
                     Lisp and OS:~|  ~x1 = ~x2.~|  ~x3 = ~x4"
                    ',macro-name
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
          ',macro-name nil
          "To repeat the warning above:  The macro ~x0 does not do any ~
           profiling on this host Lisp and platform."
          ',macro-name)))))

#-(or (and (not mswindows) ccl) sbcl)
(defmacro with-profiling-raw (syms form)
  (declare (ignore syms))
  `(with-profiling-no-op-warning with-profiling (:ccl :sbcl) ,form))

#+sbcl
(require :sb-sprof)

#+(and sbcl acl2-mv-as-values)
; We expect acl2-mv-as-values to be set for every sbcl installation these days
; (June 2011).  If not, someone can complain and we can fix this.
(defmacro with-sprofiling-internal-raw (&whole whole options form)

; A good value for options is (:report :graph :loop nil).  See
; http://www.sbcl.org/manual/Statistical-Profiler.html for other possibilities.

  (let ((result-var (gensym)))
    `(let ((sb-sprof::*report-sort-by* :cumulative-samples)
           (sb-sprof::*report-sort-order* :descending)
           ,result-var)
       (sb-sprof::with-profiling
        ,(eval options)
        (progn (setq ,result-var
                     (multiple-value-list ,form))
               (format t "~%*** SEE BELOW FOR PROFILING RESULTS. ***")))
       (format t "~%")
       (values-list ,result-var))))

#-(and sbcl acl2-mv-as-values)
(defmacro with-sprofiling-internal-raw (options form)
  (declare (ignore options))
  `(with-profiling-no-op-warning with-sprofiling (:sbcl) ,form))
