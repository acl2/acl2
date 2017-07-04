; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, October, 2010
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Interface to some Lisp profilers

; Note: See also oprof.lisp (contributed by Jared Davis).

; This book provides profiling support for certain host Lisps.  Currently it
; supports only CCL and SBCL.  As of this writing (October 2010) it appears
; that profiling an entire package is much more efficient in SBCL than it is in
; CCL.

; Example usage:

; Probably preferred, but SBCL only: statistical call-graph profiling
; (with-sprofiling (mini-proveall)) ; SBCL only
; The following SBCL documentation may be helpful:
;   http://www.sbcl.org/manual/Statistical-Profiler.html

; Also supported:
; (with-profiling "ACL2" (mini-proveall)) ; efficient in SBCL, slow in CCL
; (with-profiling '(rewrite assoc-equal) (mini-proveall))

; This file defines the forms (with-sprofiling form) and (with-profiling fns
; form), under the above restrictions.

; You might prefer with-sprofiling, which shows a call-graph.  If you know of
; ways to improve that display, please feel free to contribute an improvement!

; In the case of with-profiling, fns is evaluated, and the result should be
; either a function symbol, a list of function symbols, or a package name.  The
; indicated symbols are profiled, where a package name indicates all function
; symbols in that package (not including symbols imported from another
; package).

(in-package "ACL2")

(defttag :profiling)

(set-state-ok t)

(defun with-profiling-ccl-dir-warning (prof-dir state)
  (declare (xargs :mode :program))
  (warning$ 'with-profiling nil
            "The CCL profiling routines used by books/misc/profiling.lisp ~
             depend on directory ~x0, which does not exist in your CCL ~
             distribution.  Such a directory exists in svn distributions of ~
             CCL and may appear in a future ccl-contrib github repository."
            prof-dir))

(defun with-profiling-ccl-dir (state)
  (declare (xargs :mode :program))
  (cond
   ((not (eq (f-get-global 'host-lisp state) :ccl))
    (er soft 'with-profiling
        "Function ~x0 should only be called when the host Lisp is CCL. ~
         Something is amiss!"
        'with-profiling-ccl-dir))
   (t (mv-let (erp ccl-dir state)
        (getenv$ "CCL_DEFAULT_DIRECTORY" state)
        (declare (ignore erp))
        (assert$
         ccl-dir
         (value (concatenate 'string
                             ccl-dir
                             "/contrib/huebner/advice-profiler/")))))))

(progn!
 (set-raw-mode t)
 (cond
  ((and (eq (f-get-global 'host-lisp state) :ccl)
        (not (eq (os (w state)) :mswindows)))
   (er-let* ((prof-dir (with-profiling-ccl-dir state)))
     (cond
      ((our-probe-file prof-dir)
       (prog2$
        (let ((*readtable* *host-readtable*))
          (load (concatenate 'string prof-dir "package.lisp"))
          (load (concatenate 'string prof-dir "profiler.lisp"))
          (load (concatenate 'string (cbd) "profiling-raw.lsp")))
        (value nil)))
      (t
       (with-profiling-ccl-dir-warning prof-dir state)

; The calls of error below avoid having to deal with multiple values, as is
; done by the uses of our-multiple-value-prog1 in profiling-raw.lsp.

       (eval `(defmacro with-profiling-raw (syms form)
                (declare (ignore syms form))
                '(progn
                   (with-profiling-ccl-dir-warning
                    ,prof-dir *the-live-state*)
                   (error "Directory does not exist (see warning above):~%~a"
                          ,prof-dir))))
       (eval '(defmacro with-sprofiling-internal-raw (options form)
                (declare (ignore options form))
                (error "The macro ~s does not do any profiling in CCL."
                       'with-sprofiling)))))))
  (t (load (concatenate 'string (cbd) "profiling-raw.lsp")))))

(defmacro-last with-profiling)

(defmacro-last with-sprofiling-internal)

(defmacro with-sprofiling (form &rest options)
  (let ((options (or options '(:report :graph :loop nil))))
    `(with-sprofiling-internal ',options ,form)))
