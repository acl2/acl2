#|$ACL2s-Preamble$;
(ld ;; Newline to fool dependency scanner
   "hacker-pkg.lsp")

(include-book ;; Newline to fool dependency scanner
  "defcode" :ttags ((defcode)))

(acl2::begin-book t :ttags ((defcode)));$ACL2s-Preamble$|#

(in-package "ACL2")

(program)
(set-state-ok t)

; convert (declare (...)) or ((...)) or (...) into (declare (...))
(defun reconstruct-declare-lst (spec)
  (cond ((atom spec) nil)
        ((eq 'declare (car spec))
         (list spec))
        ((consp (car spec))
         (list (cons 'declare spec)))
        (t
         (list (list 'declare spec)))))

; for public use
(defmacro defun-bridge (name ll
                        &key (loop '() loop-p)
                             (loop-declare '())
                             (doc '())
                             (raw '() raw-p)
                             (raw-declare '()))

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; define a function that bridges ACL2 with raw Lisp.~/

; ~bv[]
; General Form:
; (defun-bridge ~i[name] (~i[formals])
;   [:doc ~i[doc-string]]
;   [:loop-declare ~i[loop-decls]]
;   :loop ~i[loop-body]
;   [:raw-declare ~i[raw-decls]]
;   :raw ~i[raw-body])
; ~ev[] ~/
;
; This is much like executing
; ~bv[]
; (defun ~i[name] (~i[formals])
;   ~i[doc-string]
;   ~i[loop-decls]
;   ~i[loop-body])
; ~ev[]
; in ACL2 and then
; ~bv[]
; (defun ~i[name] (~i[formals])
;   ~i[raw-decls]
;   ~i[raw-body])
; ~ev[]
; in raw Lisp, except that extra checks and bookkeeping make it safer
; than that.
;
; An active ttag is required to use this form (~l[defttag]), because
; it can easily corrupt ACL2 or render it unsound.
; ~/"
  (declare (xargs :guard (and loop-p
                              raw-p
                              (implies doc
                                       (stringp doc))))
           (ignorable loop-p raw-p))
  (let*
    ((ignorable-decl-lst
      (and ll `((declare (ignorable . ,ll)))))
     (loop-def-lst
      `((defun ,name
          ,ll
          ,@ (and doc (list doc))
          ,@ ignorable-decl-lst
          ,@ (reconstruct-declare-lst loop-declare)
          ,loop)))
     (raw-def-lst
      `((defun ,name ,ll
          ,@ ignorable-decl-lst
          ,@ (reconstruct-declare-lst raw-declare)
          ,raw)
        (defun-*1* ,name ,ll
                   (if (f-get-global 'safe-mode *the-live-state*)
                     (throw-raw-ev-fncall (list 'program-only-er ',name
                                                (list . ,ll) 't '(nil) t))
                     (,name . ,ll))))))
  `(progn
    (assert-unbound ,name)
    (ensure-program-only-flag ,name)
    (ensure-special-raw-definition-flag ,name)
    (defcode
     :loop ,loop-def-lst
     :extend (in-raw-mode . ,raw-def-lst)
     :compile ,raw-def-lst))))


; tests and stuff:

#|
(include-book
 "defcode" :ttags ((defcode)))
(defttag t)
(defun-bridge foo (x)
  :loop x
  :raw (progn (format t "~a~%" x)
              x))

(foo 42)
(set-guard-checking :none)
(foo 42)
(defmacro bar ()
  (foo nil))
(bar) ; error
|#
