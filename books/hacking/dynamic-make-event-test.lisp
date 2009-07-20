(in-package "ACL2")
(include-book "defcode" :load-compiled-file :comp :ttags ((defcode)))
(include-book "rewrite-code" :load-compiled-file :comp)
(include-book "redefun" :load-compiled-file :comp)
(include-book "dynamic-make-event" :load-compiled-file :comp)

#|

dynamic-make-event-test.lisp
----------------------------

By Peter Dillinger, ca. 2009

This is a regression test for the dynamic-make-event book.

|#

(program)
(set-state-ok t)


(defttag dynamic-make-event-test) ; need to do some evil stuff

; Tweak defun so that if we try to defun THE-MAGIC-NAME, then it
; will instead expand to a definition of SOME-OTHER-NAME
(progn+touchable
 :all
 (redefun+rewrite
  defuns-fn
  (:carpat %body%
   :repl (if (eq (caar def-lst) 'the-magic-name)
           (dynamic-make-event-fn '(defun some-other-name (x) (1+ x))
				  event-form
				  state)
	   %body%)
   :vars (%body%))))

(defttag nil) ; end of evil stuff

; Now try it out ...

(defun the-magic-name (x) (1- x))
; should become (defun some-other-name (x) (1+ x))

; now we use some-other-name, to be sure it's now defined
(defun testing-function (x) (some-other-name x))

