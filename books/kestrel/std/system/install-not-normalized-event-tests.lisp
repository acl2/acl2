; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "install-not-normalized-event")

(include-book "theorem-namep")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (install-not-normalized-event 'f nil nil (w state)))
              '((install-not-normalized f
                                        :defthm-name 'f$not-normalized
                                        :allp nil)
                f$not-normalized))

(assert-equal (mv-list 2 (install-not-normalized-event 'g t nil (w state)))
              '((local
                 (install-not-normalized g
                                         :defthm-name 'g$not-normalized
                                         :allp nil))
                g$not-normalized))

(assert-equal (mv-list 2 (install-not-normalized-event 'f nil '(a b) (w state)))
              '((install-not-normalized f
                                        :defthm-name 'f$not-normalized
                                        :allp nil)
                f$not-normalized))

(assert-equal (mv-list 2 (install-not-normalized-event
                          'f nil '(a f$not-normalized) (w state)))
              '((install-not-normalized f
                                        :defthm-name 'f$not-normalized$
                                        :allp nil)
                f$not-normalized$))

(must-succeed*
 (defun f$not-normalized (x) x)
 (assert-equal (mv-list 2 (install-not-normalized-event 'f nil nil (w state)))
               '((install-not-normalized f
                                         :defthm-name 'f$not-normalized$
                                         :allp nil)
                 f$not-normalized$)))

(must-succeed*
 (defun f$not-normalized (x) x)
 (defun f$not-normalized$ (x) x)
 (assert-equal (mv-list 2 (install-not-normalized-event 'f nil nil (w state)))
               '((install-not-normalized f
                                         :defthm-name 'f$not-normalized$$
                                         :allp nil)
                 f$not-normalized$$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (make-event
  (b* (((mv event &)
        (install-not-normalized-event 'f nil nil (w state))))
    event))
 (assert! (theorem-namep 'f$not-normalized (w state))))

(must-succeed*
 (defun g (x) x)
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (install-not-normalized-event 'g t nil (w state))))
      event))
   (assert! (theorem-namep 'g$not-normalized (w state))))
 (assert! (not (theorem-namep 'g$not-normalized (w state)))))

(must-succeed*
 (defun f (x) x)
 (make-event
  (b* (((mv event &)
        (install-not-normalized-event 'f nil '(a b) (w state))))
    event))
 (assert! (theorem-namep 'f$not-normalized (w state))))

(must-succeed*
 (defun f (x) x)
 (make-event
  (b* (((mv event &)
        (install-not-normalized-event
         'f nil '(a f$not-normalized) (w state))))
    event))
 (assert! (theorem-namep 'f$not-normalized$ (w state))))

(must-succeed*
 (defun f (x) x)
 (defun f$not-normalized (x) x)
 (make-event
  (b* (((mv event &)
        (install-not-normalized-event 'f nil nil (w state))))
    event))
 (assert! (theorem-namep 'f$not-normalized$ (w state))))

(must-succeed*
 (defun f (x) x)
 (defun f$not-normalized (x) x)
 (defun f$not-normalized$ (x) x)
 (make-event
  (b* (((mv event &)
        (install-not-normalized-event 'f nil nil (w state))))
    event))
 (assert! (theorem-namep 'f$not-normalized$$ (w state))))
