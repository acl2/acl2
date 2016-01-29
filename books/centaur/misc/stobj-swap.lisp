; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")


;; Defines a function that swaps the contents of two (congruent) stobjs.
;; Logically, just return one and the other.

;; Defines a function called swap-stobj1.  Stobj2 should be another stobj
;; declared congruent to stobj1.

;; Implementation note: ACL2 sometimes assumes that the stobj returned by a
;; form is the same object (i.e. pointer) as the corresponding stobj that was
;; input to that form.  E.g., stobj-let has an optimization that assumes stobj
;; fields that are updated do not actually need to be reinstalled in the stobj
;; that they came from -- it'll just be the same pointer, so reinstalling them
;; would be no-ops.  This has the consequence that we can't just do (in the raw
;; Lisp executable version of our swap) what we say we're doing in the non-exec
;; version, namely, return the pointers, just swapped.

(defmacro def-stobj-swap (stobj1 stobj2)
  (let* ((swap-nx (intern-in-package-of-symbol
                   (concatenate 'string "SWAP-" (symbol-name stobj1) "S-NX")
                   stobj1))
         (swap    (intern-in-package-of-symbol
                   (concatenate 'string "SWAP-" (symbol-name stobj1) "S")
                   stobj1)))
  `(progn
     (logic)
     (make-event
      (if (eq (congruent-stobj-rep ',stobj1 (w state))
              (congruent-stobj-rep ',stobj2 (w state)))
          '(value-triple :invisible)
        (er hard? 'def-stobj-swap
            "The two stobjs must be declared congruent to define a swapping function.~%")))
     (defun-nx ,swap-nx (,stobj1 ,stobj2)
       (declare (Xargs :stobjs (,stobj1 ,stobj2)))
       (mv ,stobj2 ,stobj1))
     (defun ,swap (,stobj1 ,stobj2)
       (declare (xargs :stobjs (,stobj1 ,stobj2)))
       (mv-let (,stobj1 ,stobj2)
         (,swap-nx ,stobj1 ,stobj2)
         (mv ,stobj1 ,stobj2)))
     (defttag ,swap)
     (progn!
      ;; [Jared] magic code that I don't understand at all, which hopefully makes it
      ;; OK to alter logic-fns-with-raw-code.
      :state-global-bindings
      ((temp-touchable-vars t set-temp-touchable-vars))
      ;; Mark swap as having raw code, so that :comp won't screw it up.
      (f-put-global 'logic-fns-with-raw-code
                    (cons ',swap (f-get-global 'logic-fns-with-raw-code state))
                    state)
      ;; Install the under the hood definition.
      (set-raw-mode t)
      (defun ,swap (,stobj1 ,stobj2)
        (let* ((bound (1- (length ,stobj1))))
          (loop for i from 0 to bound do
                (psetf (svref ,stobj1 i) (svref ,stobj2 i)
                       (svref ,stobj2 i) (svref ,stobj1 i)))
          (mv ,stobj1 ,stobj2)))))))
