; Centaur Miscellaneous Books
; Copyright (C) 2008-2014 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(defvar *sneaky-state*
  (make-hash-table))

;; (defun sneaky-save (name what)
;;   (setf (gethash name *sneaky-load-table*) what)
;;   nil)

;; (defun sneaky-push (name what)
;;   (let ((val (gethash name *sneaky-load-table*)))
;;     (setf (gethash name *sneaky-load-table*)
;;           (cons what val)))
;;   nil)

;; (defun sneaky-incf-fn (name amount)
;;   (setf (gethash name *sneaky-load-table*)
;;         (+ (fix (gethash name *sneaky-load-table*))
;;            amount))
;;   nil)

(defun sneaky-load (name state)
  (unless (live-state-p state)
    (er hard? 'sneaky-load "sneaky-load should only be used on live states"))
  (let ((val (gethash name *sneaky-state*)))
    (mv val state)))

(defun sneaky-alist (state)
  (unless (live-state-p state)
    (er hard? 'sneaky-load "sneaky-load should only be used on live states"))
  (let (al)
    (maphash (lambda (k v)
               (push (cons k v) al))
             *sneaky-state*)
    (mv al state)))


(defun sneaky-mutate (fnname get-keys user-arg)
  (b* ((st *the-live-state*)
       (world (w st))
       (stobjs-in (fgetprop fnname 'stobjs-in :none world))
       (stobjs-out (fgetprop fnname 'stobjs-out :none world))
       ((when (not (equal stobjs-in '(nil nil))))
        (er hard 'sneaky-mutate
            "FNNAME must be an ACL2 function symbol of 2 non-stobj args; ~x0 is not~%"
            fnname))
       ((when (not (equal stobjs-out '(nil))))
        (er hard 'sneaky-mutate
            "FNNAME must be an ACL2 function symbol that returns a single value; ~x0 is not~%"
            fnname))
       (get-ins (loop for key in get-keys collect
                      (gethash key *sneaky-state*)))
       (starfn (*1*-symbol fnname))
       (result (funcall starfn get-ins user-arg)))
    (loop while (consp result) do
          (b* ((head (car result)))
            (when (consp head)
              (setf (gethash (car head) *sneaky-state*) (cdr head)))
            (setq result (cdr result))))
    nil))

(defun sneaky-delete (key)
  (remhash key *sneaky-state*)
  nil)

(defun sneaky-clear ()
  (setq *sneaky-state* (make-hash-table))
  nil)
