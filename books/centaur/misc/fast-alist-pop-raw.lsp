; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; fast-alist-pop.lisp
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(defun hl-hspace-fast-alist-pop (alist hs)
  (declare (type hl-hspace hs))
  (if (atom alist)
      ;; Nothing to do, no fast alist can be bound to an atom.
      nil
    (let* ((faltable (hl-hspace-faltable hs))
           (slot     (hl-faltable-general-lookup alist faltable))
           (val      (hl-falslot-val slot))
           (ans      (cdr alist)))
      (cond ((not val)
             ;; Discipline failure, no valid backing alist.
             (hl-slow-alist-warning 'hl-hspace-fast-alist-pop))
            ((atom ans)
             ;; This is fine, but we maintain an invariant that we never
             ;; bind an atom to a hash table.  So, we just need to free
             ;; the hash table at this point.
             (hl-faltable-remove alist faltable))
            (t
             ;; Break the old association from ALIST to VAL.
             (setf (hl-falslot-key slot) nil)
             ;; If the car is an atom, we must not do anything to the backing
             ;; hash.  Otherwise, remove the key of the first pair from the
             ;; backing hash table.  Note that we don't need to hons the key
             ;; we're removing, because we're in the case where this is a
             ;; valid fast alist, hence all of its keys must be normed.
             (when (consp (car alist))
               (remhash (caar alist) (the hash-table val)))
             ;; Associate the resulting ANS with the updated VAL (which is
             ;; already in the slot).
             (setf (hl-falslot-key slot) ans)))
      ans)))

(defun hl-hspace-fast-alist-pop* (prev-binding alist hs)
  (declare (type hl-hspace hs))
  (if (atom alist)
      ;; Nothing to do, no fast alist can be bound to an atom.
      nil
    (let* ((faltable (hl-hspace-faltable hs))
           (slot     (hl-faltable-general-lookup alist faltable))
           (val      (hl-falslot-val slot))
           (ans      (cdr alist)))
      (cond ((not val)
             ;; Discipline failure, no valid backing alist.
             (hl-slow-alist-warning 'hl-hspace-fast-alist-pop*))
            ((atom ans)
             ;; This is fine, but we maintain an invariant that we never
             ;; bind an atom to a hash table.  So, we just need to free
             ;; the hash table at this point.
             (hl-faltable-remove alist faltable))
            (t
             ;; Break the old association from ALIST to VAL.
             (setf (hl-falslot-key slot) nil)

             ;; If the car is an atom, we must not do anything to the backing
             ;; hash.  Otherwise, if the prev-binding is NIL we remove the
             ;; binding of the key in the backing hash, else we smash its
             ;; current value with its previous binding.
             (when (consp (car alist))
               (if prev-binding
                   (setf (gethash (caar alist) (the hash-table val))
                         prev-binding)
                 (remhash (caar alist) (the hash-table val))))
             ;; Associate the resulting ANS with the updated VAL (which is
             ;; already in the slot).
             (setf (hl-falslot-key slot) ans)))
      ans)))

;; BOZO fast-alist-pop is really just fast-alist-pop* with prev-binding=NIL.
(defun fast-alist-pop (x)
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-pop x *default-hs*))

(defun fast-alist-pop* (prev-binding x)
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-pop* prev-binding x *default-hs*))


#|
; Note: The set-w form after this comment fixes the following soundness bug,
; which works by screwing up invariants with program mode code:

(defconst *alist1*
  (hons-acons 'a 2 nil))

(defconst *alist2*
  (hons-acons 'a 1 *alist1*))

(defun f (x)
  (declare (xargs :mode :program))
  (fast-alist-pop x))

(make-event
 (b* ((?screw-things-up (f *alist2*)))
   '(value-triple :oops)))

(defthmd lemma1
  (equal (hons-get 'a *alist1*) nil)
  :hints(("Goal" :in-theory (executable-counterpart-theory :here))))

(defthmd lemma2
  (equal (hons-get 'a *alist1*) '(a . 2))
  :hints(("Goal" :in-theory (e/d (hons-get hons-assoc-equal)
                                 ((:e hons-get))))))

(defthm darn-it
  nil
  :rule-classes nil
  :hints(("Goal" :Use ((:instance lemma1)
                       (:instance lemma2)))))

|#

(set-w 'extension
       (putprop 'fast-alist-pop 'invariant-risk 'fast-alist-pop
                (w *the-live-state*))
       *the-live-state*)

(f-put-global 'logic-fns-with-raw-code
              (cons 'fast-alist-pop
                    (f-get-global 'logic-fns-with-raw-code state))
              *the-live-state*)
