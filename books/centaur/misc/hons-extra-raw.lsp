; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")


(defun hl-hspace-normedp (x hs)

; (HL-HSPACE-NORMEDP X HS) --> BOOL
;
; X may be any ACL2 Object and HS is a Hons Space.  We determine if X is normed
; with respect to HS.

  (declare (type hl-hspace hs))
  (cond ((consp x)
         (hl-hspace-honsp x hs))
        ((stringp x)
         (let* ((str-ht (hl-hspace-str-ht hs))
                (entry  (gethash x str-ht)))
           (and entry
                #+static-hons
                (eq x (car entry))
                #-static-hons
                (eq x entry))))
        (t
         t)))

(defun hl-make-fast-alist-check (alist hs)

; Return the longest tail of alist in which all keys are normed.
;   ** may install a new ADDR-HT, SBITS
;   ** callers should not have ADDR-HT or SBITS let-bound!

  (declare (type hl-hspace hs))
  (let ((ok-tail alist))
    ;; ok-tail is a tail of alist on which we haven't yet found any unnormed keys.
    (loop for tail on alist while (consp tail) do
          (let ((pair (car tail)))
            (when (and (consp pair)
                       (not (hl-hspace-normedp (car pair) hs)))
              (setq ok-tail (cdr tail)))))
    ok-tail))

(defun hl-make-fast-norm-keys (alist tail hs)

; Makes a copy of alist in which all keys are normed, assuming all keys are
; normed in tail.
;   ** may install a new ADDR-HT, SBITS
;   ** callers should not have ADDR-HT or SBITS let-bound!

  (declare (type hl-hspace hs))
  (if (eq tail alist)
      alist
    (let* ((first-cons (list nil))
           (last-cons first-cons))
      (loop for rest on alist
            while (and (consp rest) (not (eq rest tail)))
            do
            (let* ((pair (car rest))
                   (cons (list (if (consp pair)
                                   (cons (hl-hspace-norm (car pair) hs) (cdr pair))
                                 pair))))
              (setf (cdr last-cons) cons)
              (setq last-cons cons)))
      (setf (cdr last-cons) tail)
      (cdr first-cons))))

(defun hl-make-fast-alist-put-pairs (alist ht)

; Puts the pairs in alist into table, ensuring that the first ones bound mask
; later ones.

  (declare (type hash-table ht))
  (loop for rest on alist while (consp rest) do
        (let ((pair (car rest)))
          (when (and (consp pair)
                     (not (gethash (car pair) ht)))
            (setf (gethash (car pair) ht) pair)))))

(defun hl-hspace-make-fast-alist (alist hs)

; This function ensures that there is a backing hash table for alist.  It
; returns either alist itself or an EQUAL copy.
;   ** may install a new ADDR-HT, SBITS
;   ** callers should not have ADDR-HT or SBITS let-bound!

  (declare (type hl-hspace hs))
  ;; If alist is an atom, we're done.
  (if (atom alist)
      alist
    ;; If the alist already has an associated hash table, we're also done.
    (let* ((faltable    (hl-hspace-faltable hs))
           (slot        (hl-faltable-general-lookup alist faltable))
           (alist-table (hl-falslot-val slot)))
      (if alist-table
          alist
        (let* (;; Find the largest tail of alist in which all keys are normed.
               (tail (hl-make-fast-alist-check alist hs))
               ;; Makes a copy of alist in which all keys are normed.
               (alist (hl-make-fast-norm-keys alist tail hs)))
          ;; We need to make a new hash table to back ALIST.  As in
          ;; hl-hspace-shrink-alist, we choose a size of
          ;; (max 60 (* 1/8 length)).
          (setq alist-table
                (hl-mht :size (max 60 (ash (len alist) -3))))
          (hl-make-fast-alist-put-pairs alist alist-table)
          ;; The slot is empty, so install everything.  Since the value wasn't
          ;; found, the initial ALIST isn't bound; if we ended up making a new
          ;; alist due to honsing any keys, it's also not bound because we used
          ;; cons.  So, uniqueness is guaranteed.  And we already know from the
          ;; general lookup that it is unique.
          (setf (hl-falslot-val slot) alist-table)
          (setf (hl-falslot-key slot) alist)
          alist)))))


(defun make-fast-alist (alist)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-make-fast-alist alist *default-hs*))



(defmacro with-fast-alist-raw (alist form)
  (let ((alist-was-fast-p (gensym))
        (alist-var (if (legal-variablep alist)
                       alist
                     (gensym))))
    `(b* ((- (hl-maybe-initialize-default-hs))
          ;; If alist isn't a variable, then depend on it being a computation
          ;; that returns the same (eq) object each time, and that object can
          ;; be turned into an (eq) fast alist, i.e. its keys are normed.  If
          ;; not, then the user may not find their alist to be fast during the
          ;; execution of form, but we'll still correctly free it.
          (,alist-var ,alist)
          (,alist-was-fast-p
           (let ((slot (hl-faltable-general-lookup ,alist-var (hl-hspace-faltable *default-hs*))))
             (if (hl-falslot-key slot)
                 t
               nil)))
          (,alist-var (if ,alist-was-fast-p
                          ,alist-var
                        (make-fast-alist ,alist-var))))
       (our-multiple-value-prog1
        ,form
        (if ,alist-was-fast-p
            nil
          (fast-alist-free ,alist-var))))))

