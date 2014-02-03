; NREV - A "safe" implementation of something like nreverse
; Copyright (C) 2014 Centaur Technology
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

(in-package "NREV")

; Basic implementation:
;
;  ACC is NIL == We have the empty list.
;
;  ACC is (CONS HEAD TAIL) otherwise, where:
;
;     HEAD points at the list which has been constructed IN ORDER and hence
;          does not need to be reversed
;
;     TAIL points at its tail, so we can rplacd things in as needed.

(defun nrev$c-copy (nrev$c)
  (let* ((acc  (nrev$c-acc nrev$c))
         (head (car acc)))
    ;; We must make a deep copy of the elements, because otherwise our next
    ;; PUSH would extend a list that someone else has gotten hold of.
    (loop for e in head collect e)))

(defun nrev$c-finish (nrev$c)
  (let* ((acc    (nrev$c-acc nrev$c))
         (head   (car acc))
         (nrev$c (update-nrev$c-acc nil nrev$c)))
    ;; No need to deep copy; nobody else has a handle to our conses.
    (mv head nrev$c)))

(defun nrev$c-push (a nrev$c)
  (let* ((acc      (nrev$c-acc nrev$c))
         (new-cons (cons a nil)))
    (if (atom acc)
        (update-nrev$c-acc (cons new-cons new-cons) nrev$c)
      (let* ((tail (cdr acc)))
        #+hons (acl2::memoize-flush nrev$c)
        (rplacd tail new-cons)
        (rplacd acc new-cons)
        nrev$c))))
