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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; This book proves that F-PUT-GLOBAL preserves STATE-P1, allowing it to be
;; used in guard-verified recursive logic-mode functions.

(local
 (progn
   (defthm all-boundp-add-pair
     (implies (all-boundp al1 al2)
              (all-boundp al1 (add-pair kay val al2))))

   (in-theory (disable all-boundp add-pair))

   (in-theory (disable open-channels-p
                       ordered-symbol-alistp
                       plist-worldp
                       symbol-alistp
                       timer-alistp
                       known-package-alistp
                       true-listp
                       32-bit-integer-listp
                       integer-listp
                       file-clock-p
                       readable-files-p
                       written-files-p
                       read-files-p
                       writeable-files-p
                       true-list-listp))))

(defund state-p1-good-worldp (world)
  (and (plist-worldp world)
       (symbol-alistp
        (getprop 'acl2-defaults-table
                 'table-alist
                 nil 'current-acl2-world
                 world))
       (known-package-alistp
        (getprop 'known-package-alist
                 'global-value
                 nil 'current-acl2-world
                 world))))

(defthm state-p1-put-global
  (implies (and (state-p1 state)
                (symbolp key)
                (cond ((eq key 'current-acl2-world) (state-p1-good-worldp val))
                      ((eq key 'timer-alist) (timer-alistp val))
                      (t)))
           (state-p1 (put-global key val state)))
  :hints(("Goal" :in-theory (enable state-p1 state-p1-good-worldp))))

(defthm assoc-equal-add-pair
  (equal (assoc-equal k1 (add-pair k2 v al))
         (if (equal k1 k2)
             (cons k2 v)
           (assoc-equal k1 al)))
  :hints(("Goal" :in-theory (enable add-pair))))

(defthm get-global-of-put-global
  (equal (get-global k1 (put-global k2 val state))
         (if (equal k1 k2)
             val
           (get-global k1 state))))

(defthm boundp-global1-of-put-global
  (equal (boundp-global1 k1 (put-global k2 val state))
         (or (equal k1 k2)
             (boundp-global1 k1 state))))

(in-theory (disable boundp-global1 get-global put-global))
