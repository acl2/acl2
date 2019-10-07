; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "bvar-db")
(include-book "bfr")

(define bvar-db-bfrlist-aux ((n natp) bvar-db)
  :returns (bfrs)
  :measure (nfix (- (nfix n) (base-bvar bvar-db)))
  :guard (and (<= (base-bvar bvar-db) n)
              (<= n (next-bvar bvar-db)))
  (if (zp (- (lnfix n) (base-bvar bvar-db)))
      nil
    (append (fgl-object-bfrlist (get-bvar->term (1- (lnfix n)) bvar-db))
            (bvar-db-bfrlist-aux (1- (lnfix n)) bvar-db)))
  ///
  (defthm bfrlist-aux-of-get-bvar->term
    (implies (and (not (member v (bvar-db-bfrlist-aux n bvar-db)))
                  (< (nfix m) (nfix n))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (not (member v (fgl-object-bfrlist (get-bvar->term$a m bvar-db))))))

  (defthm bfrlist-aux-of-add-term-bvar
    (implies (<= (nfix n) (next-bvar$a bvar-db))
             (equal (bvar-db-bfrlist-aux n (add-term-bvar$a obj bvar-db))
                    (bvar-db-bfrlist-aux n bvar-db))))

  (defthm bfrlist-aux-of-update-term-equivs
    (equal (bvar-db-bfrlist-aux n (update-term-equivs$a obj bvar-db))
           (bvar-db-bfrlist-aux n bvar-db)))

  (defthm subsetp-bfrlist-of-bvar-db-bfrlist-aux
    (implies (and (< (nfix m) (nfix n))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (subsetp (fgl-object-bfrlist (get-bvar->term$a m bvar-db))
                      (bvar-db-bfrlist-aux n bvar-db)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))

(define bvar-db-bfrlist (bvar-db)
  (bvar-db-bfrlist-aux (next-bvar bvar-db) bvar-db)
  ///
  (defthm bfrlist-of-get-bvar->term
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (< (nfix m) (next-bvar$a bvar-db))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (not (member v (fgl-object-bfrlist (get-bvar->term$a m bvar-db))))))

  (defthm bvar-db-bfrlist-of-add-term-bvar
    (equal (bvar-db-bfrlist (add-term-bvar$a obj bvar-db))
           (append (fgl-object-bfrlist obj)
                   (bvar-db-bfrlist bvar-db)))
    :hints (("goal" :in-theory (enable bvar-db-bfrlist-aux))))

  (defthm subsetp-bfrlist-of-bvar-db-bfrlist
    (implies (and (< (nfix m) (next-bvar$a bvar-db))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (subsetp (fgl-object-bfrlist (get-bvar->term$a m bvar-db))
                      (bvar-db-bfrlist bvar-db))))

  (defthm bvar-db-bfrlist-of-add-term-bvar-unique
    (acl2::set-equiv (bvar-db-bfrlist (mv-nth 1 (add-term-bvar-unique obj bvar-db)))
                     (append (fgl-object-bfrlist obj)
                             (bvar-db-bfrlist bvar-db)))
    :hints (("goal" :in-theory (e/d (add-term-bvar-unique)
                                    (bvar-db-bfrlist
                                     subsetp-bfrlist-of-bvar-db-bfrlist))
             :use ((:instance subsetp-bfrlist-of-bvar-db-bfrlist
                    (m (get-term->bvar$a obj bvar-db))))))))
