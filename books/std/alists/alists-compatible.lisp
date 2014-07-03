; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")
(include-book "alist-equiv")
(local (include-book "hons-assoc-equal"))
(local (include-book "../lists/list-fix"))

(defun alists-compatible-on-keys (keys a b)
  (declare (xargs :guard t))
  (or (atom keys)
      (and (let ((alook (hons-get (car keys) a))
                 (blook (hons-get (car keys) b)))
             (or (not alook) (not blook) (equal alook blook)))
           (alists-compatible-on-keys (cdr keys) a b))))

(defthm alists-compatible-on-keys-of-list-fix
  (equal (alists-compatible-on-keys (list-fix keys) a b)
         (alists-compatible-on-keys keys a b)))

(defcong list-equiv equal (alists-compatible-on-keys keys a b) 1
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (alists-compatible-on-keys-of-list-fix))
          :use ((:instance alists-compatible-on-keys-of-list-fix
                           (keys keys))
                (:instance alists-compatible-on-keys-of-list-fix
                           (keys keys-equiv))))))



(defund alists-compatible (a b)
  (declare (xargs :guard t))
  (alists-compatible-on-keys (alist-keys a) a b))

(local (defthm member-intersection
         (iff (member x (intersection-equal a b))
              (and (member x a)
                   (member x b)))))

(defthmd alists-compatible-on-keys-in-terms-of-alists-agree
  (equal (alists-compatible-on-keys keys a b)
         (alists-agree (intersection-equal keys
                                           (intersection-equal (alist-keys a)
                                                               (alist-keys b)))
                       a b))
  :hints(("Goal" :in-theory (enable alists-compatible-on-keys
                                    alists-agree
                                    alist-keys
                                    intersection-equal)))
  :rule-classes :definition)

(local (defthm intersection-equal-repeat-1
         (implies (subsetp-equal a b)
                  (equal (intersection-equal a (intersection-equal b c))
                         (intersection-equal a c)))
         :hints(("Goal" :in-theory (enable intersection-equal)))))

(local (defthm subsetp-equal-cons
         (implies (subsetp-equal a b)
                  (subsetp-equal a (cons x b)))))

(local (defthm subsetp-equal-refl
         (subsetp-equal a a)))

(local (defthm intersection-equal-repeat
         (equal (intersection-equal a (intersection-equal a c))
                (intersection-equal a c))))

(defthmd alists-compatible-in-terms-of-alists-agree
  (equal (alists-compatible a b)
         (alists-agree (intersection-equal (alist-keys a)
                                           (alist-keys b))
                       a b))
  :hints(("Goal" :in-theory (enable alists-compatible
                                    alists-compatible-on-keys-in-terms-of-alists-agree
                                    alists-agree
                                    alist-keys
                                    intersection-equal)))
  :rule-classes :definition)

(local (in-theory (enable alists-compatible-in-terms-of-alists-agree)))

(defund alists-incompatible-witness (a b)
  (alists-disagree-witness
   (intersection-equal (alist-keys a) (alist-keys b))
   a b))

(local (in-theory (enable alists-incompatible-witness)))

(local (defthm member-intersection-equal
         (iff (member x (intersection-equal a b))
              (and (member x a) (member x b)))))

(defthmd alists-compatible-iff-agree-on-bad-guy
  (iff (alists-compatible a b)
       (let ((x (alists-incompatible-witness a b)))
         (implies (and (hons-assoc-equal x a)
                       (hons-assoc-equal x b))
                  (equal (hons-assoc-equal x a)
                         (hons-assoc-equal x b)))))
  :hints(("Goal" :in-theory (enable alists-agree-iff-witness))))

(defthmd alists-compatible-iff-agree-on-bad-guy-concl
  (implies (syntaxp (let ((a a)
                          (b b)
                          (mfc mfc)
                          (state state))
                      (declare (ignore state))
                      (member-equal `(alists-compatible ,a ,b)
                                    (mfc-clause mfc))))
           (iff (alists-compatible a b)
                (let ((x (alists-incompatible-witness a b)))
                  (implies (and (hons-assoc-equal x a)
                                (hons-assoc-equal x b))
                           (equal (hons-assoc-equal x a)
                                  (hons-assoc-equal x b))))))
  :hints(("Goal" :in-theory (enable alists-agree-iff-witness))))

(defthmd alists-compatible-hons-assoc-equal
  (implies (and (alists-compatible a b)
                (hons-assoc-equal x a)
                (hons-assoc-equal x b))
           (equal (hons-assoc-equal x a)
                  (hons-assoc-equal x b)))
  :hints(("Goal" :in-theory (enable alists-agree-hons-assoc-equal))))

(local (in-theory (enable cons-key-cdr-hons-assoc-equal)))

(local (in-theory (disable alists-compatible-in-terms-of-alists-agree)))

(defthm alists-compatible-acons-1
  (implies (alists-compatible a b)
           (iff (alists-compatible (cons (cons key val) a) b)
                (or (not (hons-assoc-equal key b))
                    (equal (cdr (hons-assoc-equal key b)) val))))
  :hints(("Goal" :in-theory (e/d
                             (alists-compatible-iff-agree-on-bad-guy-concl
                              alists-compatible-hons-assoc-equal)
                             (alists-incompatible-witness))
          :use ((:instance alists-compatible-hons-assoc-equal
                           (x key) (a (cons (cons key val) a)) (b b)))
          :do-not-induct t))
  :otf-flg t)

(defthm alists-compatible-acons-2
  (implies (alists-compatible a b)
           (iff (alists-compatible a (cons (cons key val) b))
                (or (not (hons-assoc-equal key a))
                    (equal (cdr (hons-assoc-equal key a)) val))))
  :hints(("Goal" :in-theory (e/d
                             (alists-compatible-iff-agree-on-bad-guy-concl
                              alists-compatible-hons-assoc-equal)
                             (alists-incompatible-witness))
          :use ((:instance alists-compatible-hons-assoc-equal
                           (x key) (a (cons (cons key val) a)) (b b)))
          :do-not-induct t))
  :otf-flg t)

(defthm alists-compatible-append-1
  (implies (alists-compatible a b)
           (iff (alists-compatible (append c a) b)
                (alists-compatible c b)))
  :hints(("Goal" :in-theory (e/d
                             (alists-compatible-iff-agree-on-bad-guy-concl
                              alists-compatible-hons-assoc-equal)
                             (alists-incompatible-witness))
          :use ((:instance alists-compatible-hons-assoc-equal
                           (x (alists-incompatible-witness c b)) (a (append c a)) (b b)))
          :do-not-induct t)))

(defthm alists-compatible-append-2
  (implies (alists-compatible a b)
           (iff (alists-compatible a (append c b))
                (alists-compatible a c)))
  :hints(("Goal" :in-theory (e/d
                             (alists-compatible-iff-agree-on-bad-guy-concl
                              alists-compatible-hons-assoc-equal)
                             (alists-compatible
                              alists-incompatible-witness))
          :use ((:instance alists-compatible-hons-assoc-equal
                           (x (alists-incompatible-witness a c)) (a a) (b (append c b))))
          :do-not-induct t)))



(defsection alists-compatible-on-keys

  (local (in-theory (enable alists-compatible-on-keys)))

  (defthm alists-compatible-on-keys-refl
    (alists-compatible-on-keys keys a a))

  (defthmd alists-compatible-on-keys-sym
    (implies (alists-compatible-on-keys keys b a)
             (alists-compatible-on-keys keys a b)))

  (defthmd alists-compatible-on-keys-hons-assoc-equal
    (implies (and (alists-compatible-on-keys keys a b)
                  (member-equal x keys)
                  (hons-assoc-equal x a)
                  (hons-assoc-equal x b))
             (equal (cdr (hons-assoc-equal x a))
                    (cdr (hons-assoc-equal x b)))))

  (defun alists-incompatible-on-keys-witness (keys a b)
    (if (atom keys)
        nil
      (if (let ((alook (hons-get (car keys) a))
                (blook (hons-get (car keys) b)))
            (and alook blook (not (equal alook blook))))
          (car keys)
        (alists-incompatible-on-keys-witness (cdr keys) a b))))

  (defthmd alists-incompatible-on-keys-witness-correct
    (equal (alists-compatible-on-keys keys a b)
           (let ((witness (alists-incompatible-on-keys-witness keys a
                                                               b)))
             (not (and (member-equal witness keys)
                       (hons-assoc-equal witness a)
                       (hons-assoc-equal witness b)
                       (not (equal (cdr (hons-assoc-equal witness a))
                                   (cdr (hons-assoc-equal witness b))))))))
    :hints(("Goal" :in-theory (enable car-hons-assoc-equal-split))))

  (defthmd alists-compatible-on-keys-alist-keys
    (implies (alists-compatible-on-keys (alist-keys a) a b)
             (alists-compatible-on-keys (alist-keys b) a b))
    :hints(("Goal"
            :use ((:instance alists-incompatible-on-keys-witness-correct
                             (keys (alist-keys b)))
                  (:instance alists-compatible-on-keys-hons-assoc-equal
                             (keys (alist-keys a))
                             (x (alists-incompatible-on-keys-witness
                                 (alist-keys b) a b))))
            :do-not-induct t))))



(local (in-theory (enable alists-compatible)))

(defthm alists-compatible-refl
  (alists-compatible a a))

(defthmd alists-compatible-sym
  (implies (alists-compatible a b)
           (alists-compatible b a))
  :hints (("goal"
           :in-theory (enable alists-compatible-on-keys-alist-keys
                              alists-compatible-on-keys-sym))))

(defthm alists-compatible-on-keys-nil
  (alists-compatible-on-keys keys a nil))

(defthm alists-compatible-nil
  (and (alists-compatible a nil)
       (alists-compatible nil a)))


;; BOZO eventually it'd be nice to add, e.g., from centaur/misc/context-rw:

;; (defcong alist-equiv equal (alists-compatible a b) 1
;;   :hints (("goal" :cases ((alists-compatible a b)))
;;           (alist-reasoning)))

;; (defcong alist-equiv equal (alists-compatible a b) 2
;;   :hints (("goal" :cases ((alists-compatible a b)))
;;           (alist-reasoning)))

;; but that uses alist-reasoning...