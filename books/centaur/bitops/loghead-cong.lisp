
; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

; contextual rewriting for loghead

(in-package "ACL2")
(include-book "tools/rulesets" :dir :system)
(include-book "centaur/misc/context-rw" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "ihs-extensions"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defmacro def-context-rule (name body &rest args)
  (let* ((fnname-look (ec-call (assoc-keyword :fnname args)))
         (fnname (cadr fnname-look))
         (rest-args (append (take (- (len args) (len fnname-look)) args)
                            (cddr fnname-look))))
    `(progn (defthmd ,name ,body . ,rest-args)
            (add-context-rule ,fnname (:rewrite ,name)))))

(local
 (encapsulate
   nil
   (local (defun ind (n m a b c)
            (if (zp n)
                (list m a b c)
              (ind (1- n) (1- m)
                   (logcdr a)
                   (logcdr b)
                   (b-ior (b-and (logcar a) (logcar b))
                          (b-ior
                           (b-and (logcar a) (logcar c))
                           (b-and (logcar b) (logcar c))))))))

   (defthm loghead-of-sum-lemma
     (implies (and (integerp a)
                   (integerp b)
                   (bitp c)
                   (<= (nfix n) (nfix m)))
              (equal (loghead n (+ c a (loghead m b)))
                     (loghead n (+ c a b))))
     :hints (("goal"
              :induct (ind n m a b c)
              :do-not '(generalize fertilize)
              :expand ((:free (b) (loghead n b))
                       (:free (b) (loghead m b)))
              :in-theory (e/d (nfix logcdr-of-bit b-and b-ior)
                              (loghead-identity))
              :do-not-induct t))
     :rule-classes nil)))

(defthmd loghead-of-minus-of-loghead
  (implies (and (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (- (loghead m b)))
                  (loghead n (- b))))
  :hints (("goal" :in-theory (e/d (minus-to-lognot))
           :use ((:instance loghead-of-sum-lemma
                  (c 1) (a 0) (b (lognot (loghead m b))))
                 (:instance loghead-of-sum-lemma
                  (c 1) (a 0) (b (lognot b)))))))

(defthmd loghead-of-plus-loghead-first
  (implies (and (integerp a)
                (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (+ (loghead m b) a))
                  (loghead n (+ a b))))
  :hints (("goal" :use ((:instance loghead-of-sum-lemma (c 0))))))

(defthmd loghead-of-plus-loghead-second
  (implies (and (integerp a)
                (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (+ a (loghead m b)))
                  (loghead n (+ a b))))
  :hints (("goal" :use ((:instance loghead-of-sum-lemma (c 0))))))

(def-context-rule loghead-of-minus-context
  (implies (integerp b)
           (equal (loghead n (- (loghead n b)))
                  (loghead n (- b))))
  :hints(("Goal" :in-theory (enable loghead-of-minus-of-loghead)))
  :fnname loghead)

(def-context-rule loghead-of-plus-context-1
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ (loghead n a) b))
                  (loghead n (+ a b))))
  :hints(("Goal" :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname loghead)

(def-context-rule loghead-of-plus-context-2
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ a (loghead n b)))
                  (loghead n (+ a b))))
  :hints(("Goal" :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname loghead)

(def-context-rule loghead-of-logtail-context
  (equal (loghead n (logtail m (loghead (+ (nfix n) (nfix m)) a)))
         (loghead n (logtail m a)))
  :fnname loghead)

(def-context-rule loghead-of-ash-context
  (equal (loghead n (ash (loghead (- (nfix n) (ifix m)) a) m))
         (loghead n (ash a m)))
  :hints(("Goal" :in-theory (enable loghead-of-ash nfix ifix)))
  :fnname loghead)

(def-context-rule loghead-of-logior-context-1
  (equal (loghead n (logior (loghead n a) b))
         (loghead n (logior a b)))
  :fnname loghead)

(def-context-rule loghead-of-logior-context-2
  (equal (loghead n (logior a (loghead n b)))
         (loghead n (logior a b)))
  :fnname loghead)

(def-context-rule logbitp-to-loghead-context
  (equal (logbitp n (loghead (+ 1 (nfix n)) x))
         (logbitp n x))
  :hints(("Goal" :in-theory (enable logbitp-of-loghead-split)))
  :fnname logbitp)

(def-ruleset! loghead-cong-rules
  '(apply-context-for-loghead
    common-lisp::apply-context-for-logbitp))

(in-theory (disable* loghead-cong-rules))
