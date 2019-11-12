; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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
(include-book "stack")

(local (std::add-default-post-define-hook :fix))

(define scratchobj-isomorphic ((x scratchobj-p) (y scratchobj-p))
  (and (eq (scratchobj-kind x) (scratchobj-kind y))
       (scratchobj-case x
         :fgl-objlist (eql (len x.val) (len (scratchobj-fgl-objlist->val y)))
         :bfrlist (eql (len x.val) (len (scratchobj-bfrlist->val y)))
         :cinstlist (eql (len x.val) (len (scratchobj-cinstlist->val y)))
         :otherwise t))
  ///
  (defequiv scratchobj-isomorphic)

  (defcong scratchobj-isomorphic equal (scratchobj-kind x) 1)

  (defthm len-fgl-objlist-when-scratchobj-isomorphic
    (implies (and (scratchobj-isomorphic x y)
                  (scratchobj-case x :fgl-objlist))
             (= (len (scratchobj-fgl-objlist->val x))
                (len (scratchobj-fgl-objlist->val y))))
    :rule-classes :linear)

  (defthm len-bfrlist-when-scratchobj-isomorphic
    (implies (and (scratchobj-isomorphic x y)
                  (scratchobj-case x :bfrlist))
             (= (len (scratchobj-bfrlist->val x))
                (len (scratchobj-bfrlist->val y))))
    :rule-classes :linear)

  (defthm len-cinstlist-when-scratchobj-isomorphic
    (implies (and (scratchobj-isomorphic x y)
                  (scratchobj-case x :cinstlist))
             (= (len (scratchobj-cinstlist->val x))
                (len (scratchobj-cinstlist->val y))))
    :rule-classes :linear))

(define scratchlist-isomorphic ((x scratchlist-p) (y scratchlist-p))
  (if (atom x)
      (atom y)
    (and (consp y)
         (scratchobj-isomorphic (car x) (car y))
         (scratchlist-isomorphic (cdr x) (cdr y))))
  ///
  (defequiv scratchlist-isomorphic)

  (defcong scratchlist-isomorphic scratchobj-isomorphic (car x) 1
    :hints(("Goal" :in-theory (enable default-car))))
  (defcong scratchlist-isomorphic scratchlist-isomorphic (cdr x) 1)
  
  (defcong scratchobj-isomorphic scratchlist-isomorphic (cons x y) 1)
  (defcong scratchlist-isomorphic scratchlist-isomorphic (cons x y) 2)

  (defcong scratchlist-isomorphic equal (len x) 1
    :hints(("Goal" :in-theory (enable len)))))

(define minor-frame-scratch-isomorphic ((x minor-frame-p) (y minor-frame-p))
  (scratchlist-isomorphic (minor-frame->scratch x) (minor-frame->scratch y))
  ///
  (defequiv minor-frame-scratch-isomorphic)

  (defcong minor-frame-scratch-isomorphic scratchlist-isomorphic (minor-frame->scratch x) 1)

  (defcong scratchlist-isomorphic minor-frame-scratch-isomorphic (minor-frame bindings scratch term term-index) 2)

  (defthm minor-frame-scratch-isomorphic-normalize-minor-frame
    (implies (syntaxp (not (and (Equal bindings ''nil)
                                (equal term ''nil)
                                (equal term-index ''nil))))
             (minor-frame-scratch-isomorphic (minor-frame bindings scratch term term-index)
                                             (minor-frame nil scratch nil nil)))))

(define minor-stack-scratch-isomorphic ((x minor-stack-p) (y minor-stack-p))
  (and (minor-frame-scratch-isomorphic (car x) (car y))
       (if (atom (cdr x))
           (atom (cdr y))
         (and (consp (cdr y))
              (minor-stack-scratch-isomorphic (cdr x) (cdr y)))))
  ///
  (defequiv minor-stack-scratch-isomorphic)

  (defcong minor-stack-scratch-isomorphic minor-frame-scratch-isomorphic (car x) 1
    :hints(("Goal" :in-theory (enable default-car))))
  (defcong minor-stack-scratch-isomorphic minor-stack-scratch-isomorphic (cdr x) 1
    :hints(("Goal" :in-theory (enable default-car))))
  
  (defcong minor-frame-scratch-isomorphic minor-stack-scratch-isomorphic (cons x y) 1)

  (defthm minor-stack-scratch-isomorphic-cons-cdr-congruence
    (implies (minor-stack-scratch-isomorphic x y)
             (minor-stack-scratch-isomorphic (cons frame (cdr x))
                                             (cons frame (cdr y))))
    :rule-classes :congruence)

  (defcong minor-stack-scratch-isomorphic acl2::pos-equiv (len x) 1
    :hints(("Goal" :in-theory (enable len pos-fix)))))


(define major-frame-scratch-isomorphic ((x major-frame-p) (y major-frame-p))
  (minor-stack-scratch-isomorphic (major-frame->minor-stack x) (major-frame->minor-stack y))
  ///
  (defequiv major-frame-scratch-isomorphic)

  (defcong major-frame-scratch-isomorphic minor-stack-scratch-isomorphic (major-frame->minor-stack x) 1)

  (defcong minor-stack-scratch-isomorphic major-frame-scratch-isomorphic (major-frame bindings rule phase minor-stack) 4)

  (defthm major-frame-scratch-isomorphic-normalize-major-frame
    (implies (syntaxp (not (and (Equal bindings ''nil)
                                (equal rule ''nil)
                                (equal phase ''nil))))
             (major-frame-scratch-isomorphic (major-frame bindings rule phase minor-stack)
                                             (major-frame nil nil nil minor-stack)))))

(define major-stack-scratch-isomorphic ((x major-stack-p) (y major-stack-p))
  (and (major-frame-scratch-isomorphic (car x) (car y))
       (if (atom (cdr x))
           (atom (cdr y))
         (and (consp (cdr y))
              (major-stack-scratch-isomorphic (cdr x) (cdr y)))))
  ///
  (defequiv major-stack-scratch-isomorphic)

  (defcong major-stack-scratch-isomorphic major-frame-scratch-isomorphic (car x) 1
    :hints(("Goal" :in-theory (enable default-car))))
  (defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic (cdr x) 1
    :hints(("Goal" :in-theory (enable default-car))))
  
  (defcong major-frame-scratch-isomorphic major-stack-scratch-isomorphic (cons x y) 1)

  (defthm major-stack-scratch-isomorphic-cons-cdr-congruence
    (implies (major-stack-scratch-isomorphic x y)
             (major-stack-scratch-isomorphic (cons frame (cdr x))
                                             (cons frame (cdr y))))
    :rule-classes :congruence)

  (defcong major-stack-scratch-isomorphic acl2::pos-equiv (len x) 1
    :hints(("Goal" :in-theory (enable len pos-fix)))))





(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-pop-scratch stack) 1
  :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-pop-frame stack) 1
  :hints(("Goal" :in-theory (enable stack$a-pop-frame))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-pop-minor-frame stack) 1
  :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-set-bindings bindings stack) 2
  :hints(("Goal" :in-theory (enable stack$a-set-bindings))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-set-rule rule stack) 2
  :hints(("Goal" :in-theory (enable stack$a-set-rule))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-set-phase phase stack) 2
  :hints(("Goal" :in-theory (enable stack$a-set-phase))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-set-term term stack) 2
  :hints(("Goal" :in-theory (enable stack$a-set-term))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-set-term-index term-index stack) 2
  :hints(("Goal" :in-theory (enable stack$a-set-term-index))))

(defcong scratchlist-isomorphic scratchlist-isomorphic (update-nth n obj x) 3
  :hints(("Goal" :in-theory (enable update-nth))))

(defcong major-stack-scratch-isomorphic
  major-stack-scratch-isomorphic (stack$a-update-scratch n obj stack) 3
  :hints(("Goal" :in-theory (enable stack$a-update-scratch))))

(defthm stack$a-pop-scratch-of-stack$a-push-scratch
  (equal (stack$a-pop-scratch (stack$a-push-scratch obj stack))
         (major-stack-fix stack))
  :hints(("Goal" :in-theory (enable stack$a-push-scratch stack$a-pop-scratch default-car)
          :expand ((major-stack-fix stack)))))


(defthm stack$a-pop-frame-of-stack$a-set-bindings
  (equal (stack$a-pop-frame (stack$a-set-bindings bindings stack))
         (stack$a-pop-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-bindings))))

(defthm stack$a-pop-frame-of-stack$a-set-rule
  (equal (stack$a-pop-frame (stack$a-set-rule obj stack))
         (stack$a-pop-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-rule))))

(defthm stack$a-pop-frame-of-stack$a-set-phase
  (equal (stack$a-pop-frame (stack$a-set-phase obj stack))
         (stack$a-pop-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-phase))))

(defthm stack$a-pop-frame-of-stack$a-set-term
  (equal (stack$a-pop-frame (stack$a-set-term obj stack))
         (stack$a-pop-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-term))))

(defthm stack$a-pop-frame-of-stack$a-set-term-index
  (equal (stack$a-pop-frame (stack$a-set-term-index obj stack))
         (stack$a-pop-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-term-index))))

(defthm stack$a-pop-frame-of-stack$a-push-frame
  (equal (stack$a-pop-frame (stack$a-push-frame stack))
         (major-stack-fix stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-push-frame))))

(defthm stack$a-pop-minor-frame-of-stack$a-set-minor-bindings
  (equal (stack$a-pop-minor-frame (stack$a-set-minor-bindings bindings stack))
         (stack$a-pop-minor-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-set-minor-bindings))))

(defthm stack$a-pop-minor-frame-of-stack$a-set-term
  (equal (stack$a-pop-minor-frame (stack$a-set-term obj stack))
         (stack$a-pop-minor-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-set-term))))

(defthm stack$a-pop-minor-frame-of-stack$a-set-term-index
  (equal (stack$a-pop-minor-frame (stack$a-set-term-index obj stack))
         (stack$a-pop-minor-frame stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-set-term-index))))

(defthm stack$a-pop-minor-frame-of-stack$a-push-minor-frame
  (equal (stack$a-pop-minor-frame (stack$a-push-minor-frame stack))
         (major-stack-fix stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-push-minor-frame
                                    major-stack-fix default-car))))


(defthm major-stack-scratch-isomorphic-of-add-binding
  (major-stack-scratch-isomorphic (stack$a-add-binding var val stack) stack)
  :hints(("Goal" :in-theory (enable stack$a-add-binding major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic))))

(defthm major-stack-scratch-isomorphic-of-set-bindings
  (major-stack-scratch-isomorphic (stack$a-set-bindings bindings stack) stack)
  :hints(("Goal" :in-theory (enable stack$a-set-bindings major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic))))

(defthm major-stack-scratch-isomorphic-of-set-rule
  (major-stack-scratch-isomorphic (stack$a-set-rule rule stack)
                                  stack)
  :hints(("Goal" :in-theory (enable stack$a-set-rule major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic))))

(defthm major-stack-scratch-isomorphic-of-set-phase
  (major-stack-scratch-isomorphic (stack$a-set-phase phase stack)
                                  stack)
  :hints(("Goal" :in-theory (enable stack$a-set-phase major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic))))

(defthm major-stack-scratch-isomorphic-of-set-term
  (major-stack-scratch-isomorphic (stack$a-set-term term stack)
                                  stack)
  :hints(("Goal" :in-theory (enable stack$a-set-term major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic
                                    minor-stack-scratch-isomorphic
                                    minor-frame-scratch-isomorphic))))

(defthm major-stack-scratch-isomorphic-of-set-term-index
  (major-stack-scratch-isomorphic (stack$a-set-term-index term-index stack)
                                  stack)
  :hints(("Goal" :in-theory (enable stack$a-set-term-index major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic
                                    minor-stack-scratch-isomorphic
                                    minor-frame-scratch-isomorphic))))

(defthm major-stack-scratch-isomorphic-of-add-minor-bindings
  (major-stack-scratch-isomorphic (stack$a-add-minor-bindings bindings stack) stack)
  :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings
                                    major-stack-scratch-isomorphic
                                    major-frame-scratch-isomorphic
                                    minor-stack-scratch-isomorphic
                                    minor-frame-scratch-isomorphic))))

