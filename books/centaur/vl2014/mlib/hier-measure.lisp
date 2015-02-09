; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "modnamespace")
(include-book "find")
(include-book "centaur/misc/dag-measure" :dir :system)


(defsection vl-modhier-measure
  ;; this isn't necessary for def-dag-measure, but is helpful for getting the
  ;; measure of vl-modhier-depth-memo
  (local (include-book "centaur/misc/dag-measure-thms" :dir :system))

  (acl2::def-dag-measure vl-modhier-aux
    :graph-formals (modalist)
    :successors-expr (let ((look (mbe :logic (hons-assoc-equal acl2::x modalist)
                                      :exec (hons-get acl2::x modalist))))
                       (and look
                            (vl-modinstlist->modnames
                             (vl-module->modinsts (cdr look)))))
    :nodes-expr (alist-keys modalist)
    :guard (vl-modalist-p modalist))


  (mutual-recursion
   (defun vl-modhier-depth-memo (x memo modalist)
     (declare (xargs :measure (acl2::nat-list-measure
                               (list (len (set-difference-equal (alist-keys modalist)
                                                                (alist-keys memo)))
                                     0 1))
                     :verify-guards nil
                     :guard (and (vl-modalist-p modalist)
                                 (acl2::fg-memo-p memo))))
     (b* ((look (hons-get x memo))
          ((when look)
           (let ((val (cdr look)))
             (if (or (eq val :back)
                     (eq val :loop))
                 (mv :loop memo)
               (mv (lnfix val) memo))))
          (memo (hons-acons x :back memo))
          ((mv max-depth memo)
           (vl-modhier-depth-memo-list
            (let
                ((look (mbe :logic (hons-assoc-equal x modalist)
                            :exec (hons-get x modalist))))
              (and look
                   (vl-module->modinsts (cdr look))))
            memo modalist))
          (res (if (eq max-depth :loop)
                   :loop
                 (+ 1 (lnfix max-depth)))))
       (mv res (hons-acons x res memo))))

   (defun vl-modhier-depth-memo-list (x memo modalist)
     (declare (xargs :measure (acl2::nat-list-measure
                               (list
                                (len (set-difference-equal (alist-keys modalist)
                                                           (alist-keys memo)))
                                (len x)
                                0))
                     :guard (and (vl-modalist-p modalist)
                                 (vl-modinstlist-p x)
                                 (acl2::fg-memo-p memo))))
     (b* (((when (atom x)) (mv 0 memo))
          ((mv depth1 memo1)
           (vl-modhier-depth-memo (vl-modinst->modname (car x)) memo modalist))
          ((unless
               (mbt (<= (len (set-difference-equal (alist-keys modalist)
                                                   (alist-keys memo1)))
                        (len (set-difference-equal (alist-keys modalist)
                                                   (alist-keys memo))))))
           (mv :loop memo1))
          ((mv depth2 memo)
           (vl-modhier-depth-memo-list (cdr x) memo1 modalist))
          ((when (or (eq depth1 :loop)
                     (eq depth2 :loop)))
           (mv :loop memo)))
       (mv (max depth1 depth2) memo))))

  (flag::make-flag vl-modhier-depth-flag vl-modhier-depth-memo)

  (local (in-theory (disable max)))

  (defthm-vl-modhier-depth-flag
    (defthm vl-modhier-depth-memo-is-vl-modhier-aux-depth-memo
      (equal (vl-modhier-depth-memo x memo modalist)
             (vl-modhier-aux-depth-memo x memo modalist))
      :hints ('(:expand ((vl-modhier-depth-memo x memo modalist)
                         (vl-modhier-aux-depth-memo x memo modalist))))
      :flag vl-modhier-depth-memo)
    (defthm vl-modhier-depth-memo-list-is-vl-modhier-aux-depth-memo-list
      (equal (vl-modhier-depth-memo-list x memo modalist)
             (vl-modhier-aux-depth-memo-list (vl-modinstlist->modnames x) memo modalist))
      :hints ('(:expand ((vl-modhier-depth-memo-list x memo modalist)
                         (vl-modinstlist->modnames x)
                         (:free (a b)
                          (vl-modhier-aux-depth-memo-list (cons a b) memo modalist)))))
      :flag vl-modhier-depth-memo-list))

  (encapsulate nil
    (local (defthm acl2-numberp-when-integerp
             (implies (integerp x)
                      (and (acl2-numberp x)
                           (rationalp x)))))
    (verify-guards vl-modhier-depth-memo))

  (define vl-modhier-loopfree-p (x (modalist vl-modalist-p))
    :parents (vl-modhier-measure)
    :short "Checks that a module's instances (transitively) never contain a
loop in the hierarchy."
    :long "<p>@('x') is the name of a module.  Returns true if there are no
module hierarchy loops reachable (through module instantiation) from
@('x').</p>

<p>This is useful as a guard for functions that recur over the module
hierarchy.  See @('vl-modhinst-count') for an example.</p>"
    (b* (((mv res memo) (vl-modhier-depth-memo x nil modalist)))
      (fast-alist-free memo)
      (not (eq res :loop)))
    ///
    (defthm vl-modhier-loopfree-p-is-vl-modhier-aux-loopfree-p
      (equal (vl-modhier-loopfree-p x modalist)
             (vl-modhier-aux-loopfree-p x modalist))
      :hints(("Goal" :in-theory (enable vl-modhier-aux-loopfree-p)))))

  (define vl-modhier-loopfreelist-p ((x vl-modinstlist-p) (modalist vl-modalist-p))
    (b* (((mv res memo) (vl-modhier-depth-memo-list x nil modalist)))
      (fast-alist-free memo)
      (not (eq res :loop)))
    ///
    (defthm vl-modhier-loopfreelist-p-is-vl-modhier-aux-loopfreelist-p
      (equal (vl-modhier-loopfreelist-p x modalist)
             (vl-modhier-aux-loopfreelist-p (vl-modinstlist->modnames x) modalist))
      :hints(("Goal" :in-theory (enable vl-modhier-aux-loopfreelist-p))))

    (defthm vl-modhier-aux-loopfreelist-p-of-successors-rw
      (implies (and (vl-modhier-aux-loopfree-p x modalist)
                    (hons-assoc-equal x modalist))
               (vl-modhier-aux-loopfreelist-p
                (vl-modinstlist->modnames
                 (vl-module->modinsts (cdr (hons-assoc-equal x modalist))))
                modalist))
      :hints (("goal" :use ((:instance vl-modhier-aux-loopfreelist-p-of-successors
                             (acl2::x x))))))

    (defthm vl-modhier-aux-loopfreelist-p-of-cdr-rw
      (implies (and (vl-modhier-aux-loopfreelist-p (vl-modinstlist->modnames x) modalist)
                    (consp x))
               (vl-modhier-aux-loopfreelist-p
                (vl-modinstlist->modnames (cdr x)) modalist))
      :hints (("goal" :use ((:instance vl-modhier-aux-loopfreelist-p-of-cdr
                             (acl2::x (vl-modinstlist->modnames x)))))))

    (defthm vl-modhier-aux-loopfree-p-of-car-rw
      (implies (and (vl-modhier-aux-loopfreelist-p (vl-modinstlist->modnames x) modalist)
                    (consp x))
               (vl-modhier-aux-loopfree-p
                (vl-modinst->modname (car x)) modalist))
      :hints (("goal" :use ((:instance vl-modhier-aux-loopfree-p-of-car
                             (acl2::x (vl-modinstlist->modnames x))))))))

  (define vl-modhier-measure (x (modalist vl-modalist-p))
    :parents (mlib)
    :short "Measure for module hierarchy traversal"
    :long " <p>This, along with @('vl-modhier-loopfree-p'), provide a simple
way to traverse the module hierarchy, avoiding termination problems due to the
possibility of modules that instance each other in a cycle.</p>

<p>This and @('vl-modhier-list-measure') together are an appropriate measure
for a mutual-recursion in which one function (measured by
@('vl-modhier-measure')) takes a module name and calls the other function on
its list of module instances, and the other function (measured by
@('vl-modhier-list-measure') in turn calls the first function on the modname of
each instance.</p>

<p>For an example of usage, see @('vl-module-modinst-count').</p>"

    :enabled t
    :verify-guards nil
    (vl-modhier-aux-measure x modalist)
    ///
    (defthm vl-modhier-aux-list-measure-of-successors-rw
      (implies (and (vl-modhier-aux-loopfree-p x modalist)
                    (hons-assoc-equal x modalist))
               (o< (vl-modhier-aux-list-measure
                    (vl-modinstlist->modnames
                     (vl-module->modinsts (cdr (hons-assoc-equal x modalist))))
                    modalist)
                   (vl-modhier-aux-measure x modalist)))
      :hints (("goal" :use ((:instance vl-modhier-aux-list-measure-of-successors
                             (acl2::x x)))))))

  (define vl-modhier-list-measure ((x vl-modinstlist-p) (modalist vl-modalist-p))
    :parents (vl-modhier-measure)
    :short "Measure (of a list of module instances)for module hierarchy traversal"
    :long "<p>See @(see vl-modhier-measure).</p>"
    :enabled t
    :verify-guards nil
    (vl-modhier-aux-list-measure (vl-modinstlist->modnames x) modalist)
    ///
    (defthm vl-modhier-aux-measure-of-car-rw
      (implies (consp x)
               (o< (vl-modhier-aux-measure (vl-modinst->modname (car x)) modalist)
                   (vl-modhier-aux-list-measure (vl-modinstlist->modnames x) modalist)))
      :hints (("goal" :use ((:instance vl-modhier-aux-measure-of-car
                             (acl2::x (vl-modinstlist->modnames x))))
               :in-theory (disable vl-modhier-aux-measure-of-car))))
    (defthm vl-modhier-aux-list-measure-of-cdr-rw
      (implies (consp x)
               (o< (vl-modhier-aux-list-measure (vl-modinstlist->modnames (cdr x)) modalist)
                   (vl-modhier-aux-list-measure (vl-modinstlist->modnames x) modalist)))
      :hints (("goal" :use ((:instance vl-modhier-aux-list-measure-of-cdr
                             (acl2::x (vl-modinstlist->modnames x))))
               :in-theory (disable vl-modhier-aux-list-measure-of-cdr))))))


(defsection vl-module-modinst-count
  :parents (vl-modhier-measure)
  :short "Full count of the total number of module instances, including repetitions, in a module."
  (mutual-recursion
   (defun vl-module-modinst-count (x modalist)
     (declare (xargs :guard (and (vl-modalist-p modalist)
                                 (vl-modhier-loopfree-p x modalist))
                     :measure (vl-modhier-measure x modalist)))
     (b* (((unless (mbt (vl-modhier-loopfree-p x modalist))) 1)
          (look (hons-get x modalist))
          ((unless look) 1))
       (+ 1 (vl-modinstlist-modinst-count (vl-module->modinsts (cdr look)) modalist))))
   (defun vl-modinstlist-modinst-count (x modalist)
     (declare (xargs :guard (and (vl-modinstlist-p x)
                                 (vl-modalist-p modalist)
                                 (vl-modhier-loopfreelist-p x modalist))
                     :measure (vl-modhier-list-measure x modalist)))
     (if (atom x)
         0
       (+ (vl-module-modinst-count (vl-modinst->modname (car x)) modalist)
          (vl-modinstlist-modinst-count (cdr x) modalist)))))

  (flag::make-flag vl-module-modinst-count-flag vl-module-modinst-count)


  (defthm-vl-module-modinst-count-flag
    (defthm vl-module-modinst-count-type
      (posp (vl-module-modinst-count x modalist))
      :rule-classes :type-prescription
      :flag vl-module-modinst-count)
    (defthm vl-modinstlist-modinst-count-type
      (natp (vl-module-modinst-count x modalist))
      :rule-classes :type-prescription
      :flag vl-modinstlist-modinst-count)))


