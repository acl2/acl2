; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "scopestack")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc reordering-by-name
  :parents (mlib)
  :short "Functions for reordering lists of parsed objects by their names."

  :long "<p>We implement functions for rearranging design elements into a
different order.</p>

<p>In most ways, these functions are similar to the functions for @(see
filtering-by-name).  However, the name filtering functions preserve the order
of the input list, whereas these functions explicitly reorder the elements to
match the order of the names.</p>

<p>This can be useful in, e.g., dependency ordering.</p>")

(local (xdoc::set-default-parents reordering-by-name))

(defund def-vl-reorder-by-name-fn
  (type          ;; should be 'paramdecl, 'vardecl, 'module, etc.
   suffix        ;; e.g., "netdecls" or "events" or "modinsts-by-name"
   )
  (declare (xargs :guard (and (symbolp type)
                              (symbolp suffix))))
  (let* ((mksym-package-symbol 'vl::foo)
         ;(type->name   accessor)
         ;(type-fix     (mksym 'vl- type '-fix))
         (list-p       (mksym 'vl- type 'list-p))
         ;(list-fix     (mksym 'vl- type 'list-fix))
         (list-alist   (mksym 'vl- type 'list-alist))
         (find-fn      (mksym 'vl-find- type))
         (fast-fn      (mksym 'vl-fast-reorder- suffix))
         (fn           (mksym 'vl-reorder- suffix)))
    `(encapsulate ()

       (define ,fn ((names string-listp)
                    (x ,list-p))
         :short ,(cat "Reorder a @(see " (symbol-name list-p) " to match some desired name ordering.")
         :long ,(cat "<p>See also @(see " (symbol-name fast-fn) " for a faster version using @(see fast-alists).")
         :verbosep t
         (b* (((when (atom names))
               nil)
              (item (,find-fn (string-fix (car names)) x))
              ((when item)
               (cons item (,fn (cdr names) x))))
           (,fn (cdr names) x)))

       (define ,fast-fn ((names string-listp)
                         (x     ,list-p)
                         (fal   (equal fal (,list-alist x nil))))
         :parents (,fn)
         :short ,(cat "Fast-alist enhanced version of @(see " (symbol-name fn) ").")
         :enabled t
         :guard-hints(("Goal" :in-theory (enable ,fn)))
         :verbosep t
         (mbe :logic
              (,fn names x)
              :exec
              (b* (((when (atom names))
                    nil)
                   (look (hons-get (car names) fal))
                   ((when look)
                    (cons (cdr look) (,fast-fn (cdr names) x fal))))
                (,fast-fn (cdr names) x fal))))
         )))

(defmacro def-vl-reorder-by-name (type &key suffix)
  (let* ((mksym-package-symbol 'vl::foo)
         (suffix     (or suffix (mksym type 's))))
    (def-vl-reorder-by-name-fn type suffix)))

(def-vl-reorder-by-name fundecl)



(define vl-reorder-fundecls
  :parents (vl-fundecllist-p filtering-by-name vl-depsort-functions)
  :short "@(call vl-reorder-fundecls) extracts the named functions from @('x'),
a @(see vl-fundecllist-p), in the same order as @('names')."
  ((names string-listp)
   (x     vl-fundecllist-p))
  :returns (named-functions vl-fundecllist-p)
  :long "<p>This is similar to @(see vl-keep-fundecls), but
@('vl-keep-fundecls') preserves the order of @('x'), whereas this explicitly
reorders @('x') to match @('names').</p>"

  (b* (((when (atom names))
        nil)
       (decl (vl-find-fundecl (car names) x))
       ((when decl)
        (cons decl (vl-reorder-fundecls (cdr names) x))))
    (vl-reorder-fundecls (cdr names) x))
  ///
  (local (in-theory (enable vl-reorder-fundecls)))

  (deffixequiv vl-reorder-fundecls :args ((x vl-fundecllist-p)))

  (local (defthm l1
           (implies (not (member-equal (vl-fundecl->name a) names))
                    (not (member-equal a (vl-reorder-fundecls names x))))
           :hints(("Goal" :in-theory (disable (force))))))

  (local (defthm l2-helper
           (implies (vl-find-fundecl name x)
                    (member-equal (vl-find-fundecl name x)
                                  (vl-fundecllist-fix x)))
           :hints(("Goal" :in-theory (e/d (vl-find-fundecl) ((force)))))))

  (local (defthm l2
           (implies (not (member-equal a (vl-fundecllist-fix x)))
                    (not (member-equal a (vl-reorder-fundecls names x))))
           :hints(("Goal" :in-theory (disable (force))))))

  (defthm subsetp-equal-of-vl-reorder-fundecls
    ;; pick-a-point with l2
    (implies (subsetp-equal (double-rewrite names) (vl-fundecllist->names x))
             (subsetp-equal (vl-reorder-fundecls names x)
                            (vl-fundecllist-fix x)))
    :hints((set-reasoning)))


  ;; For the other direction we need no-duplicatesp-equal, since "shadowed"
  ;; function definitions wouldn't be included since vl-find-fundecl just
  ;; grabs the first decl by name.

  (local (defthm l3
           (implies (and (member-equal a x)
                         (no-duplicatesp-equal (vl-fundecllist->names x)))
                    (equal (vl-find-fundecl (vl-fundecl->name a) x)
                           (vl-fundecl-fix a)))
           :hints(("Goal" :in-theory (enable vl-find-fundecl)))))

  (local (defthm l4
           (implies (and (member-equal a x)
                         (member-equal (vl-fundecl->name a) names)
                         (no-duplicatesp-equal (vl-fundecllist->names x))
                         (vl-fundecllist-p x))
                    (member-equal a (vl-reorder-fundecls names x)))))

  (defthm member-equal-of-vl-reorder-fundecls
    (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                  (force (vl-fundecllist-p x)))
             (iff (member-equal a (vl-reorder-fundecls names x))
                  (and (member-equal a x)
                       (member-equal (vl-fundecl->name a) names)))))


  (local (defthm other-direction ;; pick-a-point
           (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                         (subsetp-equal (vl-fundecllist->names x) names)
                         (vl-fundecllist-p x)
                         )
                    (subsetp-equal (vl-fundecllist-fix x)
                                   (vl-reorder-fundecls names x)))
           :hints((acl2::witness :ruleset (acl2::subsetp-witnessing)))))

  (local (defthm x1
           (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                         (set-equiv (double-rewrite names) (vl-fundecllist->names x))
                         (force (vl-fundecllist-p x)))
                    (set-equiv (vl-reorder-fundecls names x)
                               x))
           :hints(("Goal"
                   :in-theory (e/d (set-equiv)
                                   (other-direction
                                    subsetp-equal-of-vl-reorder-fundecls))
                   :use ((:instance other-direction)
                         (:instance subsetp-equal-of-vl-reorder-fundecls))))))

  (defthm vl-reorder-fundecls-under-set-equiv
    (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                  (set-equiv (double-rewrite names) (vl-fundecllist->names x)))
             (set-equiv (vl-reorder-fundecls names x)
                        (vl-fundecllist-fix x)))
    :hints(("Goal"
            :do-not-induct t
            :in-theory (disable x1
                                other-direction
                                subsetp-equal-of-vl-reorder-fundecls)
            :use ((:instance x1 (x (vl-fundecllist-fix x))))))))
