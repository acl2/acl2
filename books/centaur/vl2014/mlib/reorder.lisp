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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "find")
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

<p>This can be useful in various places, e.g., dependency ordering for modules
or functions, reordering for port declarations in UDPs, etc.</p>

<p>These functions are reasonably efficient, i.e., if the list to reorder is
long, we build a temporary fast alist to speed up the lookups.  This
optimization is logically invisible via @(see mbe).</p>")

(local (xdoc::set-default-parents reordering-by-name))

(defconst *reorder-by-name-template*
  ;; Template for item reordering functions.
  ;;
  ;; Parameters                  Example
  ;; -------------------------------------------------------------
  ;;   [foo]                     fundecl
  ;;   [reorder-foos]            vl-reorder-fundecls
  ;;   [fast-reorder-foos]       vl-fast-reorder-fundecls
  ;;   [slow-reorder-foos]       vl-slow-reorder-fundecls
  ;;   [find-foo]                vl-find-fundecl
  ;;   [foo->name]               vl-fundecl->name
  ;;   [foolist->names]          vl-fundecllist->names
  ;; -------------------------------------------------------------

  '(progn

     (define [fast-reorder-foos] ((names string-listp)
                                  (x     vl-[foo]list-p)
                                  (fal   (equal fal (vl-[foo]list-alist x nil))))
       :parents ([reorder-foos])
       :short (cat "Fast-alist enhanced version of @(see " (symbol-name '[reorder-foos]) ").")
       :hooks nil
       (b* (((when (atom names))
             nil)
            (look (hons-get (car names) fal))
            ((when look)
             (cons (cdr look) ([fast-reorder-foos] (cdr names) x fal))))
         ([fast-reorder-foos] (cdr names) x fal)))

     (define [slow-reorder-foos] ((names string-listp)
                                  (x     vl-[foo]list-p))
       :parents ([reorder-foos])
       :short (cat "Non fast-alist version of @(see " (symbol-name '[reorder-foos]) "), used
                    when the lists are really short.")
       :long (cat "<p>You should ordinarily never reason about this because of the
                   following rule, which we leave enabled.</p>"
                  "@(def " (symbol-name '[slow-reorder-foos]-removal) ")")
       :hooks nil
       (b* (((when (atom names))
             nil)
            (decl ([find-foo] (car names) x))
            ((when decl)
             (cons decl ([slow-reorder-foos] (cdr names) x))))
         ([slow-reorder-foos] (cdr names) x)))

     (define [reorder-foos]
       :parents (vl-[foo]list-p reordering-by-name)
       :short (cat "Collect a subset of a @(see " (symbol-name 'vl-[foo]list-p)
                   ") by their names, according to a given name ordering.")
       ((names string-listp)
        (x     vl-[foo]list-p))
       :returns (sublist vl-[foo]list-p)
       :long "<p>This is a basic reordering function; see @(see reordering-by-name).</p>"
       :verify-guards nil
       (mbe :logic
            (b* (((when (atom names))
                  nil)
                 (decl ([find-foo] (car names) x))
                 ((when decl)
                  (cons decl ([reorder-foos] (cdr names) x))))
              ([reorder-foos] (cdr names) x))
            :exec
            (b* (((unless (and
                           ;; Contrived limits, not supported by benchmarking
                           (longer-than-p 6 names)
                           (acl2::worth-hashing x)))
                  ;; Since the list isn't very long, or we just aren't looking
                  ;; up very many names, don't bother building a fast alist.
                  ([slow-reorder-foos] names x))
                 (fal (make-fast-alist (vl-[foo]list-alist x nil)))
                 (ans ([fast-reorder-foos] names x fal)))
              (fast-alist-free fal)
              ans))
       ///
       (defthm [slow-reorder-foos]-removal
         (equal ([slow-reorder-foos] names x)
                ([reorder-foos] names x))
         :hints(("Goal" :in-theory (enable [slow-reorder-foos]))))

       (defthm [fast-reorder-foos]-removal
         (implies (and (string-listp names)
                       (vl-[foo]list-p x)
                       (equal fal (vl-[foo]list-alist x nil)))
                  (equal ([fast-reorder-foos] names x fal)
                         ([reorder-foos] names x)))
         :hints(("Goal" :in-theory (enable [fast-reorder-foos]))))

       (verify-guards [reorder-foos])

       (deffixequiv [reorder-foos])

       "<p>We prove some basic correctness properties.  To start, the list
        we get back is always a subset of the original list (modulo fixing).</p>"

       (local (defthm l1
                (implies (not (member ([foo->name] a) (string-list-fix names)))
                         (not (member a ([reorder-foos] names x))))
                :hints(("Goal" :in-theory (disable (force))))))

       (local (defthm l2-helper
                (implies ([find-foo] name x)
                         (member ([find-foo] name x)
                                 (vl-[foo]list-fix x)))
                :hints(("Goal" :in-theory (e/d ([find-foo]) ((force)))))))

       (local (defthm l2
                (implies (not (member a (vl-[foo]list-fix x)))
                         (not (member a ([reorder-foos] names x))))
                :hints(("Goal" :in-theory (disable (force))))))

       (defthm subsetp-of-[reorder-foos]
         ;; pick-a-point with l2
         (subsetp ([reorder-foos] names x) (vl-[foo]list-fix x))
         :hints((set-reasoning)))

       "<p>Furthermore, the names we get back for are the names we asked for.</p>"

       (defthm [foolist->names]-of-[reorder-foos]
         (implies (subsetp (double-rewrite names) ([foolist->names] x))
                  (equal ([foolist->names] ([reorder-foos] names x))
                         (list-fix names))))

       (defthm [foolist->names]-of-[reorder-foos]-bounded
         (subsetp ([foolist->names] ([reorder-foos] names x))
                  (string-list-fix names)))

       "<p>For stronger correctness properties, we need to know that the names in
        @('x') are unique.  After all, our finding functions rely on this, and
        won't return any \"shadowed\" objects in the list.</p>"

       (local (defthm l3
                (implies (and (member a x)
                              (no-duplicatesp-equal ([foolist->names] x)))
                         (equal ([find-foo] ([foo->name] a) x)
                                (vl-[foo]-fix a)))
                :hints(("Goal" :in-theory (enable [find-foo])))))

       (local (defthm l4-help
                (implies (and (vl-[foo]list-p x)
                              (member a x)
                              (equal ([foo->name] a) (str-fix name))
                              (no-duplicatesp-equal ([foolist->names] x)))
                         (equal ([find-foo] name x)
                                a))
                :hints(("Goal" :in-theory (enable [find-foo])))))

       (local (defthm l4
                (implies (and (member a x)
                              (member ([foo->name] a) (string-list-fix names))
                              (no-duplicatesp-equal ([foolist->names] x))
                              (vl-[foo]list-p x))
                         (member a ([reorder-foos] names x)))
                :hints(("Goal" :induct ([reorder-foos] names x)))))

       (defthm member-of-[reorder-foos]
         (implies (and (no-duplicatesp-equal ([foolist->names] x))
                       (force (vl-[foo]list-p x)))
                  (iff (member a ([reorder-foos] names x))
                       (and (member a x)
                            (member ([foo->name] a)
                                    (string-list-fix names))))))


       (local (defthm other-direction ;; pick-a-point
                (implies (and (no-duplicatesp-equal ([foolist->names] x))
                              (subsetp ([foolist->names] x)
                                       (string-list-fix names))
                              (vl-[foo]list-p x)
                              )
                         (subsetp (vl-[foo]list-fix x)
                                  ([reorder-foos] names x)))
                :hints((acl2::witness :ruleset (acl2::subsetp-witnessing)))))

       (local (defthm x1
                (implies (and (no-duplicatesp-equal ([foolist->names] x))
                              (set-equiv (double-rewrite (string-list-fix names))
                                         ([foolist->names] x))
                              (force (vl-[foo]list-p x)))
                         (set-equiv ([reorder-foos] names x)
                                    x))
                :hints(("Goal"
                        :in-theory (e/d (set-equiv)
                                        (other-direction
                                         subsetp-of-[reorder-foos]))
                        :use ((:instance other-direction)
                              (:instance subsetp-of-[reorder-foos])))
                       (and stable-under-simplificationp
                            (acl2::witness :ruleset (acl2::subsetp-witnessing))))))

       (defthm [reorder-foos]-under-set-equiv
         (implies (and (no-duplicatesp-equal ([foolist->names] x))
                       (set-equiv (double-rewrite (string-list-fix names))
                                  ([foolist->names] x)))
                  (set-equiv ([reorder-foos] names x)
                             (vl-[foo]list-fix x)))
         :hints(("Goal"
                 :do-not-induct t
                 :in-theory (disable x1
                                     other-direction
                                     subsetp-of-[reorder-foos])
                 :use ((:instance x1 (x (vl-[foo]list-fix x))))))))))

(defmacro def-vl-reorder (foo)
  (b* ((foo               (symbol-name foo))
       (find-foo          (cat "VL-FIND-" foo))
       (reorder-foos      (cat "VL-REORDER-" foo "S"))
       (fast-reorder-foos (cat "VL-FAST-REORDER-" foo))
       (slow-reorder-foos (cat "VL-SLOW-REORDER-" foo))
       (foo->name         (cat "VL-" foo "->NAME"))
       (foolist->names    (cat "VL-" foo "LIST->NAMES")))
    `(make-event
      (template-subst *reorder-by-name-template*
                      :str-alist ',(list (cons "[FOO]"               foo)
                                         (cons "[FIND-FOO]"          find-foo)
                                         (cons "[REORDER-FOOS]"      reorder-foos)
                                         (cons "[FAST-REORDER-FOOS]" fast-reorder-foos)
                                         (cons "[SLOW-REORDER-FOOS]" slow-reorder-foos)
                                         (cons "[FOO->NAME]"         foo->name)
                                         (cons "[FOOLIST->NAMES]"    foolist->names))
                      :pkg-sym (pkg-witness "VL2014")))))

(def-vl-reorder fundecl)
(def-vl-reorder portdecl)
(def-vl-reorder module)
(def-vl-reorder vardecl)
