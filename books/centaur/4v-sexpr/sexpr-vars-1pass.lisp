; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; sexpr-vars-1pass.lisp
;  - sexpr-vars-1pass function for gathering variables in a sexpr
;  - correctness proof w.r.t. sexpr-vars

(in-package "ACL2")
(include-book "sexpr-vars")
(local (include-book "std/lists/sets" :dir :system))

(defsection 4v-sexpr-vars-1pass
  :parents (4v-sexpr-vars)
  :short "Often faster alternative to @(see 4v-sexpr-vars)."

  :long "<p>@(call 4v-sexpr-vars-1pass) is logically identical to @(see
4v-sexpr-vars).  But in the execution, a much different strategy for collecting
variables is used.</p>

<p>In particular, we use an ordinary fast alist as a seen-table to keep track
of the sexprs whose variables we have already seen, and a separate accumulator
for the variables we have encountered.</p>

<p>This approach allows us to much more quickly gather the variables from a
single sexpr.  But it can be a poor choice if you need to compute the variables
of many related sexprs, basically because no information can be reused across
separate runs.</p>

<p>See also @(see 4v-nsexpr-vars).</p>

<h3>Technical Note</h3>

<p>The definition is slightly odd in that (1) we update SEEN even in the ATOM
case, and (2) we do the update to SEEN <b>after</b> the recursive call, even
though it means that we don't get to have a tail call.</p>

<p>These oddities ensure that VARS are always correct w.r.t. SEEN as we recur,
by which we mean that VARS are set-equiv to collecting vars from the keys of
SEEN.</p>

<p>If we were to recur in the other way, i.e., by first updating SEEN, then we
would be temporarily violating the invariant until the recursion finished.
This stupid twist makes the proof ridiculously harder!</p>"

  (mutual-recursion

   (defun 4v-sexpr-vars-1pass-exec (x seen vars)
     "Returns (MV SEEN VARS)"
     (declare (xargs :guard t))
     (b* (((when (hons-get x seen))
           (mv seen vars))
          ((when (atom x))
           (mv (hons-acons x t seen)
               (if x (cons x vars) vars)))
          ((mv seen vars)
           (4v-sexpr-vars-1pass-list-exec (cdr x) seen vars))
          (seen (hons-acons x t seen)))
       (mv seen vars)))

   (defun 4v-sexpr-vars-1pass-list-exec (x seen vars)
     "Returns (MV SEEN VARS)"
     (declare (xargs :guard t))
     (b* (((when (atom x))
           (mv seen vars))
          ((mv seen vars)
           (4v-sexpr-vars-1pass-exec (car x) seen vars)))
       (4v-sexpr-vars-1pass-list-exec (cdr x) seen vars))))

  (defun 4v-sexpr-vars-1pass (x)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (4v-sexpr-vars x)
         :exec
         (b* (((mv seen vars) (4v-sexpr-vars-1pass-exec x nil nil)))
           (fast-alist-free seen)
           ;; [Jared]: This originally used an alphorder-merge based on
           ;; defsort.  When I did the correctness proof, he switched it to
           ;; set::mergesort so that I wouldn't need to argue that there
           ;; aren't any duplicates.  The two should be very similar in speed,
           ;; and eventually set::mergesort may get additional optimizations.
           (set::mergesort vars)))))

(local (flag::make-flag flag-4v-sexpr-vars-1pass-exec
                        4v-sexpr-vars-1pass-exec
                        :flag-mapping ((4v-sexpr-vars-1pass-exec sexpr)
                                       (4v-sexpr-vars-1pass-list-exec list))))

(local (in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                       (alist-keys-member-hons-assoc-equal))))

;; (local (defthm member-by-subset
;;            (and (implies (and (subsetp-equal x y)
;;                               (member-equal a x))
;;                          (member-equal a y))
;;                 (implies (and (member-equal a x)
;;                               (subsetp-equal x y))
;;                          (member-equal a y)))))

;; (local (defthm subset-transitive
;;            (and (implies (and (subsetp-equal x y)
;;                               (subsetp-equal y z))
;;                          (subsetp-equal x z))
;;                 (implies (and (subsetp-equal y z)
;;                               (subsetp-equal x y))
;;                          (subsetp-equal x z)))))

(local (defthm helper-1
           ;; this works out because if x is an atom, then its sexpr-vars are just itself
           (implies (and (member-equal x (alist-keys seen))
                         (not (consp x))
                         x
                         )
                    (member-equal x (4v-sexpr-vars-list (alist-keys seen))))
           :hints(("goal" :induct (len seen)))))

(local (defthm helper-2
           (implies (equal sexpr (cons fn args))
                    (subsetp-equal (4v-sexpr-vars-list args)
                                   (append lhs (4v-sexpr-vars sexpr))))))

(local (defthm helper-3
           (implies (member-equal x (alist-keys seen))
                    (subsetp-equal (4v-sexpr-vars-list (cdr x))
                                   (4v-sexpr-vars-list (alist-keys seen))))
           :hints(("goal" :induct (len seen)))))

(local (defthm helper-4
         (implies (member-equal a x)
                  (subsetp-equal (4v-sexpr-vars a)
                                 (4v-sexpr-vars-list x)))
         :hints(("Goal" :in-theory (enable member-equal)))))

(local (defthm-flag-4v-sexpr-vars-1pass-exec
         (defthm seen-has-correct-vars-sexpr
           (b* (((mv new-seen &) (4v-sexpr-vars-1pass-exec x seen vars)))
             (set-equiv (4v-sexpr-vars-list (alist-keys new-seen))
                         (append (4v-sexpr-vars-list (alist-keys seen))
                                 (4v-sexpr-vars x))))
           :flag sexpr)
         (defthm seen-has-correct-vars-list
           (b* (((mv new-seen &) (4v-sexpr-vars-1pass-list-exec x seen vars)))
             (set-equiv (4v-sexpr-vars-list (alist-keys new-seen))
                         (append (4v-sexpr-vars-list (alist-keys seen))
                                 (4v-sexpr-vars-list x))))
           :flag list)))

(local (defthm-flag-4v-sexpr-vars-1pass-exec
         (defthm vars-are-increasing-sexpr
           (subsetp vars (mv-nth 1 (4v-sexpr-vars-1pass-exec x seen vars)))
           :flag sexpr)
         (defthm vars-are-increasing-list
           (subsetp vars (mv-nth 1 (4v-sexpr-vars-1pass-list-exec x seen vars)))
           :flag list)))

(local (defthm-flag-4v-sexpr-vars-1pass-exec
         (defthm vars-upper-bound-sexpr
           (b* (((mv & new-vars) (4v-sexpr-vars-1pass-exec x seen vars)))
             (subsetp-equal new-vars (append vars (4v-sexpr-vars x))))
           :flag sexpr)
         (defthm vars-upper-bound-list
           (b* (((mv & new-vars) (4v-sexpr-vars-1pass-list-exec x seen vars)))
             (subsetp-equal new-vars (append vars (4v-sexpr-vars-list x))))
           :flag list)))

(local (defthm-flag-4v-sexpr-vars-1pass-exec
         (defthm vars-are-correct-sexpr
           (b* (((mv & new-vars)
                 (4v-sexpr-vars-1pass-exec x seen vars)))
             (implies (set-equiv vars (4v-sexpr-vars-list (alist-keys seen)))
                      (set-equiv new-vars
                                  (append (4v-sexpr-vars-list (alist-keys seen))
                                          (4v-sexpr-vars x)))))
           :flag sexpr)
         (defthm vars-are-correct-list
           (b* (((mv & new-vars)
                 (4v-sexpr-vars-1pass-list-exec x seen vars)))
             (implies (set-equiv vars (4v-sexpr-vars-list (alist-keys seen)))
                      (set-equiv new-vars
                                  (append (4v-sexpr-vars-list (alist-keys seen))
                                          (4v-sexpr-vars-list x)))))
           :flag list)))

(local (defthm promote-member-equal-to-in
         (implies (set::setp x)
                  (iff (member-equal a x)
                       (set::in a x)))
         :hints(("Goal" :in-theory (enable set::in-to-member)))))

(local (defthm main-corollary
           (set-equiv (mv-nth 1 (4v-sexpr-vars-1pass-exec x nil nil))
                       (4v-sexpr-vars x))))


(defsection 4v-sexpr-vars-1pass-main
  :extension 4v-sexpr-vars-1pass

  (defthm 4v-sexpr-vars-1pass-exec-correct
    (equal (set::mergesort (mv-nth 1 (4v-sexpr-vars-1pass-exec x nil nil)))
           (4v-sexpr-vars x)))

  (defthm 4v-sexpr-vars-1pass-list-exec-correct
    (equal (set::mergesort (mv-nth 1 (4v-sexpr-vars-1pass-list-exec x nil nil)))
           (4v-sexpr-vars-list x)))

  (verify-guards 4v-sexpr-vars-1pass))


(defsection 4v-sexpr-vars-1pass-list
  :parents (4v-sexpr-vars)
  :short "Often faster alternative to @(see 4v-sexpr-vars-list)."

  :long "<p>This uses the @(see 4v-sexpr-vars-1pass) strategy to gather
variables from a list of sexprs.</p>"

  (defun 4v-sexpr-vars-1pass-list (x)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-vars-list x)
         :exec
         (b* (((mv seen vars)
               (4v-sexpr-vars-1pass-list-exec x nil nil)))
           (fast-alist-free seen)
           (set::mergesort vars)))))


(defsection 4v-sexpr-vars-1pass-list-list
  :parents (4v-sexpr-vars)
  :short "Often faster alternative to @(see 4v-sexpr-vars-list-list)."

  :long "<p>This uses the @(see 4v-sexpr-vars-1pass) to gather variables from a
list of sexpr lists.</p>"

  (defun 4v-sexpr-vars-1pass-list-list-exec (x seen vars)
    (declare (xargs :guard t))
    (b* (((when (atom x))
          (mv seen vars))
         ((mv seen vars)
          (4v-sexpr-vars-1pass-list-exec (car x) seen vars)))
      (4v-sexpr-vars-1pass-list-list-exec (cdr x) seen vars)))

  (local (defthm l0
           (b* (((mv & new-vars)
                 (4v-sexpr-vars-1pass-list-list-exec x seen vars)))
             (implies (set-equiv vars (4v-sexpr-vars-list (alist-keys seen)))
                      (set-equiv new-vars
                                  (append (4v-sexpr-vars-list (alist-keys seen))
                                          (4v-sexpr-vars-list-list x)))))))

  (defthm 4v-sexpr-vars-1pass-list-list-exec-correct
    (equal (set::mergesort (mv-nth 1 (4v-sexpr-vars-1pass-list-list-exec x nil nil)))
           (4v-sexpr-vars-list-list x)))

  (defun 4v-sexpr-vars-1pass-list-list (x)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-vars-list-list x)
         :exec
         (b* (((mv seen vars)
               (4v-sexpr-vars-1pass-list-list-exec x nil nil)))
           (fast-alist-free seen)
           (set::mergesort vars)))))


