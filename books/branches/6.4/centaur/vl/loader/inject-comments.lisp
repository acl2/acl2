; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


(defsection vl-commentmap-entry-sort
  :parents (vl-commentmap-p)
  :short "A basic sort for comment maps."

  :long "<p>Our pretty-printer uses the following routine in a funny way to get
the comments put inline with the module elements.</p>

<p>The sort is introduced with defsort, so it is a stable mergesort.  Note that
we ignore file names.</p>"

  (defund vl-commentmap-entry-p (x)
    (declare (xargs :guard t))
    (and (consp x)
         (vl-location-p (car x))
         (stringp (cdr x))))

  (defund vl-commentmap-entry-< (x y)
    (declare (xargs :guard (and (vl-commentmap-entry-p x)
                                (vl-commentmap-entry-p y))
                    :guard-hints (("Goal" :in-theory (enable vl-commentmap-entry-p)))))
    (let ((line-x (vl-location->line (car x)))
          (line-y (vl-location->line (car y))))
      (or (< line-x line-y)
          (and (= line-x line-y)
               (< (vl-location->col (car x))
                  (vl-location->col (car y)))))))

  (defthm transitivity-of-vl-commentmap-entry-<
    (implies (and (vl-commentmap-entry-< x y)
                  (vl-commentmap-entry-< y z))
             (vl-commentmap-entry-< x z))
    :hints(("Goal" :in-theory (enable vl-commentmap-entry-<))))

  (ACL2::defsort :comparablep vl-commentmap-entry-p
                 :compare< vl-commentmap-entry-<
                 :prefix vl-commentmap-entry)

  (defthm vl-commentmap-entry-list-p-elim
    (equal (vl-commentmap-entry-list-p x)
           (vl-commentmap-p (list-fix x)))
    :hints(("Goal"
            :in-theory (enable vl-commentmap-entry-p
                               vl-commentmap-entry-list-p))))

  (defthm true-listp-when-vl-commentmap-p
    (implies (vl-commentmap-p x)
             (true-listp x))
    :rule-classes ((:compound-recognizer)
                   (:rewrite :backchain-limit-lst 1))
    :hints(("Goal" :induct (len x))))

  (defthm vl-commentmap-p-of-vl-commentmap-entry-sort
    (implies (vl-commentmap-p x)
             (vl-commentmap-p (vl-commentmap-entry-sort x)))
    :hints(("goal" :use ((:instance vl-commentmap-entry-sort-creates-comparable-listp
                                    (acl2::x x)))))))





(defsection vl-gather-comments
  :parents (vl-commentmap-p)
  :short "Slow, but straightforward routine for gathering all comments between
two locations."

  :long "<p>See also @(see vl-gather-comments-fal), which implements a much faster
routine for gathering comments.</p>"

  (defund vl-gather-comments-aux (min max cmap acc)
    (declare (xargs :guard (and (vl-location-p min)
                                (vl-location-p max)
                                (vl-commentmap-p cmap)
                                (vl-commentmap-p acc))))
    (if (consp cmap)
        (vl-gather-comments-aux min max (cdr cmap)
                                (if (vl-location-between-p (caar cmap) min max)
                                    (cons (car cmap) acc)
                                  acc))
      acc))

  (defthm true-listp-of-vl-gather-comments-aux
    (implies (true-listp acc)
             (true-listp (vl-gather-comments-aux min max cmap acc)))
    :hints(("Goal" :in-theory (enable vl-gather-comments-aux))))

  (defthm vl-commentmap-p-of-vl-gather-comments-aux
    (implies (and (force (vl-commentmap-p acc))
                  (force (vl-commentmap-p cmap)))
             (vl-commentmap-p (vl-gather-comments-aux min max cmap acc)))
    :hints(("Goal" :in-theory (enable vl-gather-comments-aux))))

  (defund vl-gather-comments (min max cmap)
    (declare (xargs :guard (and (vl-location-p min)
                                (vl-location-p max)
                                (vl-commentmap-p cmap))
                    :verify-guards nil))
    (mbe :logic
         (cond ((atom cmap)
                nil)
               ((vl-location-between-p (caar cmap) min max)
                (cons (car cmap)
                      (vl-gather-comments min max (cdr cmap))))
               (t
                (vl-gather-comments min max (cdr cmap))))
         :exec
         (prog2$
          ;; Extralogical warning because it's weird to think about trying to
          ;; gather from a min and max in different files, and because of the
          ;; notion of vl-location-between-p, this will always result in no
          ;; comments.
          (let ((min-filename (vl-location->filename min))
                (max-filename (vl-location->filename max)))
            (or (equal min-filename max-filename)
                (cw "; vl-gather-comments: min/max have different filenames.~%")))

          ;; Actual implementation:
          (reverse (vl-gather-comments-aux min max cmap nil)))))

  (defthm vl-gather-comments-aux-removal
    (implies (true-listp acc)
             (equal (vl-gather-comments-aux min max cmap acc)
                    (revappend (vl-gather-comments min max cmap) acc)))
    :hints(("Goal" :in-theory (enable vl-gather-comments-aux
                                      vl-gather-comments))))

  (verify-guards vl-gather-comments
                 :hints(("Goal" :in-theory (enable vl-gather-comments))))

  (defthm vl-commentmap-p-of-vl-gather-comments
    (implies (force (vl-commentmap-p cmap))
             (vl-commentmap-p (vl-gather-comments min max cmap)))
    :hints(("Goal" :in-theory (enable vl-gather-comments)))))



(defsection vl-commentmap-falp
  :parents (vl-commentmap-p)
  :short "Data structure that supports efficient comment gathering."

  :long "<p>Our initial approach to pretty-printing with comments was to store
all comments in a single comment map, then extract the relevant part of the
comment map when we wanted to print each module.  But profiling indicated that
we were spending 90% of the (considerable) pretty-printing time just gathering
the appropriate comments.</p>

<p>We then decided to attach the comments to each module, once and for all, so
that we never need to look them up during pretty printing.  An advantage of
this is that we can carry out the comment injection before unparameterization,
so that there are fewer lookups to begin with.  Another advantage is that we
can do the comment injection after loading each file, so that we never need to
build a massive comment map spanning all files, but only smaller ones on a
per-file basis.</p>

<p>Even so, individual files can be large.  For a half-million line file, we
obtained a big comment map, and our simple-minded comment gathering scheme was
taking around 20 seconds.  We developed a faster version that threw away
comments after assigning them to a module, but even this was taking 10 seconds
and allocating 1 GB of memory.</p>

<p>To correct for this, we developed a much faster comment gathering mechanism.
The basic idea is to partition the big comment map into an alist that maps each
line number to the subset of the comment map which is about that line.</p>

<p>That is, each entry in our commentmap-fal has the form:</p>

@({
 line --> comment-map
})

<p>where the @('comment-map') has only the comments for this line and, in
practice, is typically a singleton.</p>

<p>To extract all of the comments, we simply walk over the lines between min
and max, gathering their comments.</p>"

  (defund vl-commentmap-lines-agreep (line x)
    (declare (xargs :guard (vl-commentmap-p x)))
    (if (atom x)
        t
      (and (equal (vl-location->line (caar x)) line)
           (vl-commentmap-lines-agreep line (cdr x)))))

  (defthm vl-commentmap-lines-agreep-when-not-consp
    (implies (not (consp x))
             (equal (vl-commentmap-lines-agreep line x)
                    t))
    :hints(("Goal" :in-theory (enable vl-commentmap-lines-agreep))))

  (defthm vl-commentmap-lines-agreep-of-cons
    (equal (vl-commentmap-lines-agreep line (cons a x))
           (and (equal (vl-location->line (car a)) line)
                (vl-commentmap-lines-agreep line x)))
    :hints(("Goal" :in-theory (enable vl-commentmap-lines-agreep))))

  (defund vl-commentmap-falp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (posp (caar x))
           (vl-commentmap-p (cdar x))
           (vl-commentmap-lines-agreep (caar x) (cdar x))
           (vl-commentmap-falp (cdr x)))))

  (defthm vl-commentmap-falp-of-extension
    (implies (and (force (posp line))
                  (force (vl-commentmap-p map))
                  (force (vl-commentmap-lines-agreep line map))
                  (force (vl-commentmap-falp alist)))
             (vl-commentmap-falp (cons (cons line map) alist)))
    :hints(("Goal" :in-theory (enable vl-commentmap-falp))))

  (defthm vl-commentmap-falp-of-hons-shrink-alist
    (implies (and (force (vl-commentmap-falp x))
                  (force (vl-commentmap-falp y)))
             (vl-commentmap-falp (hons-shrink-alist x y)))
    :hints(("Goal" :in-theory (enable vl-commentmap-falp hons-shrink-alist))))

  (defthm vl-commentmap-p-of-hons-assoc-equal
    (implies (vl-commentmap-falp x)
             (equal (vl-commentmap-p (cdr (hons-assoc-equal line x)))
                    t))
    :hints(("Goal" :in-theory (enable vl-commentmap-falp))))

  (defthm vl-commentmap-lines-agreep-of-hons-assoc-equal
    (implies (force (vl-commentmap-falp x))
             (equal (vl-commentmap-lines-agreep line (cdr (hons-assoc-equal line x)))
                    t))
    :hints(("Goal" :in-theory (enable vl-commentmap-falp)))))



(defsection vl-commentmap-fal
  :parents (vl-commentmap-p)
  :short "Construct the @(see vl-commentmap-falp) for a @(see vl-commentmap-p)."
  :long "<p>Note: returns a fast alist.</p>"

  (defund vl-commentmap-fal-aux (x alist)
    (declare (xargs :guard (vl-commentmap-p x)))
    (if (atom x)
        alist
      (let* ((line  (vl-location->line (caar x)))
             (curr  (cdr (hons-get line alist)))
             (alist (hons-acons line (cons (car x) curr) alist)))
        (vl-commentmap-fal-aux (cdr x) alist))))

  (defthm consp-of-vl-commentmap-fal-aux
    (equal (consp (vl-commentmap-fal-aux x alist))
           (or (consp alist)
               (consp x)))
    :hints(("Goal" :in-theory (e/d (vl-commentmap-fal-aux)
                                   ((force))))))

  (defthm vl-commentmap-falp-of-vl-commentmap-fal-aux
    (implies (and (vl-commentmap-p x)
                  (vl-commentmap-falp alist))
             (vl-commentmap-falp (vl-commentmap-fal-aux x alist)))
    :hints(("Goal"
            :induct (vl-commentmap-fal-aux x alist)
            :in-theory (enable vl-commentmap-fal-aux))))

  (defund vl-commentmap-fal (x)
    (declare (xargs :guard (vl-commentmap-p x)))
    (b* ((alist1 (vl-commentmap-fal-aux x nil))
         (alist2 (hons-shrink-alist alist1 nil))
         (- (flush-hons-get-hash-table-link alist1)))
        alist2))

  (defthm vl-commentmap-falp-of-vl-commentmap-fal
    (implies (vl-commentmap-p x)
             (vl-commentmap-falp (vl-commentmap-fal x)))
    :hints(("Goal" :in-theory (enable vl-commentmap-fal)))))



(defsection vl-gather-comments-fal
  :parents (vl-commentmap-p)
  :short "Efficient routine for gathering comments using an @(see vl-commentmap-falp)."

  (defund vl-gather-comments-fal-aux (minl maxl n min max fal acc)
    (declare (xargs :guard (and (natp n)
                                (natp minl)
                                (natp maxl)
                                (vl-location-p min)
                                (vl-location-p max)
                                (= (vl-location->line min) minl)
                                (= (vl-location->line max) maxl)
                                (<= minl n)
                                (<= n maxl)
                                (vl-commentmap-falp fal)
                                (vl-commentmap-p acc))
                    :verify-guards nil
                    :measure (nfix (- (nfix n) (nfix minl)))))
    (let* ((entry (hons-get n fal))
           (acc   (if entry
                      (vl-gather-comments-aux min max (cdr entry) acc)
                    acc)))
      (if (mbe :logic (zp (- (nfix n) (nfix minl)))
               :exec (= n minl))
          acc
        (vl-gather-comments-fal-aux minl maxl (- n 1) min max fal acc))))

  (verify-guards vl-gather-comments-fal-aux
                 :hints(("goal" :use ((:instance return-type-of-vl-location->line
                                                 (x min))))))

  (defthm vl-commentmap-p-of-vl-gather-comments-fal-aux
    (implies (and (vl-commentmap-p acc)
                  (vl-commentmap-falp fal))
             (vl-commentmap-p (vl-gather-comments-fal-aux minl maxl n min max fal acc)))
    :hints(("Goal" :in-theory (enable vl-gather-comments-fal-aux))))

  (defun vl-gather-comments-fal (min max fal)
    (declare (xargs :guard (and (vl-location-p min)
                                (vl-location-p max)
                                (<= (vl-location->line min)
                                    (vl-location->line max))
                                (vl-commentmap-falp fal))))
    (let ((minl (vl-location->line min))
          (maxl (vl-location->line max)))
      (vl-gather-comments-fal-aux minl maxl maxl min max fal nil))))



(define vl-inject-comments-module
  :parents (vl-commentmap-p)
  ((x   vl-module-p        "Module to inject some comments into.")
   (fal vl-commentmap-falp "All comments, gathered before parsing."))
  :returns (new-x vl-module-p :hyp :fguard
                  "Same as @('x'), but with comments added.")
  (b* (((when (vl-module->hands-offp x))
        x)
       (minloc  (vl-module->minloc x))
       (maxloc  (vl-module->maxloc x))
       ((unless (<= (vl-location->line minloc) (vl-location->line maxloc)))
        (let ((warnings (warn :type :vl-warn-comment-injection
                              :msg "Cannot add comments, minloc exceeds maxloc?~% ~
                                    minloc = ~l0; maxloc = ~l1."
                              :args (list minloc maxloc)
                              :acc (vl-module->warnings x))))
          (change-vl-module x :warnings warnings)))
       (comments (vl-gather-comments-fal minloc maxloc fal)))
    (if (not comments)
        x
      (change-vl-module x :comments comments)))
  ///
  (defthm vl-module->name-of-vl-inject-comments-module
    (equal (vl-module->name (vl-inject-comments-module x comment-map))
           (vl-module->name x))))


(defprojection vl-inject-comments-modulelist-aux (x fal)
  (vl-inject-comments-module x fal)
  :guard (and (vl-modulelist-p x)
              (vl-commentmap-falp fal))
  :result-type vl-modulelist-p
  :parents (vl-commentmap-p)
  :rest
  ((defthm vl-modulelist->names-of-vl-inject-comments-modulelist-aux
     (equal (vl-modulelist->names (vl-inject-comments-modulelist-aux x comment-map))
            (vl-modulelist->names x)))))


(define vl-inject-comments-modulelist
  :parents (vl-commentmap-p)
  :short "Associate all comments with their modules."
  ((x           vl-modulelist-p "Parsed modules.")
   (comment-map vl-commentmap-p "Comments gathered before parsing."))
  :returns (new-x vl-modulelist-p :hyp :fguard
                  "Parsed modules with their comments attached.")
  (b* ((fal (vl-commentmap-fal comment-map))
       (ret (vl-inject-comments-modulelist-aux x fal)))
    (fast-alist-free fal)
    ret)
  ///
  (defthm vl-modulelist->names-of-vl-inject-comments-modulelist
    (equal (vl-modulelist->names (vl-inject-comments-modulelist x comment-map))
           (vl-modulelist->names x))))


;; BELOW THIS LINE THERE ARE ONLY COMMENTS.


#||


; Here are some alternate approaches we tried.

; This was pretty good, and took about 10 seconds for top.v but allocated
; almost a gigabyte.

(defund vl-fast-extract-comments (min max cmap mine yours)
  "Returns (MV MINE YOURS)"
  (declare (xargs :guard (and (vl-location-p min)
                              (vl-location-p max)
                              (vl-commentmap-p cmap)
                              (vl-commentmap-p mine)
                              (vl-commentmap-p yours))))

; We split up the comment map into two sections:
;   - mine are the comments between min and max
;   - yours are any other comments

  (cond ((atom cmap)
         (mv mine yours))
        ((vl-location-between-p (caar cmap) min max)
         (vl-fast-extract-comments min max (cdr cmap) (cons (car cmap) mine) yours))
        (t
         (vl-fast-extract-comments min max (cdr cmap) mine (cons (car cmap) yours)))))

(defthm true-listp-of-vl-fast-extract-comments-1
  (equal (true-listp (first (vl-fast-extract-comments min max cmap mine yours)))
         (true-listp mine))
  :hints(("Goal" :in-theory (enable vl-fast-extract-comments))))

(defthm true-listp-of-vl-fast-extract-comments-2
  (equal (true-listp (second (vl-fast-extract-comments min max cmap mine yours)))
         (true-listp yours))
  :hints(("Goal" :in-theory (enable vl-fast-extract-comments))))

(defund vl-extract-comments (min max cmap)
  "Returns (MV MINE YOURS)"
  (declare (xargs :guard (and (vl-location-p min)
                              (vl-location-p max)
                              (vl-commentmap-p cmap))
                  :verify-guards nil))

; This function nicely maintains the order of cmap.  So, if you sort the thing
; to begin with, both mine and yours will still be in order.

  (mbe :logic
       (if (atom cmap)
           (mv nil nil)
         (mv-let (mine yours)
                 (vl-extract-comments min max (cdr cmap))
                 (if (vl-location-between-p (caar cmap) min max)
                     (mv (cons (car cmap) mine) yours)
                   (mv mine (cons (car cmap) yours)))))
       :exec
       (mv-let (mine yours)
               (vl-fast-extract-comments min max cmap nil nil)
               ;; Efficiency hack: don't do reversals if mine is empty.
               (if (not mine)
                   (mv nil cmap)
                 (mv (reverse mine) (reverse yours))))))

(defthm true-listp-of-vl-extract-comments-1
  (true-listp (first (vl-extract-comments min max cmap)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-extract-comments))))

(defthm true-listp-of-vl-extract-comments-2
  (true-listp (second (vl-extract-comments min max cmap)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-extract-comments))))

(encapsulate
 ()
 (local (defthm guard-lemma-1
          (implies (true-listp mine)
                   (equal (first (vl-fast-extract-comments min max cmap mine yours))
                          (revappend (first (vl-extract-comments min max cmap)) mine)))
          :hints(("Goal" :in-theory (enable vl-extract-comments vl-fast-extract-comments)))))

 (local (defthm guard-lemma-2
          (implies (true-listp mine)
                   (equal (second (vl-fast-extract-comments min max cmap mine yours))
                          (revappend (second (vl-extract-comments min max cmap)) yours)))
          :hints(("Goal" :in-theory (enable vl-extract-comments vl-fast-extract-comments)))))

 (local (defthm guard-lemma-3
          (implies (not (first (vl-extract-comments min max cmap)))
                   (equal (second (vl-extract-comments min max cmap))
                          (list-fix cmap)))
          :hints(("Goal" :in-theory (enable vl-extract-comments)))))

 (local (defthm equal-of-cons-rewrite
          (equal (equal (cons a b) x)
                 (and (consp x)
                      (equal a (car x))
                      (equal b (cdr x))))))

 (verify-guards vl-extract-comments
                :hints(("Goal" :in-theory (enable vl-extract-comments)))))

(defthm vl-commentmap-p-of-vl-extract-comments-1
  (implies (and (force (vl-commentmap-p cmap))
                (force (vl-commentmap-p mine)))
           (vl-commentmap-p (first (vl-extract-comments min max cmap))))
  :hints(("Goal" :in-theory (enable vl-extract-comments))))

(defthm vl-commentmap-p-of-vl-extract-comments-2
  (implies (and (force (vl-commentmap-p cmap))
                (force (vl-commentmap-p yours)))
           (vl-commentmap-p (second (vl-extract-comments min max cmap))))
  :hints(("Goal" :in-theory (enable vl-extract-comments))))



(defund vl-inject-comments-module (x cmap)
  "Returns (X-PRIME CMAP-PRIME)"
  (declare (xargs :guard (and (vl-module-p x)
                              (vl-commentmap-p cmap))))
  (b* ((minloc          (vl-module->minloc x))
       (maxloc          (vl-module->maxloc x))
       ((mv mine yours) (vl-extract-comments minloc maxloc cmap)))
      (if (not mine)
          (mv x cmap)
        (mv (change-vl-module x :comments mine)
            yours))))

(defthm vl-module-p-of-vl-inject-comments-module-1
  (implies (and (force (vl-module-p x))
                (force (vl-commentmap-p cmap)))
           (vl-module-p (first (vl-inject-comments-module x cmap))))
  :hints(("Goal" :in-theory (enable vl-inject-comments-module))))

(defthm vl-commentmap-p-of-vl-inject-comments-module-2
  (implies (and (force (vl-module-p x))
                (force (vl-commentmap-p cmap)))
           (vl-commentmap-p (second (vl-inject-comments-module x cmap))))
  :hints(("Goal" :in-theory (enable vl-inject-comments-module))))


(defund vl-inject-comments-modulelist (x cmap)
  (declare (xargs :guard (and (vl-modulelist-p x)
                              (vl-commentmap-p cmap))))
  (if (atom x)
      nil
    (mv-let (car-prime cmap)
            (vl-inject-comments-module (car x) cmap)
            (cons car-prime
                  (vl-inject-comments-modulelist (cdr x) cmap)))))

(defthm vl-modulelist-p-of-vl-inject-comments-modulelist
  (implies (and (force (vl-modulelist-p x))
                (force (vl-commentmap-p cmap)))
           (vl-modulelist-p (vl-inject-comments-modulelist x cmap)))
  :hints(("Goal" :in-theory (enable vl-inject-comments-modulelist))))



; Just using gather-comments directly took about 20 seconds but involved
; almost no allocation

(defund vl-inject-comments-module (x cmap)
  "Returns (X-PRIME CMAP-PRIME)"
  (declare (xargs :guard (and (vl-module-p x)
                              (vl-commentmap-p cmap))))
  (b* ((minloc  (vl-module->minloc x))
       (maxloc  (vl-module->maxloc x))
       (mine    (vl-gather-comments minloc maxloc cmap)))
      (mv (if mine
              (change-vl-module x :comments mine)
            x)
          cmap)))


; Eventually I would like to prove that vl-gather-comments-fal is the same as
; vl-gather-comments.  The claim would probably be something like this, except
; that we probably also need to know that the comment map is sorted.

;; (defthm crock
;;   (implies (and (vl-location-p min)
;;                 (vl-location-p max)
;;                 (<= (vl-location->line min) (vl-location->line max))
;;                 (vl-commentmap-p cmap))
;;            (equal (vl-gather-comments-fal min max (vl-commentmap-fal cmap))
;;                   (vl-gather-comments min max cmap))))

; Here is a simple test that at least shows the above theorem is possibly true.

(defconst *cmap*
  '(((:vl-location "file" 1 . 0) . "// Comment a1")
    ((:vl-location "file" 1 . 1) . "// Comment a2")
    ((:vl-location "file" 1 . 2) . "// Comment a3")
    ((:vl-location "file" 2 . 0) . "// Comment b1")
    ((:vl-location "file" 2 . 1) . "// Comment b2")
    ((:vl-location "file" 2 . 2) . "// Comment b3")))

(vl-gather-comments
 '(:vl-location "file" 1 . 0)
 '(:vl-location "file" 3 . 0)
 *cmap*)

(vl-gather-comments-fal
 '(:vl-location "file" 1 . 0)
 '(:vl-location "file" 3 . 0)
 (vl-commentmap-fal *cmap*))

; And below are some fledgling efforts toward trying to show this, but I do not
; have a real proof in mind yet and there are other important things to do.

(defund vl-slice-comment-map (line x)
  (declare (xargs :guard (and (posp line)
                              (vl-commentmap-p x))))
  (cond ((atom x)
         nil)
        ((equal line (vl-location->line (caar x)))
         (cons (car x) (vl-slice-comment-map line (cdr x))))
        (t
         (vl-slice-comment-map line (cdr x)))))

(defthm vl-slice-comment-map-when-not-consp
  (implies (not (consp x))
           (equal (vl-slice-comment-map line x)
                  nil))
  :hints(("Goal" :in-theory (enable vl-slice-comment-map))))

(defthm vl-slice-comment-map-of-cons
  (equal (vl-slice-comment-map line (cons a x))
         (if (equal (vl-location->line (car a)) line)
             (cons a (vl-slice-comment-map line x))
           (vl-slice-comment-map line x)))
  :hints(("Goal" :in-theory (enable vl-slice-comment-map))))

(defthm cdr-of-hons-assoc-equal-of-vl-commentmap-fal-aux
  (implies (and (vl-commentmap-p cmap)
                (vl-commentmap-falp alist))
           (equal (cdr (hons-assoc-equal line (vl-commentmap-fal-aux cmap alist)))
                  (revappend (vl-slice-comment-map line cmap)
                             (cdr (hons-assoc-equal line alist)))))
  :hints(("Goal"
          :in-theory (enable vl-commentmap-fal-aux)
          :do-not '(generalize fertilize))))

(defthm vl-commentmap-p-of-vl-slice-comment-map
  (implies (force (vl-commentmap-p x))
           (vl-commentmap-p (vl-slice-comment-map line x)))
  :hints(("Goal" :induct (len x))))

(defthm type-of-vl-location->line
  (implies (force (vl-location-p x))
           (posp (vl-location->line x)))
  :rule-classes :type-prescription)

(defund vl-slice-gather-comments (min max n x)
  (declare (xargs :guard (and (vl-location-p min)
                              (vl-location-p max)
                              (natp n)
                              (<= (vl-location->line min) n)
                              (<= n (vl-location->line max))
                              (vl-commentmap-p x))
                  :hints(("Goal" :in-theory (disable (force))))
                  :measure (nfix (- (nfix n)
                                    (nfix (vl-location->line min))))))
  (let* ((slice          (vl-slice-comment-map n x))
         (slice-comments (vl-gather-comments min max slice)))
    (if (zp (- (nfix n) (nfix (vl-location->line min))))
        slice-comments
      (append slice-comments
              (vl-slice-gather-comments min max (- (nfix n) 1) x)))))

(defthm vl-slice-gather-comments-correct
  (implies (and (vl-location-p min)
                (vl-location-p max)
                (natp n)
                (<= (vl-location->line min) n)
                (<= n (vl-location->line max)))
           (equal (vl-slice-gather-comments min max n x)
                  (vl-gather-comments min max x)))
  :hints(("Goal" :in-theory (enable vl-slice-gather-comments
                                    vl-gather-comments))))

(defund vl-naive-gather-comments-fal (min max fal)
  (declare (xargs :guard (and (vl-location-p min)
                              (vl-location-p max)
                              (vl-commentmap-falp fal))))
  (if (atom fal)
      nil
    (append (vl-gather-comments min max (cdar fal))
            (vl-naive-gather-comments-fal min max (cdr fal)))))


||#

