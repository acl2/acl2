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
(include-book "descriptions")
(local (include-book "../util/arithmetic"))
(local (xdoc::set-default-parents vl-commentmap-p))

(define vl-gather-comments-nrev ((min vl-location-p)
                                 (max vl-location-p)
                                 (cmap vl-commentmap-p)
                                 nrev)
  :parents (vl-gather-comments)
  (b* (((when (atom cmap))
        (nrev-fix nrev))
       (nrev (if (vl-location-between-p (caar cmap) min max)
                 (nrev-push (car cmap) nrev)
               nrev)))
    (vl-gather-comments-nrev min max (cdr cmap) nrev)))

(define vl-gather-comments
  :short "Slow, but straightforward routine for gathering all comments between
two locations."
  ((min vl-location-p)
   (max vl-location-p)
   (cmap vl-commentmap-p))
  :long "<p>See also @(see vl-gather-comments-fal), which implements a much faster
routine for gathering comments.</p>"
  :verify-guards nil
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
        (if (atom cmap)
            nil
          (with-local-nrev
            (vl-gather-comments-nrev min max cmap nrev)))))
  ///
  (defthm vl-gather-comments-nrev-removal
    (equal (vl-gather-comments-nrev min max cmap nrev)
           (append nrev (vl-gather-comments min max cmap)))
    :hints(("Goal" :in-theory (enable vl-gather-comments-nrev))))

  (verify-guards vl-gather-comments)

  (defthm vl-commentmap-p-of-vl-gather-comments
    (implies (force (vl-commentmap-p cmap))
             (vl-commentmap-p (vl-gather-comments min max cmap)))))


(define vl-commentmap-lines-agreep
  :parents (vl-commentmap-falp)
  ((line posp)
   (x    vl-commentmap-p))
  (if (atom x)
      t
    (and (equal (vl-location->line (caar x)) line)
         (vl-commentmap-lines-agreep line (cdr x))))
  ///
  (defthm vl-commentmap-lines-agreep-when-not-consp
    (implies (not (consp x))
             (equal (vl-commentmap-lines-agreep line x)
                    t)))

  (defthm vl-commentmap-lines-agreep-of-cons
    (equal (vl-commentmap-lines-agreep line (cons a x))
           (and (equal (vl-location->line (car a)) line)
                (vl-commentmap-lines-agreep line x)))))



(define vl-commentmap-falp (x)
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

  (if (atom x)
      (not x)
    (and (consp (car x))
         (posp (caar x))
         (vl-commentmap-p (cdar x))
         (vl-commentmap-lines-agreep (caar x) (cdar x))
         (vl-commentmap-falp (cdr x))))
  ///
  (defthm vl-commentmap-falp-of-extension
    (implies (and (force (posp line))
                  (force (vl-commentmap-p map))
                  (force (vl-commentmap-lines-agreep line map))
                  (force (vl-commentmap-falp alist)))
             (vl-commentmap-falp (cons (cons line map) alist))))

  (defthm vl-commentmap-falp-of-hons-shrink-alist
    (implies (and (force (vl-commentmap-falp x))
                  (force (vl-commentmap-falp y)))
             (vl-commentmap-falp (hons-shrink-alist x y)))
    :hints(("Goal" :in-theory (enable hons-shrink-alist))))

  (defthm vl-commentmap-falp-of-append
    (implies (and (force (vl-commentmap-falp x))
                  (force (vl-commentmap-falp y)))
             (vl-commentmap-falp (append x y))))

  (defthm vl-commentmap-p-of-hons-assoc-equal
    (implies (vl-commentmap-falp x)
             (equal (vl-commentmap-p (cdr (hons-assoc-equal line x)))
                    t)))

  (defthm vl-commentmap-lines-agreep-of-hons-assoc-equal
    (implies (force (vl-commentmap-falp x))
             (equal (vl-commentmap-lines-agreep line (cdr (hons-assoc-equal line x)))
                    t))))



(define vl-commentmap-fal-aux
  :parents (vl-commentmap-fal)
  :short "Construct the @(see vl-commentmap-falp) for a @(see vl-commentmap-p)."
  ((x     vl-commentmap-p "Commentmap we're processing.")
   (alist "The fast alist we're extending."))
  (b* (((when (atom x))
        alist)
       (line  (vl-location->line (caar x)))
       (curr  (cdr (hons-get line alist)))
       (alist (hons-acons line (cons (car x) curr) alist)))
    (vl-commentmap-fal-aux (cdr x) alist))
  ///
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
            :in-theory (enable vl-commentmap-fal-aux)))))

(define vl-commentmap-fal ((x vl-commentmap-p))
  :returns (commentmap-fal vl-commentmap-falp)
  :hooks (:fix)
  (b* ((x      (vl-commentmap-fix x))
       (alist1 (vl-commentmap-fal-aux x nil))
       (alist2 (hons-shrink-alist alist1 nil)))
    (fast-alist-free alist1)
    alist2))


(define vl-gather-comments-fal-nrev
  :parents (vl-gather-comments-fal)
  ((minl natp)
   (maxl natp)
   (n natp)
   (min vl-location-p)
   (max vl-location-p)
   (fal vl-commentmap-falp)
   (nrev))
  :guard (and (eql (vl-location->line min) minl)
              (eql (vl-location->line max) maxl)
              (<= minl n)
              (<= n maxl))
  :measure (nfix (- (nfix n) (nfix minl)))
  (b* ((entry (hons-get n fal))
       (nrev  (if entry
                  (vl-gather-comments-nrev min max (cdr entry) nrev)
                nrev))
       ((when (mbe :logic (zp (- (nfix n) (nfix minl)))
                   :exec (eql n minl)))
        (nrev-fix nrev)))
    (vl-gather-comments-fal-nrev minl maxl (- n 1) min max fal nrev))
  ///
  (defthm vl-commentmap-p-of-vl-gather-comments-fal-nrev
    (implies (and (vl-commentmap-p nrev)
                  (vl-commentmap-falp fal))
             (vl-commentmap-p (vl-gather-comments-fal-nrev minl maxl n min max fal nrev)))))

(define vl-gather-comments-fal
  :short "Efficient routine for gathering comments using an @(see vl-commentmap-falp)."
  ((min vl-location-p)
   (max vl-location-p)
   (fal vl-commentmap-falp))
  :guard (<= (vl-location->line min)
             (vl-location->line max))
  (b* ((minl (vl-location->line min))
       (maxl (vl-location->line max)))
    (with-local-nrev
      (vl-gather-comments-fal-nrev minl maxl maxl min max fal nrev)))
  ///
  (defthm vl-commentmap-p-of-vl-gather-comments-fal
    (implies (force (vl-commentmap-falp fal))
             (vl-commentmap-p (vl-gather-comments-fal min max fal)))))



; Actually injecting the comments is gross.  When we only had modules this was
; pretty straightforward.  But now there are other kinds of top-level
; descriptions, and some of them don't have any comments of their own.

(define vl-description-has-comments-p ((x vl-description-p))
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      ((:vl-module :vl-udp :vl-interface :vl-package :vl-program
        :vl-class :vl-config :vl-typedef)
       t)
      (otherwise
       nil))))

(local (in-theory (enable vl-description-has-comments-p)))

(define vl-description->minloc ((x vl-description-p))
  :returns (minloc vl-location-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->minloc x))
      (:vl-udp       (vl-udp->minloc x))
      (:vl-interface (vl-interface->minloc x))
      (:vl-package   (vl-package->minloc x))
      (:vl-program   (vl-program->minloc x))
      (:vl-class     (vl-class->minloc x))
      (:vl-config    (vl-config->minloc x))
      (:vl-typedef   (vl-typedef->minloc x))
      ;; Other things don't necessarily have minlocs, but we'll just use their
      ;; ordinary locations.
      (:vl-vardecl    (vl-vardecl->loc x))
      (:vl-taskdecl   (vl-taskdecl->loc x))
      (:vl-fundecl    (vl-fundecl->loc x))
      (:vl-paramdecl  (vl-paramdecl->loc x))
      (:vl-import     (vl-import->loc x))
      (:vl-fwdtypedef (vl-fwdtypedef->loc x))
      (:vl-dpiimport  (vl-dpiimport->loc x))
      (:vl-dpiexport  (vl-dpiexport->loc x))
      (:vl-bind       (vl-bind->loc x))
      (:vl-property   (vl-property->loc x))
      (:vl-sequence   (vl-sequence->loc x))
      (otherwise      (progn$ (impossible) *vl-fakeloc*)))))

(define vl-description->maxloc ((x vl-description-p))
  :returns (maxloc vl-location-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->maxloc x))
      (:vl-udp       (vl-udp->maxloc x))
      (:vl-interface (vl-interface->maxloc x))
      (:vl-package   (vl-package->maxloc x))
      (:vl-program   (vl-program->maxloc x))
      (:vl-class     (vl-class->maxloc x))
      (:vl-config    (vl-config->maxloc x))
      (:vl-typedef   (vl-typedef->maxloc x))
      ;; Other things don't have separate min/max locs, but we'll just use
      ;; their ordinary locations.
      (:vl-vardecl    (vl-vardecl->loc x))
      (:vl-taskdecl   (vl-taskdecl->loc x))
      (:vl-fundecl    (vl-fundecl->loc x))
      (:vl-paramdecl  (vl-paramdecl->loc x))
      (:vl-import     (vl-import->loc x))
      (:vl-fwdtypedef (vl-fwdtypedef->loc x))
      (:vl-dpiimport  (vl-dpiimport->loc x))
      (:vl-dpiexport  (vl-dpiexport->loc x))
      (:vl-bind       (vl-bind->loc x))
      (:vl-property   (vl-property->loc x))
      (:vl-sequence   (vl-sequence->loc x))
      (otherwise      (progn$ (impossible) *vl-fakeloc*)))))

(define vl-description->comments ((x vl-description-p))
  :guard (vl-description-has-comments-p x)
  :returns (comments vl-commentmap-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->comments x))
      (:vl-udp       (vl-udp->comments x))
      (:vl-interface (vl-interface->comments x))
      (:vl-package   (vl-package->comments x))
      (:vl-program   (vl-program->comments x))
      (:vl-class     (vl-class->comments x))
      (:vl-config    (vl-config->comments x))
      (:vl-typedef   (vl-typedef->comments x))
      (otherwise     (impossible)))))

(define vl-description-add-warning ((x vl-description-p)
                                    (warning vl-warning-p))
  :guard (vl-description-has-comments-p x)
  :returns (new-x vl-description-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (change-vl-module    x :warnings (cons warning (vl-module->warnings x))))
      (:vl-udp       (change-vl-udp       x :warnings (cons warning (vl-udp->warnings x))))
      (:vl-interface (change-vl-interface x :warnings (cons warning (vl-interface->warnings x))))
      (:vl-package   (change-vl-package   x :warnings (cons warning (vl-package->warnings x))))
      (:vl-program   (change-vl-program   x :warnings (cons warning (vl-program->warnings x))))
      (:vl-class     (change-vl-class     x :warnings (cons warning (vl-class->warnings x))))
      (:vl-config    (change-vl-config    x :warnings (cons warning (vl-config->warnings x))))
      (:vl-typedef   (change-vl-typedef   x :warnings (cons warning (vl-typedef->warnings x))))
      (otherwise     (progn$ (impossible) x))))
  ///
  (defthm vl-description->name-of-vl-description-add-warning
    (equal (vl-description->name (vl-description-add-warning x warning))
           (vl-description->name x))
    :hints(("Goal" :in-theory (enable vl-description->name)))))


(define vl-description-set-comments ((x        vl-description-p)
                                     (comments vl-commentmap-p))
  :guard (vl-description-has-comments-p x)
  :returns (new-x vl-description-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (change-vl-module    x :comments comments))
      (:vl-udp       (change-vl-udp       x :comments comments))
      (:vl-interface (change-vl-interface x :comments comments))
      (:vl-package   (change-vl-package   x :comments comments))
      (:vl-program   (change-vl-program   x :comments comments))
      (:vl-class     (change-vl-class     x :comments comments))
      (:vl-config    (change-vl-config    x :comments comments))
      (:vl-typedef   (change-vl-typedef   x :comments comments))
      (otherwise     (progn$ (impossible) x))))
  ///
  (defthm vl-description->name-of-vl-description-set-comments
    (equal (vl-description->name (vl-description-set-comments x comments))
           (vl-description->name x))
    :hints(("Goal" :in-theory (enable vl-description->name)))))



(define vl-adjust-minloc-for-comments
  :short "Tweak starting location so that we get comments preceding the
          @('module') keyword."
  ((acc     vl-location-p        "Initially line 0 of the file.")
   (minloc  vl-location-p        "True @('minloc') of the module we're considering.")
   (descs   vl-descriptionlist-p "All top-level descriptions found in the file."))
  :returns (adjusted-minloc vl-location-p :hyp :guard)
  :long "<p>It turns out that useful comments about a module (or other kind of
top-level description) are often put <b>before</b> the module instead of within
it.  For instance:</p>

@({
    // Module: SuchAndSo
    // Author: John Q. Designer
    // Purpose: This module is responsible for blah blah blah.  It
    //          interfaces with units blah and blah, and implements ...
    // ...
    module SuchAndSo (...) ;
      ...
    endmodule
})

<p>This is especially common when modules are written in separate files, and
the comments describing the module are found at the top.  Unfortunately, our
basic approach to comment gathering&mdash;associating all comments between
@('module') and @('endmodule')&mdash;misses these comments.</p>

<p>To correct for this, we no longer use the actual @('minloc') for the module.
Instead, we (almost) choose the largest @('maxloc') of any <i>other</i> module
such that @('other-maxloc < minloc').  That sounds like gibberish but it makes
sense if you just draw what portion of the file you want:</p>

@({
     module foo1 (...);
      ...
     endmodule

     module foo2 (...);
      ...
     endmodule              <-- largest maxloc less than minloc of bar

     // helpful comments about module bar, which we
     // want to make sure are associated with bar.
     module bar (...);
      ...
     endmodule
})

<p>Well, we don't <i>quite</i> use the maxloc of the previous module.  Instead,
we use <i>maxloc+1</i>.  The reason for this is that sometimes people put in
really stupid comments after @('end') keywords, such as:</p>

@({
    module foo (...);
      ...
    endmodule // foo
})

<p>And we don't want to associate this @('// foo') comment with the subsequent
module.</p>"

  (b* (((when (atom descs))
        acc)
       (mod1.maxloc (vl-description->maxloc (car descs)))
       ((unless (and
                 ;; The other module needs to be in the same file,
                 ;; or we don't care about it.
                 (equal (vl-location->filename acc)
                        (vl-location->filename mod1.maxloc))
                 ;; The other module must come BEFORE us, or we don't
                 ;; care about it.
                 (< (vl-location->line mod1.maxloc)
                    (vl-location->line minloc))
                 ;; The other module must be PAST our current max,
                 ;; or we don't care about it.
                 (< (vl-location->line acc)
                    (vl-location->line mod1.maxloc))))
        (vl-adjust-minloc-for-comments acc minloc (cdr descs)))
       ;; Else, mod1.maxloc is better than what we have now.
       (acc (change-vl-location acc
                                ;; Goofy computation ensures we never go backwards,
                                ;; in case of one-line module ... endmodule stuff.
                                :line (min (+ 1 (vl-location->line mod1.maxloc))
                                           (vl-location->line minloc)))))
    (vl-adjust-minloc-for-comments acc minloc (cdr descs)))
  ///
  (defthm bound-of-vl-adjust-minloc-for-comments
    (implies (and (<= (vl-location->line acc) (vl-location->line minloc))
                  (force (vl-location-p acc))
                  (force (vl-location-p minloc))
                  (force (vl-descriptionlist-p descs)))
             (<= (vl-location->line (vl-adjust-minloc-for-comments acc minloc descs))
                 (vl-location->line minloc)))
    :rule-classes ((:rewrite) (:linear))))


(define vl-description-inject-comments
  :parents (vl-commentmap-p)
  ((x         vl-description-p
              "Description to inject some comments into.")
   (fal       vl-commentmap-falp
              "All comments, gathered before parsing.")
   (all-descs vl-descriptionlist-p
              "All descriptions, used to adjust starting locations."))
  :returns (new-x vl-description-p "Same as @('x'), but with comments added.")
  (b* (;; When we only supported modules, we respected hands-off here.  But
       ;; I don't think there's any reason to worry about that.
       (x       (vl-description-fix x))
       ((unless (vl-description-has-comments-p x))
        ;; Something too simple like a net declaration, no comments anyway.
        x)
       (minloc  (vl-description->minloc x))
       (maxloc  (vl-description->maxloc x))
       ((unless (<= (vl-location->line minloc) (vl-location->line maxloc)))
        (let ((w (make-vl-warning :type :vl-warn-comment-injection
                                  :msg "Cannot add comments, minloc exceeds ~
                                        maxloc?~% minloc = ~l0; maxloc = ~l1."
                                  :args (list minloc maxloc)
                                  :fatalp nil
                                  :fn __function__)))
          (vl-description-add-warning x w)))
       (minloc (vl-adjust-minloc-for-comments (change-vl-location minloc :line 1)
                                              minloc all-descs))
       (comments (vl-gather-comments-fal minloc maxloc fal)))
    (if (not comments)
        x
      (vl-description-set-comments x comments)))
  ///
  (defthm vl-description->name-of-vl-description-inject-comments
    (equal (vl-description->name (vl-description-inject-comments x comment-map all-mods))
           (vl-description->name x))))

(defprojection vl-descriptionlist-inject-comments-aux ((x         vl-descriptionlist-p)
                                                       (fal       vl-commentmap-falp)
                                                       (all-descs vl-descriptionlist-p))
  :returns (new-x vl-descriptionlist-p)
  (vl-description-inject-comments x fal all-descs)
  ///
  (defthm vl-descriptionlist->names-of-vl-descriptionlist-inject-comments-aux
    (equal (vl-descriptionlist->names (vl-descriptionlist-inject-comments-aux x fal all-descs))
           (vl-descriptionlist->names x))))

(define vl-descriptionlist-inject-comments
  :parents (vl-commentmap-p)
  :short "Associate all comments with their modules/interfaces/etc."
  ((x           vl-descriptionlist-p "Parsed modules, packages, etc.")
   (comment-map vl-commentmap-p      "Comments gathered before parsing."))
  :returns
  (new-x vl-descriptionlist-p "Parsed descriptions with their comments attached.")
  (b* ((comment-map
        ;; Subtle.  We sort all the comments.  This sorting isn't useful for
        ;; the comment-injection algorithm, but is only meant to remove
        ;; duplicates.
        ;;
        ;; You might wonder: why in the world would there be duplicate entries
        ;; in the comment map?  After all, it's an alist that binds locations
        ;; to strings.  So wouldn't there only be duplicates if we've read the
        ;; same lines of code multiple times?  Yes.  So why would we be doing
        ;; that???
        ;;
        ;; The problem is that files can be `included in multiple places.
        ;;
        ;; Recall how `include works: when we encounter `include "foo_if.sv",
        ;; we are to grab the entire contents of foo_if.sv and essentially
        ;; paste them down into the superior file.  This is an extremely dumb
        ;; process that doesn't, e.g., remember what files it has already
        ;; loaded.  Because of this, a widely `included "header" file ends up
        ;; getting replicated every time it is used.
        ;;
        ;; Normally, such header files will have "include guards" to ensure
        ;; that the real contents of such a header are only really included
        ;; into the design once.  For instance, a typical header might look
        ;; like this:
        ;;
        ;;    // foo_if.sv
        ;;    // Copyright (C) 2014 Centaur Technology
        ;;    // ... more copyright information, authorship, etc ...
        ;;
        ;;    `ifndef INCLUDED_FOO_INTERFACE
        ;;    `define INCLUDED_FOO_INTERFACE
        ;;
        ;;    interface foo ...
        ;;      ...
        ;;    endinterface
        ;;
        ;;    `endif
        ;;
        ;; The `ifndef stuff ensures that the actual definition of "foo" will
        ;; not be replicated.  However, since the copyright comments here are
        ;; not put underneath the include guard, they are essentially going to
        ;; be replicated every time that this header is included!
        ;;
        ;; So, to deal with this kind of replication, we sort the comments to
        ;; remove the duplicates before attaching them to their associated
        ;; modules, etc.
        (mergesort comment-map))
       (fal (vl-commentmap-fal comment-map))
       (ret (vl-descriptionlist-inject-comments-aux x fal x)))
    (fast-alist-free fal)
    ret)
  ///
  (defthm vl-descriptionlist->names-of-vl-descriptionlist-inject-comments
    (equal (vl-descriptionlist->names (vl-descriptionlist-inject-comments x comment-map))
           (vl-descriptionlist->names x))))

; BOZO we currently leave some comments unaccounted for.  For instance,
; consider something like:
;
;    module foo ... endmodule
;
;    // comment about the import
;    import mypkg::name;
;
;    // comment about bar
;    module bar ... endmodule
;
; Here we'll get the comment about bar and associate it with bar.  However,
; since imports don't have comments, the comment about the import will be lost.
; Some day we might try to gather these comments and stick them in the design.
; For now, well, we used to skip ALL comments between modules, so we're still
; working pretty hard to do something reasonably sensible.

