; ESIM Symbolic Hardware Simulator
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

(in-package "ACL2")
(include-book "std/util/top" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "../esim-paths")

; esim-snapshot.lisp -- this is a tool for building nice snapshots from ESIM
; runs of VL-generated modules.



; (MOD-VCD-SNAPSHOT MOD IN-BINDINGS OUT-BINDINGS INT-BINDINGS) is given:
;
;   - MOD, an esim module,
;
;   - IN-BINDINGS, an alist that should bind (GPL :I MOD) to values,
;
;   - OUT-BINDINGS, an alist that should bind (GPL :O MOD) to values,
;
;   - INT-BINDINGS, an alist that should bind all of the (MOD-INTERNAL-PATHS
;     MOD) to values.  Such an alist is typically obtained by running
;     ESIM-NEW-PROBE or similar.
;
; It builds a new (slow) alist that binds symbol-names that are suitable for
; VCD dumping to the values in IN-BINDINGS, OUT-BINDINGS, and INT-BINDINGS.
;
; If you want to directly use the resulting alist in a VCD dump, you'll have to
; make sure your values are valid for VCD-DUMP, e.g., they can be concrete
; FAIGS like (faig-f), S-expressions like *4vf*, or results from OT like the
; symbols T, NIL, X, or U.
;
; However, MOD-VCD-SNAPSHOT doesn't care what values are being used, so for
; instance you can use it to generate an AIG alist that you then restrict to
; generate the actual snapshots, etc.


(defsection symbol-path-p

; Recognize "proper" paths in the sense of mod-internal-paths, when we have
; module and wire names as symbols, as we normally expect

  (defund symbol-path-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (symbolp x)
      (and (symbolp (car x))
           (symbol-path-p (cdr x)))))

  (local (in-theory (enable symbol-path-p)))

  (defthm symbol-path-p-when-atom
    (implies (atom x)
             (equal (symbol-path-p x)
                    (symbolp x))))

  (defthm symbol-path-p-of-cons
    (equal (symbol-path-p (cons a x))
           (and (symbolp a)
                (symbol-path-p x)))))



(defsection symbol-path-list-p

  (std::deflist symbol-path-list-p (x)
    (symbol-path-p x)
    :guard t
    :elementp-of-nil t)

  (defthm symbol-path-list-p-when-symbol-listp
    (implies (symbol-listp x)
             (symbol-path-list-p x))
    :hints(("Goal" :induct (len x)))))



(defsection symbol-path-flatten

; Flatten out a symbol-path into a single symbol with dots separating its
; pieces.

  (defund symbol-path-flatten-aux (x)
    (declare (xargs :guard (symbol-path-p x)))
    (if (atom x)
        (list (symbol-name x))
      (list* (symbol-name (car x))
             "."
             (symbol-path-flatten-aux (cdr x)))))

  (defthm string-listp-of-symbol-path-flatten-aux
    (string-listp (symbol-path-flatten-aux x))
    :hints(("Goal" :in-theory (enable symbol-path-flatten-aux))))

  (defund symbol-path-flatten (x)
    (declare (xargs :guard (symbol-path-p x)))
    (intern$ (str::fast-string-append-lst (symbol-path-flatten-aux x)) "ACL2")))




(defsection good-pathpart-p

; We don't want to include VL-generated wires (e.g., the internals of adders,
; etc.)  in the VCD dump, so filter out these sorts of things as we're building
; the list of all "good" paths.

  (defund good-pathpart-p (x)
    (declare (xargs :guard t))
    (and (symbolp x)
         (let ((name (symbol-name x)))
           (not (or (str::strprefixp "vl_" name)
                    (str::strprefixp "temp_" name)
                    (str::substrp "-" name)
                    (str::substrp "~" name))))))

  (local (in-theory (enable good-pathpart-p)))

  (defthm symbolp-when-good-pathpart-p
    (implies (good-pathpart-p x)
             (symbolp x))
    :rule-classes :compound-recognizer))



(defsection remove-bad-path-parts

  (defund remove-bad-path-parts (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((good-pathpart-p (car x))
           (cons (car x) (remove-bad-path-parts (cdr x))))
          (t
           (remove-bad-path-parts (cdr x)))))

  (local (in-theory (enable remove-bad-path-parts)))

  (defthm symbol-listp-of-remove-bad-path-parts
    (symbol-listp (remove-bad-path-parts x))))



(defsection mod-vcd-paths

  (mutual-recursion

   (defun mod-vcd-paths (mod)
     (declare (xargs :guard t
                     :well-founded-relation nat-list-<
                     :measure (list (acl2-count mod) 1)))
     (append (remove-bad-path-parts (pat-flatten (gpl :i mod) nil))
             (remove-bad-path-parts (driven-signals mod))
             (occs-vcd-paths (gpl :occs mod))))

   (defun occ-vcd-paths (occ)
     (declare (xargs :guard t
                     :measure (list (acl2-count occ) 2)))
     (if (good-pathpart-p (gpl :u occ))
         ;; Don't use HONS because we're going to canonicalize these paths, so
         ;; we don't need them to be honsed.
         (extend-internal-paths (gpl :u occ)
                                (mod-vcd-paths (gpl :op occ)))
       nil))

   (defun occs-vcd-paths (occs)
     (declare (xargs :guard t
                     :measure (list (acl2-count occs) 0)))
     (if (atom occs)
         nil
       (append (occ-vcd-paths (car occs))
               (occs-vcd-paths (cdr occs))))))

  (flag::make-flag flag-mod-vcd-paths
                   mod-vcd-paths
                   :flag-mapping ((mod-vcd-paths mod)
                                  (occ-vcd-paths occ)
                                  (occs-vcd-paths occs)))

  (local (defthm symbol-path-list-p-of-extend-internal-paths
           (implies (and (symbolp a)
                         (symbol-path-list-p x))
                    (symbol-path-list-p (extend-internal-paths a x)))
           :hints(("Goal" :in-theory (enable extend-internal-paths)))))

  (defthm-flag-mod-vcd-paths
    (defthm symbol-path-list-p-of-mod-vcd-paths
      (symbol-path-list-p (mod-vcd-paths mod))
      :flag mod)

    (defthm symbol-path-list-p-of-occ-vcd-paths
      (symbol-path-list-p (occ-vcd-paths occ))
      :flag occ)

    (defthm symbol-path-list-p-of-occs-vcd-paths
      (symbol-path-list-p (occs-vcd-paths occs))
      :flag occs)

    :hints(("Goal"
            :expand ((mod-vcd-paths mod)
                     (occ-vcd-paths occ)
                     (occs-vcd-paths occs))))))



(defsection mod-vcd-alist

; (MOD-VCD-ALIST MOD) takes an ESIM module as input and produces an alist that
; should bind "real" wires (not generated by VL) to "canonical" paths that
; really exist in the set of MOD-INTERNAL-PATHS that are computed by the
; ESIM-NEW-PROBE stuff.

  (defund mod-vcd-alist-aux (paths mod)
    (declare (xargs :guard (and (symbol-path-list-p paths)
                                (good-esim-modulep mod))))
    (if (atom paths)
        nil
      (b* (((mv okp canonical-version)
            (fast-canonicalize-path (car paths) mod))
           ((unless okp)
            (er hard? 'mod-vcd-alist-aux "Failed to get canonical version of ~x0." (car paths))))
        (cons (cons (symbol-path-flatten (car paths)) canonical-version)
              (mod-vcd-alist-aux (cdr paths) mod)))))

  (defund mod-vcd-alist (mod)
    (declare (xargs :guard (good-esim-modulep mod)))
    (time$ (mod-vcd-alist-aux (mod-vcd-paths mod) mod)
           :msg "; mod-vcd-alist-aux took ~st sec, ~sa bytes~%"
           :mintime 1))

  (memoize 'mod-vcd-alist)

  (local (in-theory (enable mod-vcd-alist-aux mod-vcd-alist)))

  (defthm cons-listp-of-mod-vcd-alist-aux
    (cons-listp (mod-vcd-alist-aux paths mod)))

  (defthm cons-listp-of-mod-vcd-alist
    (cons-listp (mod-vcd-alist mod))))



(defsection mod-vcd-snapshot

  (defund mod-ins-fal (mod)
    (declare (xargs :guard t))
    (make-fast-alist (pairlis$ (pat-flatten (gpl :i mod) nil) nil)))

  (defund mod-outs-fal (mod)
    (declare (xargs :guard t))
    (make-fast-alist (pairlis$ (pat-flatten (gpl :o mod) nil) nil)))

  (memoize 'mod-ins-fal)
  (memoize 'mod-outs-fal)

  (defund mod-vcd-snapshot-aux
    ;; Basically like make-path-sexpr-alist-aux from cnq-clocks
    (vcd-alist  ; (mod-vcd-alist mod) for looking up canonical paths
     ins-fal    ; (mod-ins-fal mod) for looking up which signals are inputs
     outs-fal   ; (mod-outs-fal mod) for looking up which signals are outputs
     in-bindings ; User's bindings of inputs signals to values
     out-bindings ; User's bindings of output signals to values
     int-bindings ; User's bindings of internal (canonical) signals to values
     acc          ; Answer we are accumulating binding vcd-alist keys to values
     )
    (declare (xargs :guard (cons-listp vcd-alist)))
    (b* (((when (atom vcd-alist))
          acc)
         (name1 (caar vcd-alist))
         (path1 (cdar vcd-alist)) ;; we assume it's canonical
         (acc
          (cond ((and (atom path1) (hons-get path1 ins-fal))
                 (b* ((look (hons-get path1 in-bindings)))
                   (or look
                       (er hard? 'mod-vcd-snapshot-aux "failed to find a binding for input ~s0, path ~x1." name1 path1))
                   (cons (cons name1 (cdr look)) acc)))

                ((and (atom path1) (hons-get path1 outs-fal))
                 (b* ((look (hons-get path1 out-bindings)))
                   (or look
                       (er hard? 'mod-vcd-snapshot-aux "failed to find a binding for output ~s0, path ~s1" name1 path1))
                   (cons (cons name1 (cdr look)) acc)))

                (t
                 ;; Else, it should be an internal signal (atomic or a more elaborate path, either way.)
                 (b* ((look (hons-get path1 int-bindings)))
                   (or look
                       (er hard? 'mod-vcd-snapshot-aux "failed to find a binding for internal path ~s0, path ~s1." name1 path1))
                   (cons (cons name1 (cdr look)) acc))))))

      (mod-vcd-snapshot-aux (cdr vcd-alist) ins-fal outs-fal in-bindings out-bindings int-bindings acc)))

  (defund mod-vcd-snapshot (mod in-bindings out-bindings int-bindings)
    (declare (xargs :guard (good-esim-modulep mod)))
    (b* ((ins-fal   (make-fast-alist (mod-ins-fal mod)))
         (outs-fal  (make-fast-alist (mod-outs-fal mod)))
         (vcd-alist (mod-vcd-alist mod))
         (snap      (mod-vcd-snapshot-aux vcd-alist ins-fal outs-fal in-bindings out-bindings int-bindings nil)))

; Subtle: see vcd-dump-fn-real.  As a special optimization, vcd-dump can avoid
; sorting all the snapshots if they are in reverse sorted order.  So, we try to
; put them in this order before specializing them, so that specializing the
; snapshot will leave it in this order.

; For some snapshots in the XIB module, this improved the "vcd snapshot
; preparation" step from 17 seconds to 8 seconds, which seems pretty good.

      (reverse (set::mergesort snap)))))
