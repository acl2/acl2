; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "../toe/toe-wirealist")
(include-book "../toe/toe-verilogify")
(include-book "../mlib/allexprs")
(include-book "../mlib/fmt")
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))


(defsection vl-expr-allwires
  :parents (vl-wirealist-p)
  :short "Collect an @(see vl-emodwirelist-p) of every wire that is mentioned
in an expression."

  :long "<p><b>Signature:</b> @(call vl-expr-allwires) returns @('(mv warnings
wires)').</p>

<p>This is similar to @(see vl-msb-expr-bitlist), but can be applied to more
kinds of expressions.  For instance, given the expression @('a + b'), this
function will collect the wires of @('a') and the wires of @('b'), whereas
@('vl-msb-expr-bitlist') will just fail since this isn't a sliceable
expression.</p>

<p>This function tries to be very permissive and does not necessarily do the
same level of error checking as @(see vl-msb-expr-bitlist).  Also, the wires
are returned in a nonsensical order.</p>"

  (mutual-recursion

   (defund vl-expr-allwires (x walist)
     "Returns (MV WARNINGS WIRES)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-wirealist-p walist))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (b* ((guts (vl-atom->guts x))

                ((when (vl-fast-id-p guts))

; BOZO?  Not repeating the sign bit if there's an implicit signed extension.
; Not necessarily something we need to do.  We might want to do the sign
; extension if we ever care about the duplicity of the resulting wires, but for
; now we don't bother.

                 (b* ((name  (vl-id->name guts))
                      (entry (hons-get name walist))
                      (wires (mbe :logic (list-fix (cdr entry))
                                  :exec (cdr entry)))
                      ((when entry)
                       (mv nil wires))
                      (w (make-vl-warning
                          :type :vl-collect-wires-fail
                          :msg "Failed to collect wires for ~w0; no such entry ~
                                in the wire-alist."
                          :args (list name)
                          :fn 'vl-expr-allwires)))
                   (mv (list w) nil)))

                ((when (or (vl-fast-constint-p guts)
                           (vl-fast-weirdint-p guts)
                           (vl-fast-hidpiece-p guts)))
                 (mv nil nil))

                (w (make-vl-warning
                    :type :vl-collect-wires-fail
                    :msg "Failed to collect wires for ~a0; expression type is ~
                          not supported."
                    :args (list x)
                    :fn 'vl-expr-allwires)))
             (mv (list w) nil)))

          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((when (eq op :vl-bitselect))
           (b* ((from (first args))
                (index (second args))
                ((unless (vl-idexpr-p from))
                 (b* ((w (make-vl-warning
                          :type :vl-collect-wires-fail
                          :msg "Failed to collect wires for ~a0; expected to ~
                                select only from identifiers."
                          :args (list x)
                          :fn 'vl-expr-allwires)))
                   (mv (list w) nil)))

                (name  (vl-idexpr->name from))
                (entry (hons-get name walist))
                (wires (mbe :logic (list-fix (cdr entry))
                            :exec (cdr entry)))

                ((unless entry)
                 (b* ((w (make-vl-warning
                          :type :vl-collect-wires-fail
                          :msg "Failed to collect wires for ~a0; no entry for ~
                               ~w1 in the wire alist."
                          :args (list x name)
                          :fn 'vl-expr-allwires)))
                   (mv (list w) nil)))

                ((unless (and (vl-expr-resolved-p index)
                              (natp (vl-resolved->val index))))
                 (b* ((w (make-vl-warning
                          :type :vl-collect-wires-approx
                          :msg "Approximating the wires for ~a0 with ~s1."
                          :args (list x (vl-verilogify-emodwirelist wires))
                          :fn 'vl-expr-allwires)))
                   (mv (list w) wires)))

                (option1 (vl-plain-wire-name name))
                ((when (member option1 wires))
                 (mv nil (list option1)))

                (option2 (make-vl-emodwire :basename name
                                           :index (vl-resolved->val index)))
                ((when (member option2 wires))
                 (mv nil (list option2)))

                (w (make-vl-warning
                    :type :vl-collect-wires-approx
                    :msg "Failed to collect wires for ~a0; index out of range?"
                    :args (list x)
                    :fn 'vl-expr-allwires)))
             (mv (list w) nil)))


          ((when (eq op :vl-partselect-colon))
           (b* ((from  (first args))
                (left  (second args))
                (right (third args))

                ((unless (vl-idexpr-p from))
                 (b* ((w (make-vl-warning
                          :type :vl-collect-wires-fail
                          :msg "Failed to collect wires for ~a0; expected to ~
                                select only from identifiers."
                          :args (list x)
                          :fn 'vl-expr-allwires)))
                   (mv (list w) nil)))

                (name  (vl-idexpr->name from))
                (entry (hons-get name walist))
                (wires (mbe :logic (list-fix (cdr entry))
                            :exec (cdr entry)))

                ((unless entry)
                 (b* ((w (make-vl-warning
                          :type :vl-collect-wires-fail
                          :msg "Failed to collect wires for ~a0; no entry for ~
                                ~w1 in the wire alist."
                          :args (list x name)
                          :fn 'vl-expr-allwires)))
                   (mv (list w) nil)))

                ((unless (and (vl-expr-resolved-p left)
                              (vl-expr-resolved-p right)))
                 (b* ((w (make-vl-warning
                          :type :vl-collect-wires-approx
                          :msg "Approximating the wires for ~a0 with ~s1."
                          :args (list x (vl-verilogify-emodwirelist wires))
                          :fn 'vl-expr-allwires)))
                   (mv (list w) wires)))

                (left  (vl-resolved->val left))
                (right (vl-resolved->val right))

; Special case for foo[0:0] when foo is a non-ranged wire.  BOZO this is
; probably wrong, as in the normal partselect function.

                ((when (and (= left 0)
                            (= right 0)
                            (equal wires (list (vl-plain-wire-name name)))))
                 (mv nil wires))

                (name[left]  (make-vl-emodwire :basename name :index left))
                (name[right] (make-vl-emodwire :basename name :index right))

                ((when (and (member name[left] wires)
                            (member name[right] wires)))
                 (mv nil (vl-emodwires-from-msb-to-lsb name left right)))

                (w (make-vl-warning
                    :type :vl-collect-wires-fail
                    :msg "Failed to collect wires for ~a0; index out of range?"
                    :args (list x)
                    :fn 'vl-expr-allwires)))
             (mv (list w) nil))))

       (vl-exprlist-allwires args walist)))

   (defund vl-exprlist-allwires (x walist)
     "Returns (MV WARNINGS WIRES)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-wirealist-p walist))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv nil nil))
          ((mv warnings1 car-wires)
           (vl-expr-allwires (car x) walist))
          ((mv warnings2 cdr-wires)
           (vl-exprlist-allwires (cdr x) walist)))
       (mv (append warnings1 warnings2)
           (append car-wires cdr-wires)))))

  (local (in-theory (enable vl-exprlist-allwires)))

  (flag::make-flag flag-vl-expr-allwires
                   vl-expr-allwires
                   :flag-mapping ((vl-expr-allwires . expr)
                                  (vl-exprlist-allwires . list)))

  (defthm-flag-vl-expr-allwires
    (defthm true-listp-of-vl-expr-allwires-0
      (true-listp (mv-nth 0 (vl-expr-allwires x walist)))
      :rule-classes :type-prescription
      :flag expr)
    (defthm true-listp-of-vl-exprlist-allwires-0
      (true-listp (mv-nth 0 (vl-exprlist-allwires x walist)))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal" :expand ((vl-expr-allwires x walist)
                            (vl-exprlist-allwires x walist)))))

  (defthm-flag-vl-expr-allwires
    (defthm true-listp-of-vl-expr-allwires-1
      (true-listp (mv-nth 1 (vl-expr-allwires x walist)))
      :rule-classes :type-prescription
      :flag expr)
    (defthm true-listp-of-vl-exprlist-allwires-1
      (true-listp (mv-nth 1 (vl-exprlist-allwires x walist)))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal" :expand ((vl-expr-allwires x walist)
                            (vl-exprlist-allwires x walist)))))

  (defthm-flag-vl-expr-allwires
    (defthm vl-warninglist-p-of-vl-expr-allwires
      (vl-warninglist-p (mv-nth 0 (vl-expr-allwires x walist)))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-allwires
      (vl-warninglist-p (mv-nth 0 (vl-exprlist-allwires x walist)))
      :flag list)
    :hints(("Goal" :expand ((vl-expr-allwires x walist)
                            (vl-exprlist-allwires x walist)))))

  (defthm-flag-vl-expr-allwires
    (defthm vl-emodwirelist-p-of-vl-expr-allwires
      (implies (force (vl-wirealist-p walist))
               (vl-emodwirelist-p (mv-nth 1 (vl-expr-allwires x walist))))
      :flag expr)
    (defthm vl-emodwirelist-p-of-vl-exprlist-allwires
      (implies (force (vl-wirealist-p walist))
               (vl-emodwirelist-p (mv-nth 1 (vl-exprlist-allwires x walist))))
      :flag list)
    :hints(("Goal" :expand ((vl-expr-allwires x walist)
                            (vl-exprlist-allwires x walist)))))

  (verify-guards vl-expr-allwires))


(defsection vl-collect-flattened-hids

  (defund vl-collect-flattened-hids (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (if (atom x)
        nil
      (let ((atts (vl-netdecl->atts (car x))))
        (if (or (assoc-equal "VL_HID_LOCAL_P" atts)
                (assoc-equal "VL_HID_GLOBAL_P" atts))
            (cons (car x)
                  (vl-collect-flattened-hids (cdr x)))
          (vl-collect-flattened-hids (cdr x))))))

  (local (in-theory (enable vl-collect-flattened-hids)))

  (defthm vl-netdecllist-p-of-vl-collect-flattened-hids
    (implies (force (vl-netdecllist-p x))
             (vl-netdecllist-p (vl-collect-flattened-hids x)))))


(defsection vl-delete-emodwires-with-basenames

  (defund vl-delete-emodwires-with-basenames (basenames fal x)
    (declare (xargs :guard (and (string-listp basenames)
                                (equal fal (make-lookup-alist basenames))
                                (vl-emodwirelist-p x))))
    (cond ((atom x)
           nil)
          ((fast-memberp (vl-emodwire->basename (car x)) basenames fal)
           (vl-delete-emodwires-with-basenames basenames fal (cdr x)))
          (t
           (cons (car x)
                 (vl-delete-emodwires-with-basenames basenames fal (cdr x))))))

  (local (in-theory (enable vl-delete-emodwires-with-basenames)))

  (defthm vl-emodwirelist-p-of-vl-delete-emodwires-with-basenames
    (implies (force (vl-emodwirelist-p x))
             (vl-emodwirelist-p (vl-delete-emodwires-with-basenames basenames fal x)))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-gather-interestingly-disconnected

; This is kind of goofy.  The goal is to find wires where only part of the wire
; is disconnected.

  (defund vl-gather-interestingly-disconnected (walist disconnected)
    (declare (xargs :guard (and (vl-wirealist-p walist)
                                (vl-emodwirelist-p disconnected)
                                (setp disconnected))))
    (b* (((when (atom walist))
          nil)

         (wires1 (mergesort (cdar walist)))

         ((when (not (sets::intersectp wires1 disconnected)))
          ;; None of these wires are disconnected; not interesting.
          (vl-gather-interestingly-disconnected (cdr walist) disconnected))

         ((when (subset wires1 disconnected))
          ;; All of these wires are disconnected; not interesting.
          (vl-gather-interestingly-disconnected (cdr walist) disconnected))

         ;; Otherwise, interesting because only some bits are disconnected.
         (wires1-dis  (intersect wires1 disconnected))
         (summary     (vl-verilogify-emodwirelist wires1-dis))

         (max  (nfix (vl-emodwire->index (car (cdar walist)))))
         (min  (nfix (vl-emodwire->index (car (last (cdar walist))))))

         (msg (with-local-ps
               (vl-cw "bits ~&0 from [~x1:~x2]" summary max min))))
      (cons msg
            (vl-gather-interestingly-disconnected (cdr walist) disconnected))))

  (local (in-theory (enable vl-gather-interestingly-disconnected)))

  (defthm string-listp-of-vl-gather-interestingly-disconnected
    (implies (and (force (vl-wirealist-p walist))
                  (force (vl-emodwirelist-p disconnected))
                  (force (setp disconnected)))
             (string-listp
              (vl-gather-interestingly-disconnected walist disconnected)))))

(defund strcat-like-tilde-& (x)
  (declare (xargs :guard (string-listp x)))
  (if (atom x)
      ""
    (cat (car x)
         (if (atom (cdr x))
             ""
           (cat (if (consp (cddr x)) ", " " and ")
                (strcat-like-tilde-& (cdr x)))))))

(assert! (equal (strcat-like-tilde-& '("A")) "A"))
(assert! (equal (strcat-like-tilde-& '("A" "B")) "A and B"))
(assert! (equal (strcat-like-tilde-& '("A" "B" "C")) "A, B and C"))
(assert! (equal (strcat-like-tilde-& '("A" "B" "C" "D")) "A, B, C and D"))



(defsection vl-module-find-disconnected

  (local (defthm vl-emodwirelist-p-of-append-domains
           (implies (vl-wirealist-p x)
                    (vl-emodwirelist-p (append-domains x)))))

  (defund vl-module-find-disconnected (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)

         (all-exprs
          (cwtime (vl-module-allexprs-exec x nil)
                  :mintime 1/2))

         ((mv ?successp walist-warnings walist)
          (cwtime (vl-module-wirealist x nil)
                  :mintime 1/2))

         ((with-fast walist))

         ((mv collect-warnings connected-wires)
          (cwtime (vl-exprlist-allwires all-exprs walist)
                  :mintime 1/2))

         (all-wires          (mergesort (append-domains walist)))
         (connected-wires    (mergesort connected-wires))
         (disconnected-wires (difference all-wires connected-wires))

         ;; Originally we reported the disconnected-wires, but that was stupid
         ;; because we don't care if this particular module uses all of the
         ;; bits of a HID it refers to.  So, suppress any disconnected hids.
         (hid-netdecls       (vl-collect-flattened-hids x.netdecls))
         (hid-names          (vl-netdecllist->names hid-netdecls))
         (hid-names-fal      (make-lookup-alist hid-names))
         (disconnected-wires (redundant-mergesort
                              (vl-delete-emodwires-with-basenames hid-names hid-names-fal
                                                                  disconnected-wires)))
         (-                  (fast-alist-free hid-names-fal))

         (interesting        (vl-gather-interestingly-disconnected walist disconnected-wires))

         (human-readable     (vl-verilogify-emodwirelist disconnected-wires))
         (warnings           (append-without-guard collect-warnings
                                                   walist-warnings
                                                   x.warnings))
         (warnings
          ;; Including the module name is important since this happens after
          ;; unparameterization -- for unparameterized modules, the user may
          ;; need to see the foo$size=5 part for the message to make sense.
          (cond ((not disconnected-wires)
                 warnings)
                ((or collect-warnings walist-warnings)
                 (cons (make-vl-warning
                        :type :vl-warn-disconnected
                        :msg "In ~m0, it appears that the following ~s1 not connected ~
                              to anything, but note that there were errors ~
                              ~s2, so these results may not be accurate: ~&3."
                        :args (list x.name
                                    (if (vl-plural-p disconnected-wires)
                                        "wires are"
                                      "wire is")
                                    (cond ((and collect-warnings walist-warnings)
                                           "generating and collecting wires")
                                          (collect-warnings
                                           "collecting wires")
                                          (t
                                           "generating wires"))
                                    human-readable)
                        :fatalp nil
                        :fn 'vl-module-find-disconnected)
                       warnings))
                (t
                 (cons (make-vl-warning
                        :type :vl-warn-disconnected
                        :msg "In ~m0, the following ~s1 not connected to anything: ~&2."
                        :args (list x.name
                                    (if (vl-plural-p disconnected-wires)
                                        "wires are"
                                      "wire is")
                                    human-readable)
                        :fatalp nil
                        :fn 'vl-module-find-disconnected)
                       warnings))))

         (warnings
          (if (not interesting)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-disconnected-interesting
                   :msg (cat "In ~m0, among the disconnected wires we found, ~
                              these are somewhat interesting because only a ~
                              portion of the wire is disconnected: "
                             (strcat-like-tilde-& interesting))
                   :args (list x.name)
                   :fatalp nil
                   :fn 'vl-module-find-disconnected)
                  warnings))))
      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-find-disconnected)))

  (defthm vl-module-p-of-vl-module-find-disconnected
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-find-disconnected x))))

  (defthm vl-module->name-of-vl-module-find-disconnected
    (equal (vl-module->name (vl-module-find-disconnected x))
           (vl-module->name x))))


(defsection vl-modulelist-find-disconnected-aux

  (defprojection vl-modulelist-find-disconnected-aux (x)
    (vl-module-find-disconnected x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-find-disconnected-aux)))

  (defthm vl-modulelist->names-of-vl-modulelist-find-disconnected-aux
    (equal (vl-modulelist->names (vl-modulelist-find-disconnected-aux x))
           (vl-modulelist->names x))))

(defun vl-modulelist-find-disconnected (x)
  (declare (xargs :guard (vl-modulelist-p x)))
  (b* ((ans (vl-modulelist-find-disconnected-aux x)))
    (clear-memoize-table 'vl-module-wirealist)
    ans))