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
(include-book "../mlib/wirealist")
(include-book "../mlib/allexprs")
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))



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
    (str::cat (car x)
              (if (atom (cdr x))
                  ""
                (str::cat
                 (if (consp (cddr x)) ", " " and ")
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

         ((mv collect-warnings connected-wires)
          (cwtime (vl-exprlist-allwires all-exprs walist)
                  :mintime 1/2))

         (- (fast-alist-free walist))

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
                   :msg (str::cat "In ~m0, among the disconnected wires we found, these ~
                         are somewhat interesting because only a portion of ~
                         the wire is disconnected: "
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


(defsection vl-modulelist-find-disconnected

  (defprojection vl-modulelist-find-disconnected (x)
    (vl-module-find-disconnected x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-find-disconnected)))

  (defthm vl-modulelist->names-of-vl-modulelist-find-disconnected
    (equal (vl-modulelist->names (vl-modulelist-find-disconnected x))
           (vl-modulelist->names x))))