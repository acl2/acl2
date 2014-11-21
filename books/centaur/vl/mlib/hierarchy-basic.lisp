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
(include-book "blocks")
(include-book "find")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))


(def-genblob-transform vl-genblob->flatten-modinsts ((acc vl-modinstlist-p))
  :no-new-x t
  :returns ((acc vl-modinstlist-p))
  :apply-to-generates vl-generates->flatten-modinsts
  :prepwork ((local (in-theory (disable ;; vl-genelement-p-by-tag-when-vl-scopeitem-p
                                        vl-modinstlist-p-when-not-consp
                                        (tau-system)
                                        append
                                        vl-modinstlist-p-when-subsetp-equal))))
  (vl-generates->flatten-modinsts (vl-genblob->generates x)
                                  (append-without-guard
                                   (vl-genblob->modinsts x)
                                   (vl-modinstlist-fix acc))))

(define vl-module->flatten-modinsts ((x vl-module-p))
  :parents (vl-modulelist-everinstanced)
  :short "Gather modinsts from the module, including its generate blocks."
  :returns (modinsts vl-modinstlist-p)
  (b* ((genblob (vl-module->genblob x)))
    (vl-genblob->flatten-modinsts genblob nil)))

(defprojection vl-interfaceportlist->ifnames ((x vl-interfaceportlist-p))
  :returns (names string-listp)
  (vl-interfaceport->ifname x))



(define vl-modulelist-everinstanced-nrev ((x vl-modulelist-p)
                                          (nrev))
  :parents (vl-modulelist-everinstanced)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (modinsts1 (vl-module->flatten-modinsts (car x)))
       (ifports1  (vl-module->ifports (car x)))
       (nrev      (vl-modinstlist->modnames-nrev modinsts1 nrev))
       (nrev      (vl-interfaceportlist->ifnames-nrev ifports1 nrev)))
    (vl-modulelist-everinstanced-nrev (cdr x) nrev)))

(define vl-modulelist-everinstanced ((x vl-modulelist-p))
  :parents (hierarchy)
  :short "Gather the names of every module and interface ever instanced in a
  module list or used in an interface port."

  :long "<p>The returned list typically will contain a lot of duplicates.  This
is fairly expensive, requiring a cons for every single module instance.  We
optimize it to avoid the construction of intermediate lists and to use @(see
nrev).</p>"

  :returns (names string-listp)
  :enabled t
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (modinsts1 (vl-module->flatten-modinsts (car x)))
            (ifports1  (vl-module->ifports (car x))))
         (append (vl-modinstlist->modnames modinsts1)
                 (vl-interfaceportlist->ifnames ifports1)
                 (vl-modulelist-everinstanced (cdr x))))
       :exec
       (with-local-nrev (vl-modulelist-everinstanced-nrev x nrev)))
  :verify-guards nil
  ///
  (defthm vl-modulelist-everinstanced-nrev-removal
    (equal (vl-modulelist-everinstanced-nrev x nrev)
           (append nrev (vl-modulelist-everinstanced x)))
    :hints(("Goal" :in-theory (enable vl-modulelist-everinstanced-nrev))))

  (verify-guards vl-modulelist-everinstanced))


;; (define vl-modulelist-missing
;;   :parents (hierarchy missing)
;;   :short "@(call vl-modulelist-missing) gathers the names of any modules which
;; are instantiated in the module list @('x') but are not defined in
;; @('x'), and returns them as an ordered set."

;;   ((x vl-modulelist-p))
;;   :returns (names string-listp)

;;   (mbe :logic
;;        (let ((mentioned (mergesort (vl-modulelist-everinstanced x)))
;;              (defined   (mergesort (vl-modulelist->names x))))
;;          (difference mentioned defined))
;;        :exec

;; ; Some minor optimizations.

;; ; Historically, since we're sorting the instnames anyway, we don't need to pay
;; ; the price of reversing them and can just use the exec function directly.  Now
;; ; that we're using nrev I don't bother to do this.

;;        (let* ((mentioned (mergesort (vl-modulelist-everinstanced x)))

;; ; Also, since we often work with sets of modules, we can try to avoid
;; ; mergesorting the names when they are known to be a set.  At best, this
;; ; allows us to avoid sorting the module names, and hence saves a bunch of
;; ; consing.
;; ;
;; ; Of course, when this fails we incur the additional price of a setp check,
;; ; which in principle is as bad as O(n) comparisons.  On the other hand, setp
;; ; can fail early.  It seems likely that an unordered list will have elements
;; ; near its head that are out of order.  So, even when the setp check fails, it
;; ; may often be that it fails pretty quickly.

;;               (names     (vl-modulelist->names x))
;;               (defined   (redundant-mergesort names)))
;;          (difference mentioned defined)))
;;   ///
;;   (defthm true-listp-of-vl-modulelist-missing
;;     (true-listp (vl-modulelist-missing x))
;;     :rule-classes :type-prescription)

;;   (defthm setp-of-vl-modulelist-missing
;;     (setp (vl-modulelist-missing x))))


(define vl-modulelist-toplevel
  :parents (hierarchy)
  :short "@(call vl-modulelist-toplevel) gathers the names of any modules that
are defined in the module list @('x') but are never instantiated in @('x'), and
returns them as an ordered set."

  ((x vl-modulelist-p))
  :returns (names string-listp)

  (mbe :logic
       (let ((mentioned (mergesort (vl-modulelist-everinstanced x)))
             (defined   (mergesort (vl-modulelist->names x))))
         (difference defined mentioned))
       :exec
       ;; Optimizations as in vl-modulelist-missing
       (let* ((mentioned (mergesort (vl-modulelist-everinstanced x)))
              (names     (vl-modulelist->names x))
              (defined   (if (setp names) names (mergesort names))))
         (difference defined mentioned)))
  ///
  (defthm true-listp-of-vl-modulelist-toplevel
    (true-listp (vl-modulelist-toplevel x))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-modulelist-toplevel
    (setp (vl-modulelist-toplevel x)))

  ;; (defthm vl-has-modules-of-vl-modulelist-toplevel
  ;;   (implies (vl-modulelist-complete-p mods mods)
  ;;            (subsetp-equal (vl-modulelist-toplevel mods)
  ;;                           (vl-modulelist->names mods)))
  ;;   :hints((set-reasoning)))
  )



;; (define vl-modulelist-highlevel
;;   :parents (hierarchy)
;;   :short "@(call vl-modulelist-highlevel) gathers the names of any \"high
;; level\" modules and return them as an ordered set."

;;   ((x vl-modulelist-p)
;;    (n natp "How many levels from the top to consider."))

;;   :returns (names string-listp)

;;   :long "<p>We say a module is <b>top level</b> (@(see vl-modulelist-toplevel))
;; when it is never instantiated by another module.  Similarly, we say that
;; modules are <b>high level</b> when they are \"near the top level\".</p>

;; <p>@(call vl-modulelist-highlevel) gathers the names of all modules which are
;; within @('n') levels of the top.  When @('n') is relatively small,
;; these modules are possibly the \"big units\" in the chip.</p>

;; <p>Historic note.  This function was once used in the \"unreasonable modules
;; report.\" It may not be in use any more.</p>"

;;   :verify-guards nil
;;   (b* (((when (zp n))
;;         nil)
;;        (top (vl-modulelist-toplevel x)))
;;     (union top
;;            (vl-modulelist-highlevel (vl-delete-modules top x)
;;                                     (- n 1))))
;;   ///
;;   (defthm true-listp-of-vl-modulelist-highlevel
;;     (true-listp (vl-modulelist-highlevel x n))
;;     :rule-classes :type-prescription
;;     :hints(("Goal" :in-theory (disable (force)))))

;;   (defthm setp-of-vl-modulelist-highlevel
;;     (setp (vl-modulelist-highlevel x n)))

;;   (verify-guards vl-modulelist-highlevel))
