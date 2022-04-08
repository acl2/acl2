; A utility to get functions that are called (transitively) by a given set of functions
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "world")
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (in-theory (disable mv-nth)))

(defund fns-supporting-fns-aux (count
                                worklist
                                donelist ; includes all the fns in the 3 accumulators (it's their union?)
                                stopper-fns
                                defined-fns-acc
                                undefined-fns-acc
                                stopper-fns-acc
                                wrld)
  (declare (xargs :guard (and (natp count)
                              (symbol-listp worklist)
                              (symbol-listp donelist)
                              (symbol-listp stopper-fns)
                              (symbol-listp defined-fns-acc)
                              (symbol-listp undefined-fns-acc)
                              (symbol-listp stopper-fns-acc)
                              (plist-worldp wrld))))
  (if (zp count)
      (prog2$ (er hard? 'fns-supporting-fns "Count reached.")
              (mv defined-fns-acc undefined-fns-acc stopper-fns-acc))
    (if (endp worklist)
        (mv defined-fns-acc undefined-fns-acc stopper-fns-acc)
      (let ((fn (first worklist)))
        (if (member-eq fn donelist)
            (fns-supporting-fns-aux (+ -1 count)
                                    (rest worklist)
                                    donelist
                                    stopper-fns
                                    defined-fns-acc
                                    undefined-fns-acc
                                    stopper-fns-acc
                                    wrld)
          (if (member-eq fn stopper-fns)
              (fns-supporting-fns-aux (+ -1 count)
                                      (rest worklist)
                                      (cons fn donelist)
                                      stopper-fns
                                      defined-fns-acc
                                      undefined-fns-acc
                                      (cons fn stopper-fns-acc) ; not already present since not in donelist
                                      wrld)
            (if (not (fn-definedp fn wrld))
                (fns-supporting-fns-aux (+ -1 count)
                                        (rest worklist)
                                        (cons fn donelist)
                                        stopper-fns
                                        defined-fns-acc
                                        (cons fn undefined-fns-acc) ; not already present since not in donelist
                                        stopper-fns-acc
                                        wrld)
              ;; fn is defined:
              (let* ((body (fn-body fn t wrld))
                     (called-fns (all-fnnames body)))
                (if (not (symbol-listp called-fns)) ; for guard proof
                    (prog2$ (er hard? 'fns-supporting-fns "Bad list of called fns: ~x0." called-fns)
                            (mv defined-fns-acc undefined-fns-acc stopper-fns-acc))
                  (fns-supporting-fns-aux (+ -1 count)
                                          (append called-fns ;(set-difference-eq called-fns donelist)
                                                  (rest worklist))
                                          (cons fn donelist)
                                          stopper-fns
                                          (cons fn defined-fns-acc) ; not already present since not in donelist
                                          undefined-fns-acc
                                          stopper-fns-acc
                                          wrld))))))))))

(defthm fns-supporting-fns-aux-type
  (implies (and (natp count)
                (symbol-listp worklist)
                (symbol-listp donelist)
                (symbol-listp stopper-fns)
                (plist-worldp wrld)
                (symbol-listp defined-fns-acc)
                (symbol-listp undefined-fns-acc)
                (symbol-listp stopper-fns-acc))
           (and (symbol-listp (mv-nth 0 (fns-supporting-fns-aux count worklist donelist stopper-fns defined-fns-acc undefined-fns-acc stopper-fns-acc wrld)))
                (symbol-listp (mv-nth 1 (fns-supporting-fns-aux count worklist donelist stopper-fns defined-fns-acc undefined-fns-acc stopper-fns-acc wrld)))
                (symbol-listp (mv-nth 2 (fns-supporting-fns-aux count worklist donelist stopper-fns defined-fns-acc undefined-fns-acc stopper-fns-acc wrld)))))
  :hints (("Goal" :in-theory (enable fns-supporting-fns-aux))))

;; Considers the supplied FNS and the functions they call, etc., back to functions
;; that are STOPPER-FNS or are undefined.  Classifies the discovered functions.
;; Returns (mv defined-fns undefined-fns stopper-fns), where the results include just those functions reachable from the FNS without looking inside any STOPPER-FNS.
;; Example: (fns-supporting-fns '(fns-supporting-fns) nil (w state))
(defund fns-supporting-fns (fns stopper-fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp stopper-fns)
                              (plist-worldp wrld))))
  (fns-supporting-fns-aux 1000000000 fns nil stopper-fns nil nil nil wrld))

(defthm fns-supporting-fns-type
  (implies (and (symbol-listp fns)
                (symbol-listp stopper-fns)
                (plist-worldp wrld))
           (and (symbol-listp (mv-nth 0 (fns-supporting-fns fns stopper-fns wrld)))
                (symbol-listp (mv-nth 1 (fns-supporting-fns fns stopper-fns wrld)))
                (symbol-listp (mv-nth 2 (fns-supporting-fns fns stopper-fns wrld)))))
  :hints (("Goal" :in-theory (enable fns-supporting-fns))))

;; Returns (mv defined-fns undefined-fns stopper-fns), where the results include just those functions reachable from the FNS without looking inside any STOPPER-FNS.
;; See fns-supporting-fns.
(defund fns-supporting-term (term stopper-fns wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp stopper-fns)
                              (plist-worldp wrld))))
  (let ((fns (all-fnnames term)))
    (if (not (symbol-listp fns))
        (prog2$ (er hard? 'fns-supporting-term "Bad list of called fns, ~x0, in term ~x1 ." fns term)
                (mv nil nil nil))
      (fns-supporting-fns fns stopper-fns wrld))))

(defthm fns-supporting-term-type
  (implies (and (pseudo-termp term)
                (symbol-listp stopper-fns)
                (plist-worldp wrld))
           (and (symbol-listp (mv-nth 0 (fns-supporting-term term stopper-fns wrld)))
                (symbol-listp (mv-nth 1 (fns-supporting-term term stopper-fns wrld)))
                (symbol-listp (mv-nth 2 (fns-supporting-term term stopper-fns wrld)))))
  :hints (("Goal" :in-theory (enable fns-supporting-term))))
