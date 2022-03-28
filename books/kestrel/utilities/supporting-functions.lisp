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

(local (in-theory (disable all-fnnames1)))

(defun all-supporting-fns-aux (count
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
                              (plist-worldp wrld))))
  (if (zp count)
      (prog2$ (er hard? 'all-supporting-fns "Count reached.")
              (mv defined-fns-acc undefined-fns-acc stopper-fns-acc))
    (if (endp worklist)
        (mv defined-fns-acc undefined-fns-acc stopper-fns-acc)
      (let ((fn (first worklist)))
        (if (member-eq fn donelist)
            (all-supporting-fns-aux (+ -1 count)
                                    (rest worklist)
                                    donelist
                                    stopper-fns
                                    defined-fns-acc
                                    undefined-fns-acc
                                    stopper-fns-acc
                                    wrld)
          (if (member-eq fn stopper-fns)
              (all-supporting-fns-aux (+ -1 count)
                                      (rest worklist)
                                      (cons fn donelist)
                                      stopper-fns
                                      defined-fns-acc
                                      undefined-fns-acc
                                      (cons fn stopper-fns-acc) ; not already present since not in donelist
                                      wrld)
            (if (not (fn-definedp fn wrld))
                (all-supporting-fns-aux (+ -1 count)
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
                    (prog2$ (er hard? 'all-supporting-fns "Bad list of call fns: ~x0." called-fns)
                            (mv defined-fns-acc undefined-fns-acc stopper-fns-acc))
                  (all-supporting-fns-aux (+ -1 count)
                                          (append called-fns ;(set-difference-eq called-fns donelist)
                                                  (rest worklist))
                                          (cons fn donelist)
                                          stopper-fns
                                          (cons fn defined-fns-acc) ; not already present since not in donelist
                                          undefined-fns-acc
                                          stopper-fns-acc
                                          wrld))))))))))

;; Considers the supplied FNS and the functions they call, etc., back to functions
;; that are STOPPER-FNS or are undefined.  Classifies the discovered functions.
;; Returns (mv defined-fns undefined-fns stopper-fns), where the results include just those functions reachable from the FNS without looking inside any STOPPER-FNS.
;; Example: (all-supporting-fns '(all-supporting-fns) nil (w state))
(defun all-supporting-fns (fns stopper-fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp stopper-fns)
                              (plist-worldp wrld))))
  (all-supporting-fns-aux 1000000000 fns nil stopper-fns nil nil nil wrld))
