; Checking the result of relieving an axe-bind-free hyp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-dargp-less-than")

;; Check whether ALIST is an alist that binds exactly the symbols in
;; EXPECTED-SYMBOLS, in that order, to either quoted constants or nodenums less
;; than DAG-LEN.
(defund axe-bind-free-result-okayp (alist expected-symbols dag-len)
  (declare (xargs :guard (and (natp dag-len)
                              (symbol-listp expected-symbols))))
  (if (atom alist)
      (and (null alist)
           (null expected-symbols))
    (let ((entry (first alist)))
      (and (consp entry)
           (consp expected-symbols)
           (eq (car entry) (first expected-symbols))
           (let ((val (cdr entry)))
             (and (or (myquotep val)
                      (and (natp val)
                           (< val dag-len)))
                  (axe-bind-free-result-okayp (rest alist) (rest expected-symbols) dag-len)))))))

(defthmd axe-bind-free-result-okayp-rewrite
  (equal (axe-bind-free-result-okayp alist expected-symbols dag-len)
         (and (alistp alist)
              (equal expected-symbols (strip-cars alist))
              (all-dargp-less-than (strip-cdrs alist) dag-len)))
  :hints (("Goal" :in-theory (e/d (strip-cdrs default-cdr default-car axe-bind-free-result-okayp dargp-less-than)
                                  (myquotep natp)))))

(defthm axe-bind-free-result-okayp-forward-to-alistp
  (implies (axe-bind-free-result-okayp alist expected-symbols dag-len)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-result-okayp))))
