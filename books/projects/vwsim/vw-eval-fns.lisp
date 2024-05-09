
; vw-eval-fns.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")
(include-book "names-and-indices")

(defconst *fns*
  ;; Function symbols for our VW-EVAL evaluator
  '(;; special functions
    quote
    back
    $time$<
    $time$-$hn$<
    $time$<mod-
    $time$-$hn$<mod-
    if
    ;; arithmetic/boolean functions
    f-not
    f0-
    f-abs
    f-1/x
    f-sqrt
    f-sin
    f-cos
    f-tan
    f-tanh
    f-exp
    f+
    f-
    f*
    f/
    f<
    f=
    f-mod
    ))

(defconst *quote-index*
  (pos 'quote *fns*))

(defconst *back-index*
  (pos 'back *fns*))

(defconst *$time$<-index*
  (pos '$time$< *fns*))

(defconst *$time$-$hn$<-index*
  (pos '$time$-$hn$< *fns*))

(defconst *$time$<mod--index*
  (pos '$time$<mod- *fns*))

(defconst *$time$-$hn$<mod--index*
  (pos '$time$-$hn$<mod- *fns*))

(defconst *if-index*
  (pos 'if *fns*))

(defconst *f-not-index*
  (pos 'f-not *fns*))

(defconst *f0--index*
  (pos 'f0- *fns*))

(defconst *f-abs-index*
  (pos 'f-abs *fns*))

(defconst *f-1/x-index*
  (pos 'f-1/x *fns*))

(defconst *f-sqrt-index*
  (pos 'f-sqrt *fns*))

(defconst *f-sin-index*
  (pos 'f-sin *fns*))

(defconst *f-cos-index*
  (pos 'f-cos *fns*))

(defconst *f-tan-index*
  (pos 'f-tan *fns*))

(defconst *f-tanh-index*
  (pos 'f-tanh *fns*))

(defconst *f-exp-index*
  (pos 'f-exp *fns*))

(defconst *f+-index*
  (pos 'f+ *fns*))

(defconst *f--index*
  (pos 'f- *fns*))

(defconst *f*-index*
  (pos 'f* *fns*))

(defconst *f/-index*
  (pos 'f/ *fns*))

(defconst *f<-index*
  (pos 'f< *fns*))

(defconst *f=-index*
  (pos 'f= *fns*))

(defconst *f-mod-index*
  (pos 'f-mod *fns*))

(defconst *initial-vars*
;;; <!!matt> Delete junk1 and junk2 when all looks good, and modify write-csv
;;; accordingly (see other <!!matt> comments, including the one in write-csv).
  (list 'junk1
        'junk2
        '$time$
        '$hn$))

(defconst *$time$-index*
  (pos '$time$ *initial-vars*))

(defconst *$hn$-index*
  (pos '$hn$ *initial-vars*))
