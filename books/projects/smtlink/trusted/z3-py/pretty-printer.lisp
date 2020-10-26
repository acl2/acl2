;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (6th June, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "datatypes")

(defsection SMT-pretty-print
  :parents (z3-py)
  :short "Pretty printer for SMT formula. Currently only change line every 160
  characters."

  (local (in-theory (enable paragraph-fix word-fix paragraph-p word-p)))

  (define flatten-paragraph ((p paragraph-p))
    :returns (fp word-listp)
    (b* ((p (paragraph-fix p))
         ((if (null p)) p)
         ((if (atom p)) (list p))
         ((cons first rest) p))
      (append (flatten-paragraph first)
              (flatten-paragraph rest))))

  (define pretty-print-recur ((thm word-listp) (wlimit natp) (acc natp))
    :returns (pretty-thm word-listp)
    :measure (len thm)
    (b* ((thm (word-list-fix thm))
         (wlimit (nfix wlimit))
         ((unless (consp thm)) nil)
         ((cons first rest) thm)
         ((if (<= wlimit acc))
          `(,first #\Newline
                   ,@(pretty-print-recur rest wlimit 0))))
      (cons first (pretty-print-recur rest wlimit (1+ acc)))))

  (define pretty-print-theorem ((thm paragraph-p) (wlimit natp))
    :returns (pretty-thm word-listp)
    :guard (>= wlimit 76)
    (b* ((thm (paragraph-fix thm))
         (fthm (flatten-paragraph thm)))
      (pretty-print-recur fthm wlimit 0)))

  )
