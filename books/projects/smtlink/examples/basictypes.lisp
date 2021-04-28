;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (May 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "centaur/sv/tutorial/support" :dir :system)

;; BOZO: All basic FTY type definitions in the examples directory should
;; eventually be moved to this file.

;; (def-saved-event maybe-integer-example
;;   (defoption maybe-integer integerp
;;     :parents (tutorial))
;;   )
