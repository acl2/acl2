; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann; guard verification added by Eric Smith
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "pseudo-good-worldp") ; :logic mode macro-args-structurep etc.

(include-book "verified-termination-and-guards") ; :logic mode er-cmp-fn

(include-book "kestrel") ; :logic mode macro-args

(verify-termination warning-off-p1) ; and guards

(verify-termination warning1-cw) ; and guards

(verify-termination duplicate-keys-action) ; and guards

(local
 (defthm keyword-value-listp-remove-keyword
   (implies (keyword-value-listp x)
            (keyword-value-listp (remove-keyword key x)))))

(local
 (defthm keyword-value-listp-cddr-assoc-keyword
   (implies (keyword-value-listp x)
            (keyword-value-listp (cddr (assoc-keyword key x))))))

(verify-termination bind-macro-args-keys1
  (declare (xargs :measure (acl2-count args)
                  :verify-guards nil)))

(verify-termination chk-length-and-keys) ; and guards

(verify-termination bind-macro-args-keys
  (declare (xargs :verify-guards nil)))

(verify-termination bind-macro-args-after-rest
  (declare (xargs :verify-guards nil)))

(verify-termination bind-macro-args-optional
  (declare (xargs :measure (acl2-count args)
                  :verify-guards nil)))

(verify-termination bind-macro-args1
  (declare (xargs :measure (acl2-count args)
                  :verify-guards nil)))

(verify-termination bind-macro-args
  (declare (xargs :verify-guards nil)))

(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/utilities/keyword-value-lists2" :dir :system))
(local (include-book "kestrel/utilities/assoc-keyword" :dir :system))
(local (include-book "kestrel/utilities/intern-in-package-of-symbol" :dir :system))
(local (include-book "kestrel/utilities/member-symbol-name" :dir :system))
(local (include-book "kestrel/utilities/chk-length-and-keys" :dir :system))

(local (in-theory (disable true-listp
                           macro-arglist-keysp
                           plist-worldp
                           symbol-alistp
                           keyword-value-listp
                           fgetprop
                           assoc-keyword
                           macro-arglist-optionalp
                           chk-length-and-keys
                           weak-state-vars-p
                           table-alist
                           mv-nth
                           macro-arglist1p
                           macro-arglist-optionalp)))

(verify-guards bind-macro-args-keys1
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable (:d macro-arglist-keysp)))))

(verify-guards bind-macro-args-keys)

(verify-guards bind-macro-args-after-rest)

(verify-guards bind-macro-args-optional
  :hints (("Goal" :in-theory (enable (:d macro-arglist-optionalp)))))

(verify-guards bind-macro-args1
  :hints (("Goal" :expand ((macro-arglist1p args)))))

(verify-guards bind-macro-args)
