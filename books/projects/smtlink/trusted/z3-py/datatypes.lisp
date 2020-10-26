;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (24th May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "./names")
(include-book "../../utils/basics")

(defsection Translation-datatypes
  :parents (trusted)
  :short "Datatypes for the translation in trusted clause-processor"

  (define word-p ((atom))
    (declare (xargs :guard t))
    :returns (word? booleanp)
    (if (or (acl2-numberp atom)
            (symbolp atom)
            (characterp atom)
            (stringp atom))
        t
      nil))

  (easy-fix word nil)

  (defthm word-p-of-lisp-to-python-names
    (word-p (lisp-to-python-names x))
    :hints (("Goal" :in-theory (enable word-p))))

  (deflist word-list
    :elt-type word-p
    :pred word-listp
    :true-listp t)

  (define paragraph-p ((par))
    :parents (SMT-translator)
    (declare (xargs :guard t))
    :returns (paragraph? booleanp)
    :short "A paragraph is made up of lists of words. Notice a single word is also counted as a paragraphp."
    (if (atom par)
        (word-p par)
      (and (paragraph-p (car par)) (paragraph-p (cdr par)))))

  (defthm paragraph-p-corollary-1
    (implies (word-p x) (paragraph-p x))
    :hints (("Goal" :in-theory (enable paragraph-p word-p))))

  (defthm paragraph-p-corollary-2
    (implies (and (consp x) (paragraph-p (car x))
                  (paragraph-p (cdr x)))
             (paragraph-p x))
    :hints (("Goal" :in-theory (enable paragraph-p))))

  (defthm paragraph-p-corollary-3
    (implies (and (consp x) (paragraph-p x))
             (and (paragraph-p (car x))
                  (paragraph-p (cdr x))))
    :hints (("Goal" :in-theory (enable paragraph-p))))

  (defthm paragraph-p-corollary-4
    (implies (and (paragraph-p a) (paragraph-p b))
             (paragraph-p (append a b))))

  (easy-fix paragraph nil)

  (defthm paragraph-p-corollary-5
    (implies (consp a)
             (<= (acl2-count (paragraph-fix a))
                 (acl2-count a)))
    :hints (("Goal" :in-theory (enable paragraph-fix)))
    :rule-classes (:linear))

  (defthm word-listp-is-paragraph-p
    (implies (word-listp x)
             (paragraph-p x))
    :hints (("Goal" :in-theory (enable word-listp paragraph-p))))

  )
