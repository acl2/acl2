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

(defsection Translation-datatypes
  :parents (trusted)
  :short "Datatypes for the translation in trusted clause-processor"

  (define wordp ((atom))
    (declare (xargs :guard t))
    :returns (word? booleanp)
    (if (or (acl2-numberp atom)
            (symbolp atom)
            (characterp atom)
            (stringp atom))
        t
      nil))

  (define word-fix ((atom wordp))
    :returns (fixed wordp)
    (mbe :logic (if (wordp atom) atom nil)
         :exec atom)
    ///
    (more-returns
     (fixed (equal (word-fix fixed) fixed)
            :name equal-word-fixed)))

  (local (in-theory (enable word-fix)))
  (deffixtype word
    :fix word-fix
    :pred wordp
    :equiv word-equiv
    :define t)

  (defthm wordp-of-lisp-to-python-names
    (wordp (lisp-to-python-names x))
    :hints (("Goal" :in-theory (enable wordp))))

  (deflist word-list
    :elt-type wordp
    :pred word-listp
    :true-listp t)

  (define paragraphp ((par))
    :parents (SMT-translator)
    (declare (xargs :guard t))
    :returns (paragraph? booleanp)
    :short "A paragraph is made up of lists of words. Notice a single word is also counted as a paragraphp."
    (if (atom par)
        (wordp par)
      (and (paragraphp (car par)) (paragraphp (cdr par)))))

  (defthm paragraphp-corollary-1
    (implies (wordp x) (paragraphp x))
    :hints (("Goal" :in-theory (enable paragraphp wordp))))

  (defthm paragraphp-corollary-2
    (implies (and (consp x) (paragraphp (car x)) (paragraphp (cdr x))) (paragraphp x))
    :hints (("Goal" :in-theory (enable paragraphp))))

  (defthm paragraphp-corollary-3
    (implies (and (consp x) (paragraphp x))
             (and (paragraphp (car x))
                  (paragraphp (cdr x))))
    :hints (("Goal" :in-theory (enable paragraphp))))

  (defthm paragraphp-corollary-4
    (implies (and (paragraphp a) (paragraphp b))
             (paragraphp (append a b))))

  (encapsulate ()
    (local (in-theory (enable paragraphp)))
    (define paragraph-fix ((x paragraphp))
      :returns (fixed paragraphp)
      (mbe :logic (if (consp x)
                      (cons (paragraph-fix (car x)) (paragraph-fix (cdr x)))
                    (word-fix x))
           :exec x)
      ///
      (more-returns
       (fixed (<= (acl2-count fixed) (acl2-count x))
              :name acl2-count-of-fixed-smaller
              :rule-classes :linear)
       (fixed (implies (consp fixed)
                       (< (acl2-count (car fixed)) (acl2-count x)))
              :name acl2-count-of-car-of-fixed-smaller
              :rule-classes :linear)
       (fixed (implies (consp fixed)
                       (< (acl2-count (cdr fixed)) (acl2-count x)))
              :name acl2-count-of-cdr-of-fixed-smaller
              :rule-classes :linear)
       (fixed (implies (paragraphp x)
                       (equal fixed x))
              :name equal-of-fixed-to-x)))
    )

  (encapsulate ()
    (local (in-theory (enable paragraph-fix)))
    (deffixtype paragraph
      :fix paragraph-fix
      :pred paragraphp
      :equiv paragraph-equiv
      :define t)
    )

  (defthm word-listp-is-paragraphp
    (implies (word-listp x)
             (paragraphp x))
    :hints (("Goal" :in-theory (enable word-listp paragraphp))))

  )
