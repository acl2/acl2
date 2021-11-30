; Banach-Tarski theorem
;
;
; Copyright (C) 2021 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Authors: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "workshops/2003/cowles-gamboa-van-baalen_matrix/support/matalg" :dir :system)

;; Below theorems normalize the name param of array2p. Copied from the book acl2-arrays/acl2-arrays.lisp.
;; Thanks to Eric Smith for suggesting to refer to the acl2-arrays.lisp book.

(defthm normalize-header-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (header name l)
                  (header :fake-name l)))
  :hints (("Goal" :in-theory (enable header))))

(defthm normalize-default-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (default name l)
                  (default :fake-name l)))
  :hints (("Goal" :in-theory (enable default))))

(defthm normalize-maximum-length-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (maximum-length name l)
                  (maximum-length :fake-name l)))
  :hints (("Goal" :in-theory (enable maximum-length))))

(defthm normalize-dimensions-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (dimensions name l)
                  (dimensions :fake-name l)))
  :hints (("Goal" :in-theory (enable dimensions))))

(defthm normalize-compress11-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress11 name l i n default)
                  (compress11 :fake-name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm normalize-compress1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress1 name l)
                  (compress1 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress1))))

(defthm normalize-compress211-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress211 name l i x j default)
                  (compress211 :fake-name l i x j default)))
  :hints (("Goal" :in-theory (enable compress211))))

(defthm normalize-compress21-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress21 name l n i j default)
                  (compress21 :fake-name l n i j default)))
  :hints (("Goal" :in-theory (enable compress21))))

(defthm normalize-compress2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress2 name l)
                  (compress2 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress2))))

(defthm normalize-aref2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref2 name l i j)
                  (aref2 :fake-name l i j)))
  :hints (("Goal" :in-theory (enable aref2))))

(defthm normalize-array2p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array2p name l)
                  (and (symbolp name)
                       (array2p :fake-name l))))
  :hints (("Goal" :in-theory (enable array2p))))

;; normalizing the name param of alist2p

(defthm normalize-alist2p-name
  (implies (and (syntaxp (not (equal name '':fake-name)))
		(symbolp name))
           (equal (alist2p name l)
                  (alist2p :fake-name l)))
  :hints (("Goal" :in-theory (e/d (alist2p) ()))))
