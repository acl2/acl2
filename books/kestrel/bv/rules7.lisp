; More BV rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat")
(include-book "bitnot")
(local (include-book "rules"))

(defthmd bvcat-of-bitnot-and-bitnot
  (equal (bvcat 1 (bitnot x) 1 (bitnot y))
         (bvnot 2 (bvcat 1 x 1 y))))

(defthmd bvcat-of-bvnot-and-bitnot
  (implies (posp size) ;why not 0?
           (equal (bvcat size (bvnot size x) 1 (bitnot y))
                  (bvnot (+ 1 size) (bvcat size x 1 y)))))

(defthmd bvcat-of-bitnot-and-bvnot
  (implies (posp size) ;why not 0?
           (equal (bvcat 1 (bitnot x) size (bvnot size y))
                  (bvnot (+ 1 size) (bvcat 1 x size y)))))

(defthmd bvcat-of-bvnot-and-bvnot
  (implies (and (posp highsize) ;why not 0?
                (posp lowsize) ;why not 0?
                )
           (equal (bvcat highsize (bvnot highsize highval) lowsize (bvnot lowsize lowval))
                  (bvnot (+ highsize lowsize) (bvcat highsize highval lowsize lowval)))))
