; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "points")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ points-fty
  :parents (points)
  :short "Fixtype support for elliptic curve points."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a fixtype for @(tsee pointp),
     along with some functions and theorems
     to treat elliptic curve points as if they were defined as")
   (xdoc::codeblock
    "(fty::deftagsum point"
    "  (:finite ((x nat) (y nat)))"
    "  (:infinite ())"
    "  :pred pointp"
    "  :xvar p)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deffixer point-fix
  :short "Fixer of elliptic curve points."
  :pred pointp
  :body-fix :infinity)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection point
  :short "Fixtype of elliptic curve points."
  (fty::deffixtype point
    :pred pointp
    :fix point-fix
    :equiv point-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-kind ((p pointp))
  :returns (kind keywordp)
  :short "Kinds (i.e. tags) of elliptic curve points."
  (mbe :logic (if (and (pointp p) (consp p)) :finite :infinite)
       :exec (if (consp p) :finite :infinite))

  ///

  (fty::deffixequiv point-kind
    :hints (("Goal" :in-theory (enable point-fix))))

  (defrule point-kind-possibilities
    (or (equal (point-kind p) :finite)
        (equal (point-kind p) :infinite))
    :rule-classes ((:forward-chaining :trigger-terms ((point-kind p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-finite->x ((p pointp))
  :guard (equal (point-kind p) :finite)
  :returns (x natp :hints (("Goal" :in-theory (enable point-fix pointp))))
  :short "Get the @('x') coordinate of a finite elliptic curve point."
  (b* ((p (mbe :logic (point-fix p) :exec p)))
    (if (consp p)
        (car p)
      0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-finite->y ((p pointp))
  :guard (equal (point-kind p) :finite)
  :returns (y natp :hints (("Goal" :in-theory (enable point-fix pointp))))
  :short "Get the @('y') coordinate of a finite elliptic curve point."
  (b* ((p (mbe :logic (point-fix p) :exec p)))
    (if (consp p)
        (cdr p)
      0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-finite ((x natp) (y natp))
  :returns (p pointp :hints (("Goal" :in-theory (enable pointp))))
  :short "Build a finite elliptic curve point."
  (b* ((x (mbe :logic (nfix x) :exec x))
       (y (mbe :logic (nfix y) :exec y)))
    (cons x y))
  :hooks (:fix)

  ///

  (defrule point-kind-of-point-finite
    (equal (point-kind (point-finite x y))
           :finite)
    :enable (point-kind pointp))

  (defrule point-finite->x-of-point-finite
    (equal (point-finite->x (point-finite x y))
           (nfix x))
    :enable (point-finite->x pointp))

  (defrule point-finite->y-of-point-finite
    (equal (point-finite->y (point-finite x y))
           (nfix y))
    :enable (point-finite->y pointp))

  (defrule point-finite-of-point-finite->x/y
    (implies (equal (point-kind p) :finite)
             (equal (point-finite (point-finite->x p)
                                  (point-finite->y p))
                    (point-fix p)))
    :enable (point-finite->x point-finite->y point-kind pointp))

  (defruled point-fix-when-finite
    (implies (equal (point-kind p) :finite)
             (equal (point-fix p)
                    (point-finite (point-finite->x p)
                                  (point-finite->y p))))
    :enable (point-finite->x point-finite->y point-kind pointp))

  (defruled equal-of-point-finite
    (equal (equal (point-finite x y) p)
           (and (pointp p)
                (equal (point-kind p) :finite)
                (equal (point-finite->x p) (nfix x))
                (equal (point-finite->y p) (nfix y))))
    :enable (point-finite->x point-finite->y point-kind pointp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-infinite ()
  :returns (p pointp)
  :short "Build the elliptic curve point at infinity."
  ':infinity

  ///

  (defrule point-kind-of-point-infinite
    (equal (point-kind (point-infinite))
           :infinite))

  (defruled point-fix-when-infinite
    (implies (equal (point-kind p) :infinite)
             (equal (point-fix p)
                    (point-infinite)))
    :enable (point-kind point-fix pointp))

  (defruled equal-of-point-infinite
    (equal (equal (point-infinite) p)
           (and (pointp p)
                (equal (point-kind p) :infinite)))
    :enable (point-kind point-fix pointp)))
