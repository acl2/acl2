;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

;; ======================================================================

(defconst *data-size* 32)

(defconst *v1* (list t))
(defconst *v000* (list nil nil nil))

(defconst *v0000* (list nil nil nil nil))
(defconst *v0001* (list t nil nil nil))
(defconst *v0010* (list nil t nil nil))
(defconst *v0011* (list t t nil nil))

(defconst *v0100* (list nil nil t nil))
(defconst *v0101* (list t nil t nil))
(defconst *v0110* (list nil t t nil))
(defconst *v0111* (list t t t nil))

(defconst *v1000* (list nil nil nil t))
(defconst *v1001* (list t nil nil t))
(defconst *v1010* (list nil t nil t))
(defconst *v1011* (list t t nil t))

(defconst *v1100* (list nil nil t t))
(defconst *v1101* (list t nil t t))
(defconst *v1110* (list nil t t t))
(defconst *v1111* (list t t t t))

(defconst *v00000* (list nil nil nil nil nil))
(defconst *v00001* (list t nil nil nil nil))
(defconst *v00010* (list nil t nil nil nil))
(defconst *v00011* (list t t nil nil nil))

(defconst *v00100* (list nil nil t nil nil))
(defconst *v00101* (list t nil t nil nil))
(defconst *v00110* (list nil t t nil nil))
(defconst *v00111* (list t t t nil nil))

(defconst *v01000* (list nil nil nil t nil))
(defconst *v01001* (list t nil nil t nil))
(defconst *v01010* (list nil t nil t nil))
(defconst *v01011* (list t t nil t nil))

(defconst *v01100* (list nil nil t t nil))
(defconst *v01101* (list t nil t t nil))
(defconst *v01110* (list nil t t t nil))
(defconst *v01111* (list t t t t nil))

(defconst *v10000* (list nil nil nil nil t))
(defconst *v10001* (list t nil nil nil t))
(defconst *v10010* (list nil t nil nil t))
(defconst *v10011* (list t t nil nil t))

(defconst *v10100* (list nil nil t nil t))
(defconst *v10101* (list t nil t nil t))
(defconst *v10110* (list nil t t nil t))
(defconst *v10111* (list t t t nil t))

(defconst *v11000* (list nil nil nil t t))
(defconst *v11001* (list t nil nil t t))
(defconst *v11010* (list nil t nil t t))
(defconst *v11011* (list t t nil t t))

(defconst *v11100* (list nil nil t t t))
(defconst *v11101* (list t nil t t t))
(defconst *v11110* (list nil t t t t))
(defconst *v11111* (list t t t t t))

(defconst *v000000* (list nil nil nil nil nil nil))
(defconst *v000100* (list nil nil t nil nil nil))
(defconst *v001000* (list nil nil nil t nil nil))
(defconst *v001100* (list nil nil t t nil nil))
(defconst *v010000* (list nil nil nil nil t nil))
(defconst *v010100* (list nil nil t nil t nil))
(defconst *v011000* (list nil nil nil t t nil))
(defconst *v011100* (list nil nil t t t nil))
(defconst *v100000* (list nil nil nil nil nil t))
(defconst *v100100* (list nil nil t nil nil t))
(defconst *v101000* (list nil nil nil t nil t))
(defconst *v101100* (list nil nil t t nil t))
(defconst *v110000* (list nil nil nil nil t t))
(defconst *v110100* (list nil nil t nil t t))
(defconst *v111000* (list nil nil nil t t t))
(defconst *v111100* (list nil nil t t t t))

(defconst *v0000011* (list t t nil nil nil nil nil))
(defconst *v0010110* (list nil t t nil t nil nil))
(defconst *v0100001* (list t nil nil nil nil t nil))
(defconst *v0100110* (list nil t t nil nil t nil))
(defconst *v0101110* (list nil t t t nil t nil))
(defconst *v1000000* (list nil nil nil nil nil nil t))
(defconst *v1001110* (list nil t t t nil nil t))
(defconst *v1010110* (list nil t t nil t nil t))
(defconst *v1011101* (list t nil t t t nil t))
(defconst *v1100110* (list nil t t nil nil t t))
(defconst *v1101011* (list t t nil t nil t t))
(defconst *v1110010* (list nil t nil nil t t t))
(defconst *v1110001* (list t nil nil nil t t t))






