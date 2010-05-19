(in-package "ACL2")

(include-book "../lib2/top")

(local (include-book "log-support-proofs"))


(defthmd lnot-lognot
  (implies (and (natp n)
                (> n 0)
                (integerp x))
           (equal (lnot x n)
                  (bits (lognot x) (+ -1 n) 0))))



(defthmd land-logand
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (land x y n)
                  (bits (logand x y) (+ -1 n) 0))))

(defthmd lxor-logxor
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lxor x y n)
                  (bits (logxor x y) (+ -1 n) 0))))


(defthmd lior-logior
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lior x y n)
                  (bits (logior x y) (+ -1 n) 0))))




(defthmd logand-bits-reduce
  (implies (and (syntaxp (or (and (consp y)
                                  (not (equal (car y) 'bits)))
                             (symbolp y)))
                (bvecp y (+ 1 n))
                (natp n)
                (integerp x))
           (equal (logand (bits x n 0)
                          y)
                  (logand x y))))


(defthmd logand-bitn-reduce
  (implies (and (syntaxp (or (and (consp y)
                                  (not (equal (car y) 'bitn)))
                             (symbolp y)))
                (bvecp y 1)
                (integerp x))
           (equal (logand (bitn x 0)
                          y)
                  (logand x y))))


;;;;
;;;;
