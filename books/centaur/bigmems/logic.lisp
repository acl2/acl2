(in-package "BIGMEMS")

(include-book "std/util/define" :dir :system)
(include-book "centaur/defrstobj2/def-multityped-record" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

(defn ubp8-fix (x)
  (acl2::loghead 8 (ifix x)))

#!RSTOBJ2
(def-multityped-record ubp8
  :elem-p       (unsigned-byte-p 8 x)
  :elem-default 0
  :elem-fix     (bigmems::ubp8-fix x)
  :in-package-of bigmems::bigmems-pkg)

(defn mem$ap (mem$a)
  (declare (ignore mem$a))
  t)

(defn create-mem$a ()
  nil)

(define read-mem$a ((addr :type (unsigned-byte 64))
                    (mem$a mem$ap))
  (ubp8-get addr mem$a))

(define write-mem$a ((addr :type (unsigned-byte 64))
                     (val  :type (unsigned-byte 8))
                     (mem$a mem$ap))
  (ubp8-set addr val mem$a))
