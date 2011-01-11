(in-package "ACL2")

(include-book "model")

(local (include-book "model-eq"))

(local (include-book "bvecp-raw"))

(local (include-book "../../../../../rtl/rel4/support/bvecp-helpers"))

(defbvecp out1 (n)
          1
          :hints (("Goal" :use foo$raw::bvecp$out1)))

(defbvecp out2 (n)
          4
          :hints (("Goal" :use foo$raw::bvecp$out2)))

