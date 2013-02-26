(in-package "ACL2")

(set-inhibit-warnings "SUBSUME" "THEORY" "DISABLE" "NON-REC")

(include-book "model-raw")

(local (include-book "../../../../../rtl/rel4/lib/top"))

(local
    (include-book "../../../../../rtl/rel4/support/bvecp-helpers"))

(local
 (in-theory
   (set-difference-theories
        (current-theory :here)
        (union-theories
             '(bvecp)
             (union-theories (theory 'ACL2::RTL-OPERATORS-AFTER-MACRO-EXPANSION)
                             (theory 'ACL2::MODEL-RAW-DEFS))))))

(local (defthm bvecp-if
               (equal (bvecp (if x y z) n)
                      (if x (bvecp y n) (bvecp z n)))))

(local (in-theory (enable log=)))

(defbvecp FOO$RAW::out1 (n)
          1 :hints (("Goal" :expand ((FOO$RAW::out1 n)))))

(defbvecp FOO$RAW::out2 (n)
          4 :hints
          (("Goal" :expand ((FOO$RAW::out2 n))
                   :induct (sub1-induction n))))
