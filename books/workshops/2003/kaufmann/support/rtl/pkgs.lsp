(in-package "ACL2")

(defconst *old2new-pkg-alist*
          '(("FOO$RAW" . "ACL2")))

(include-book "package-defs")

(defconst *defrom-imports* 'nil)

(defconst *loop-vars* 'nil)

(defconst *loop-fns* 'nil)

(defconst *all-imports*
          (append *loop-vars* *defrom-imports*
                  *loop-fns* (shared-symbols)))

(defconst *foo-inputs*
          '(in0 in1 in2 in3 sel ww clk))

(defpkg "FOO$RAW"
        (append *foo-inputs* *all-imports*))

