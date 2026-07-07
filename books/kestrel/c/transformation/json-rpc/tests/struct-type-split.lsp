; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "../struct-type-split")
(include-book "../../tests/utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Invoke the struct-type-split method directly with by-name (object) params,
;; mirroring the params of example-request.json.  The method reads
;; input-files/test1.c, splits the "point" struct (moving member "z" into a new
;; "point_right" struct), and writes the result under out/.
;;
;; Note: we call the method directly rather than via process-json-rpc-file,
;; because the latter writes its JSON-RPC response with a non-bang output
;; channel, which ACL2 forbids during make-event expansion.  Over a live
;; socket (run-jsonrpc-server) the full dispatch path is exercised.

(make-event
 (b* ((params
       (make-structured-object
        :members
        (list (make-member :name "old-dir"
                           :value (value-string "input-files"))
              (make-member :name "new-dir"
                           :value (value-string "out"))
              (make-member :name "files"
                           :value (value-array (list (value-string "test1.c"))))
              (make-member :name "struct-tag"
                           :value (value-string "point"))
              (make-member :name "right-members"
                           :value (value-array (list (value-string "z"))))
              (make-member :name "new-tag"
                           :value (value-string "point_right"))
              (make-member :name "preprocess"
                           :value (value-false)))))
      ((mv erp res state) (struct-type-split params state))
      ((when erp)
       (mv (msg "struct-type-split method failed: ~x0" erp) nil state))
      ;; No warnings are expected for this input.
      (expected (value-object (list (make-member
                                     :name "warnings"
                                     :value (value-array nil)))))
      ((unless (equal res expected))
       (mv (msg "Unexpected result: ~x0" res) nil state)))
   (mv nil '(value-triple :struct-type-split-method-ran) state)))

;; The transformed C file matches the expected split.

(c2c::assert-file-contents
  :file "out/test1.c"
  :content "struct point {
  int x;
  int y;
};

struct point_right {
  int z;
};

static struct point p;

static struct point_right p_0;

int main(void) {
  p.x = 4;
  p_0.z = 2;
  return p.x + p_0.z;
}
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A duplicate parameter name is rejected with an invalid-params error,
;; rather than silently using the first occurrence.

(make-event
 (b* ((params
       (make-structured-object
        :members
        (list (make-member :name "old-dir"
                           :value (value-string "input-files"))
              (make-member :name "old-dir"
                           :value (value-string "elsewhere"))
              (make-member :name "new-dir"
                           :value (value-string "out"))
              (make-member :name "files"
                           :value (value-array (list (value-string "test1.c"))))
              (make-member :name "struct-tag"
                           :value (value-string "point"))
              (make-member :name "right-members"
                           :value (value-array (list (value-string "z")))))))
      ((mv erp & state) (struct-type-split params state))
      ((unless (errorp erp))
       (mv (msg "Expected an invalid-params error, but got: ~x0" erp)
           nil state))
      ((unless (equal (error->code erp) -32602))
       (mv (msg "Expected error code -32602, but got: ~x0" (error->code erp))
           nil state)))
   (mv nil '(value-triple :duplicate-parameter-rejected) state)))
