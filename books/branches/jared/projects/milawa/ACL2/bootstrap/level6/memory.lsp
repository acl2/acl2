(in-package "ACL2")

;; We want to try boosting the threshold so that we can allocate more between gc's.

 -- we can try increasing the lisp-heap-gc-threshold
    (CCL::set-lisp-heap-gc-threshold (expt 2 31)) ;; 2 gigabytes
    (ACL2::save-exec "2gb-acl2" "Baseline, then with a 2 gigabyte threshold")

 -- we want to try not "releasing" pages because we cons at a high rate
    (CCL::gc-retain-pages t)
    (ACL2::save-exec "release-acl2" "Now retaining pages.")

 -- we might chang ethe egc-configuration by changing the sizes of the generations.
    we would need to experiment to find ideal values.
    (CCL::egc-configuration) --> 2048 4096 8192
    (CCL::configure-egc 4096 8192 16384)
    (ACL2::save-exec "2gen-acl2" "Baseline, then doubled the egc generation sizes")

 -- we probably don't need a value stack or temp stack as large as we're requesting
    we might not want to mess with the defaults at all.


 -- try turning off egc completely
    (CCL::egc nil)

 -- try clearing the memo tables after each crewrite?
    sol says we can use (acl2::clear-memoize-table 'foo) to just erase the table for
    foo.  maybe we want to get rid of the tables for:
      rw.assumptions-trace    (since assms probably won't be the same)
      rw.create-sigmas-to-try (since assms probably won't be the same)


