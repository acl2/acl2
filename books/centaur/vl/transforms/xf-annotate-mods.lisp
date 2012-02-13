
(in-package "VL")

(include-book "centaur/vl/checkers/duplicate-detect" :dir :system)
(include-book "centaur/vl/checkers/portcheck" :dir :system)
(include-book "centaur/vl/transforms/xf-designwires" :dir :system)
(include-book "centaur/vl/transforms/xf-portdecl-sign" :dir :system)
(include-book "centaur/vl/transforms/xf-argresolve" :dir :system)
(include-book "centaur/vl/transforms/xf-orig" :dir :system)
(include-book "centaur/vl/transforms/cn-hooks" :dir :system)
(include-book "centaur/vl/transforms/xf-follow-hids" :dir :system)
(include-book "centaur/vl/mlib/warnings" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)


(defmacro xf-cwtime (form &key
                          name
                          (mintime '1)
                          ;; 64 MB minalloc to report
                          (minalloc '67108864))
  `(cwtime ,form
           :name ,name
           :mintime ,mintime
           :minalloc ,minalloc))



(defsection vl-annotate-mods

; Annotations that will be done to form the "origmods" in the server

  (defund vl-annotate-mods (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (b* ((mods (xf-cwtime (vl-modulelist-duplicate-detect mods)
                          :name xf-duplicate-detect))

         (mods (xf-cwtime (vl-modulelist-portcheck mods)
                          :name xf-portcheck))

         (mods (xf-cwtime (vl-modulelist-designwires mods)
                          :name xf-mark-design-wires))

         (mods (xf-cwtime (vl-modulelist-portdecl-sign mods)
                          :name xf-crosscheck-port-signedness))

         (mods (xf-cwtime (vl-modulelist-argresolve mods)
                          :name xf-argresolve))

         (mods (xf-cwtime (vl-modulelist-origexprs mods)
                          :name xf-origexprs))

         (mods (xf-cwtime (mp-verror-transform-hook mods)
                          :name xf-mp-verror))

         (mods (xf-cwtime (vl-modulelist-follow-hids mods)
                          :name xf-follow-hids))

         (mods (xf-cwtime (vl-modulelist-clean-warnings mods)
                          :name xf-clean-warnings)))

        mods))

  (local (in-theory (enable vl-annotate-mods)))

  (defthm vl-modulelist-p-of-vl-annotate-mods
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (vl-annotate-mods mods))))

  (defthm vl-modulelist->names-of-vl-annotate-mods
    (equal (vl-modulelist->names (vl-annotate-mods mods))
           (vl-modulelist->names mods))))

