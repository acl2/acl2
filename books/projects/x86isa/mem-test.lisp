(include-book "centaur/defrstobj2/defrstobj" :dir :system)
(include-book "centaur/bigmem/bigmem" :dir :system)
(include-book "centaur/bitops/ihsext-basics" :dir :system)

(rstobj2::defrstobj mem-test
                    (mem   :type (array (unsigned-byte 8) (4503599627370496))
                           :initially 0
                           :fix (acl2::loghead 8 (ifix x))
                           :child-stobj bigmem::mem
                           :child-accessor bigmem::read-mem
                           :child-updater  bigmem::write-mem
                           :accessor memi
                           :updater !memi)
                    :enable '(bigmem::read-mem-over-write-mem
                               bigmem::read-mem-from-nil
                               bigmem::loghead-identity-alt))
