#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;;
;; Simple Equivalence-Based Maps for ACL2
;; Jared Davis 
;;
;; aliases.lisp - Macro aliases for map functions.  
;;
;; Our intention is that this file will only be loaded by books in packages
;; which have chosen to import the symbols in MAPS::*exports*.  We provide
;; macro aliases with longer names to the maps functions, which add the prefix
;; "map" onto each function.  This way, you can avoid seeing the ugly MAPS::
;; everywhere, while we still get to have nice short names for our functions.

(in-package "MAP")
(include-book "maps")

(defmacro mapdefault ()
  `(default))

;; We don't provide an alias for mapp 

;; We don't provide an alias for emptymap

(defmacro mapfix (map)
  `(fix ,map))

(defmacro mapoptimize (map)
  `(optimize ,map))

(defmacro mapdomain (map)
  `(domain ,map))

(defmacro mapget (key map)
  `(get ,key ,map))

(defmacro mapset (key val map)
  `(set ,key ,val ,map))

(defmacro maperase (key map)
  `(erase ,key ,map))

(defmacro mapin (key map)
  `(set::in ,key (domain ,map)))

;; We don't provide an alias for submap

(defmacro mapequiv (x y)
  `(equiv ,x ,y))

(defmacro maphead (map)
  `(head ,map))

(defmacro maptail (map)
  `(erase (head ,map) ,map))

(defmacro mapempty (map)
  `(set::empty (domain ,map)))

(defmacro mapempty-exec (map)
  `(empty-exec ,map))



;; We use untranslate patterns in order to make these aliases "more real" for
;; the user.  As a result, the aliases will be displayed in proof attempts,
;; rather than MAPS::erase, etc.

(ACL2::add-untranslate-pattern (default)
                               (mapdefault))

(ACL2::add-untranslate-pattern (fix ?map) 
                               (mapfix ?map))

(ACL2::add-untranslate-pattern (optimize ?map) 
                               (mapoptimize ?map))

(ACL2::add-untranslate-pattern (domain ?map) 
                               (mapdomain ?map))

(ACL2::add-untranslate-pattern (get ?key ?map) 
                               (mapget ?key ?map))

(ACL2::add-untranslate-pattern (set ?key ?val ?map) 
                               (mapset ?key ?val ?map))

(ACL2::add-untranslate-pattern (erase ?key ?map) 
                               (maperase ?key ?map))

(ACL2::add-untranslate-pattern (set::in ?key (domain ?map)) 
                               (mapin ?key ?map))

(ACL2::add-untranslate-pattern (equiv ?x ?y) 
                               (mapequiv ?x ?y))

(ACL2::add-untranslate-pattern (head ?map) 
                               (maphead ?map))

(ACL2::add-untranslate-pattern (erase (head ?map) ?map) 
                               (maptail ?map))

(ACL2::add-untranslate-pattern (set::empty (domain ?map)) 
                               (mapempty ?map))

(ACL2::add-untranslate-pattern (empty-exec ?map) 
                               (mapempty-exec ?map))

(ACL2::optimize-untranslate-patterns)



;; Finally, we add macro aliases that allow you to enable or disable the
;; aliases for map functions directly.

(add-macro-alias mapfix fix)

(add-macro-alias mapoptimize optimize)

(add-macro-alias mapdomain domain)

(add-macro-alias mapget get)

(add-macro-alias mapset set)

(add-macro-alias maperase erase)

(add-macro-alias mapequiv equiv)

(add-macro-alias maphead head)

(add-macro-alias mapempty-exec empty-exec)

