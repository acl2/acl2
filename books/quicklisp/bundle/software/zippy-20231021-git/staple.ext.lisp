(asdf:load-system :staple-markless)

(defpackage "zippy-docs"
  (:use #:cl)
  (:local-nicknames
   (#:zippy #:org.shirakumo.zippy)))

(defclass page* (staple:simple-page)
  ()
  (:default-initargs :document-package (find-package "zippy-docs")))

(defmethod staple:page-type ((system (eql (asdf:find-system :zippy))))
  'page*)

(defmethod staple:definition-wanted-p ((_ definitions:source-transform) (page page*)) NIL)
