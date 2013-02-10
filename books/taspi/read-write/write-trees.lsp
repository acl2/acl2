(include-book "misc/hons-help2" :dir :system)

(set-raw-mode-on!)

(defun start-nexus-file (str comment)
  (progn (format str "#NEXUS~%Begin trees;~%")
         (if comment
             (format str "[~%~A~%]~%" comment)
           (format str "~%"))))

(defun print-translate (str translate)
  (if (consp translate)
      (let ((key (caar translate))
            (val (cdar translate)))
        (progn (format str ",~%~T ~A ~A" key val)
               (print-translate str (cdr translate))))
    (format str ";~%")))

(defun add-translate (str translate)
  (if translate
      (progn (format str "Translate~%")
             (format str "~T ~A ~A"
                     (caar translate) 
                     (cdar translate))
             (print-translate str (cdr translate)))
    nil)) ;; do nothing

(defun new-tip (x)
  (if (consp x)
      (and (atom (car x))
           (atom (cdr x)))
    t))

;; takes a single taspi tree, returns newick string representation
(defun to-newick-string (flg tree &optional internal-names cur-internal)
  (if flg ;; top-level list
      (if (new-tip tree)
          (if (consp tree)
              (if (acl2-numberp (cdr tree))
                  (format nil "~A:~F" (car tree) (cdr tree))
                  (format nil "~A:~A" (car tree) (cdr tree)))
            (format nil "~A" tree))
        (if (atom (cdr tree))
            (let ((new-internal (cdr (assoc-hqual (car tree)
                                     internal-names))))
              (format nil "~A:~F" 
                      (to-newick-string t (car tree)
                                        internal-names
                                        new-internal)
                      (cdr tree)))
          (let ((new-internal1 (cdr (assoc-hqual (car tree) 
                                                 internal-names)))
                (new-internal2 (cdr (assoc-hqual tree internal-names))))
            (format nil "(~A,~A" (to-newick-string t (car tree)
                                                   internal-names
                                                   new-internal1)
                    (to-newick-string nil (cdr tree) 
                                      internal-names new-internal2)))))
    (if (consp tree)
        (if (consp (cdr tree))
            (let ((new-internal (cdr (assoc-hqual (car tree)
                                                  internal-names))))
              (format nil "~A,~A" (to-newick-string t (car tree) 
                                                    internal-names
                                                    new-internal)
                      (to-newick-string nil (cdr tree) internal-names
                                        nil)))
          (let ((new-internal (cdr (assoc-hqual (car tree) 
                                                internal-names))))
            (if cur-internal
                (format nil "~A)~A" (to-newick-string t (car tree) 
                                                    internal-names
                                                    new-internal)
                        cur-internal)
              (format nil "~A)" (to-newick-string t (car tree) 
                                                  internal-names
                                                  new-internal)))))
      (if cur-internal
          (format nil ")~A" cur-internal)
        ")"))))

(defun print-newick (str tree &optional internal)
  (format str "~A;~%" (to-newick-string t tree internal)))

(defun add-newick-tree (str tree count &optional internal)
  (progn (format str "tree TASPI_~A = " count)
         (print-newick str tree internal)
         (1+ count)))

(defun add-newick-trees (str list-of-trees count &optional internal)
  (if (consp list-of-trees)
      (let ((count (add-newick-tree str (car list-of-trees) count internal)))
        (add-newick-trees str (cdr list-of-trees) count internal))
    nil)) ;; do nothing, we're done
            
;; Main function, always takes a list of trees
(defun trees-to-nexus (list-of-trees filename 
                                     &key translate comment internals)
  (with-open-file (str filename :direction :output
                       :if-exists :supersede)
    (progn (start-nexus-file str comment) ;; ends after beginning trees;
           (add-translate str translate) ;; add translate block if present
           (add-newick-trees str list-of-trees 0 internals) 
           (format str "End;") ;; close tree block
           )))
