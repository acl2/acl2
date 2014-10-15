(comp t)
(er-progn
 (assign write-bookdata nil) 
 (fix-certs-fn *standard-book-list* :system 'fix-cert state)
 (mv-let (chan state)
	  (open-output-channel (string-append (@ system-books-dir)
					      "saved_dir")
			       :character
			       state)
	  (if (not chan)
	    (mv t :invisible state)
	    (pprogn (princ$ (@ system-books-dir)
			    chan
			    state)
		    (close-output-channel chan state)
		    (mv nil :invisible state)))))
