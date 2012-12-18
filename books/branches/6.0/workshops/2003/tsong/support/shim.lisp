(IN-PACKAGE "ACL2")
(include-book "../../../../data-structures/structures")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;                    tools function
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun ith(i a)
	(declare (xargs :guard (and (integerp i) (> i 0))))
  	(   cond   ((atom a) nil)
	     	((zp (- i 1)) (car a))
	     	((ith (- i 1) (cdr a)))
	)
)
(defun strlistp (strlist)
	(    if (endp strlist)     t
		(and
		(stringp (car strlist))
		(strlistp (cdr strlist))
		)
    	)
)
(defun strmem(str strlist)
  	(if (strlistp strlist)
      	(
       		if (endp strlist)
		nil
		(or (string-equal str (car strlist)) (strmem str (cdr strlist)))
	)
    	nil
    	)
)
(defun InPath(pathin pathsrc)
(cond ((endp pathsrc) t)
      ((and (endp pathin)(not (endp pathsrc))) nil)
      ((not (equal (car pathin)(car pathsrc))) nil)
      ((equal (car pathin) (car pathsrc)) (InPath(cdr pathin)(cdr pathsrc)))
)
)

(defun path-equal (path1 path2)
(cond ((and (endp path1)(endp path2)) t)
      ((and (endp path1)(not (endp path2))) nil)
      ((and (endp path2)(not (endp path1))) nil)
      ((not (equal (car path1)(car path2))) nil)
      ((equal (car path1) (car path2)) (path-equal(cdr path1)(cdr path2)))
)
)
(defun path-append (path1 path2)
(append path1 path2)
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;             formalizaion of log data
;
;log record: ((prog ruid pid euid egid)
;             (name ouid ogid pmode inodeid)
;             (syscall flags)
;             (newowner, newmode, newpath, chpid))......
;pmode: ((r w x)(r w x)(r w x)(dir reg socket pipe))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(defun natp(x)
	(and (<= 0 x)
       	(integerp x))
)
|#

(defstructure proc-obj
  	prog
  	(ruid (:assert (integerp ruid)))
  	(pid  (:assert (integerp pid)))
  	(euid (:assert (integerp euid)))
  	(egid (:assert (integerp egid)))
)

(defstructure rwx-obj
	r
	w
	x
)
(defstructure attr-obj
	(dir (:assert (integerp dir)))
	(reg (:assert (integerp reg)))
	(socket (:assert (integerp socket)))
	(pipe (:assert (integerp pipe)))
)
(defstructure pmode-obj
   	(umode (:assert (and (consp umode)(rwx-obj-p umode)) ))
   	(gmode (:assert (and (consp gmode)(rwx-obj-p gmode))))
   	(amode (:assert (and (consp amode)(rwx-obj-p amode))))
   	(attr  (:assert (and (consp attr)(attr-obj-p attr))))
)
(defstructure file-obj
 	(name (:assert (consp name)))
 	(ouid (:assert (integerp ouid)))
 	(ogid (:assert (integerp ogid)))
 	(pmode (:assert (pmode-obj-p pmode)))
 	(inodeid (:assert (integerp inodeid)))
 )
(defstructure syscall-obj
	callname
	flags
)
(defstructure newattr-obj
	newowner
	newmode
	newpath
	chpid
)
(defstructure logrec
  	(pobj (:assert (and (consp pobj)(proc-obj-p pobj))))
  	(fobj (:assert (and (consp fobj)(file-obj-p fobj))))
  	(callobj (:assert (and (consp callobj)(syscall-obj-p callobj))))
  	(newattrobj (:assert (newattr-obj-p newattrobj)))
)


(defun logp (log)
  	(if (endp log) t
    	(and (logrec-p (car log))
	(consp (car log))
	(logp (cdr log))))
  )


(defun getsyscall (logrec)
  	(logrec-callobj logrec)
  )


(defun getcallname (logrec)
  	(syscall-obj-callname (logrec-callobj logrec))
  )

(defun getcallflag (logrec)
  	(syscall-obj-flags (logrec-callobj logrec))
  )

(defun getproc (logrec)
  	(logrec-pobj logrec)
  )


(defun getprocname (logrec)
  	( proc-obj-prog(logrec-pobj logrec))
  )

(defun getprocruid (logrec)
  	(proc-obj-ruid (logrec-pobj logrec))
  )

(defun getprocpid (logrec)
  	(proc-obj-pid (logrec-pobj logrec))
  )

(defun getproceuid (logrec)
  	(proc-obj-euid (logrec-pobj logrec))
  )

(defun getprocegid (logrec)
  	(proc-obj-egid (logrec-pobj logrec)))
;  ) ; extra paren removed by Matt K.


    (defun getfile (logrec)
        (logrec-fobj logrec)
    )

    ;(filep '(/home/tsong/file 23 2 ((1 1 0) (1 0 0) (1 0 0)) 23021))
    (defun getfilename ( fileobj)
    	(file-obj-name fileobj)
    )
    (defun getfileouid( fileobj)
        (file-obj-ouid fileobj)
    )
    (defun getfileogid( fileobj)
        (file-obj-ogid fileobj)
    )
    (defun getfilemode( fileobj)
        (file-obj-pmode fileobj)
    )
    (defun getinodeid( fileobj)
        (file-obj-inodeid fileobj)
    )
    (defun getreg(fileobj)
        (attr-obj-reg(pmode-obj-attr(file-obj-pmode fileobj)))
    )
    (defun getsocket( fileobj)
        (attr-obj-socket(pmode-obj-attr(file-obj-pmode fileobj)))
    )
    (defun getpipe( fileobj)
        (attr-obj-pipe(pmode-obj-attr(file-obj-pmode fileobj)))
    )
    ;(file-obj-pmode '(/home/tsong/file 23 2 ((1 1 0) (1 0 0) (1 0 0)) 23021))


    ;(newprop '(0 ((1 1 0) (1 0 0) (1 0 0)) /root/file 4108))

    ;(logrecp '((ftpd 23 3405 0 0) (/home/tsong/file 23 2 ((1 1 0) (1 0 0) (1 0 0))23021) (open r)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;             formalization of system
;
;log: ((prog ruid pid euid egid) (name ouid ogid pmode inodeid)(syscall flags) (newowner, newmode, newpath, chpid))......
;system:(((pname pdir)...)((callname)..)((dir ouid ogid pmode inodeid)...)((uid uname gid homedir)...)((envname envvalue)...))
;(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1))))((0 root "/") (23 tsong "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print")))
;system: (proclist calllist filelist userlist envlist)
;proclist:((pname pdir)...)
;calllist:((callname)...)
;filelist:((dir ouid ogid pmode inodeid)...)
;pmode: ((r w x)(r w x)(r w x)(dir reg socket pipe))
;userlist:((uid uname gid homedir)...)
;envlist:((envname envvalue)...)
;(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1))))((0 root "/") (23 tsong "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print")))
;
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


    (defstructure prog-obj
	pname
	pdir
    )
    (defstructure call-obj
	callname
    )
    (defstructure user-obj
	uid
	uname
	gid
	(homedir (:assert (consp homedir)))
    )
    (defstructure env-obj
	envname
	envvalue
    )

    (defun filelistp (filelist)
        (if (endp filelist) t
            	(and
                (and (consp (car filelist))(file-obj-p (car filelist)))
	        (filelistp (cdr filelist))
		)
        )
    )

    (defun proglistp (proclist)
        (if (endp proclist) t
                (and
	        (and (consp (car proclist))(prog-obj-p (car proclist)))
	        (proglistp (cdr proclist))
		)
        )
    )

    (defun calllistp (calllist)
        (if (endp calllist) t
                (and
	        (and (consp (car calllist))(call-obj-p (car calllist)))
	        (calllistp (cdr calllist))
		)
        )
    )
    (defun userlistp (userlist)
        (if (endp userlist) t
                (and
	        (and (consp (car userlist))(user-obj-p (car userlist)))
	        (userlistp (cdr userlist))
		)
        )
    )

    (defun envlistp (envlist)
        (if (endp envlist) t
                (and
	        (and (consp (car envlist))(env-obj-p (car envlist)))
	        (envlistp (cdr envlist))
		)
        )
    )

    (defstructure sys
        (proglist (:assert (and (not (endp proglist))(proglistp proglist))))
        (calllist (:assert (and (not (endp calllist))(calllistp calllist))))
        (filelist (:assert (and (not (endp filelist))(filelistp filelist))))
        (userlist (:assert (and (not (endp userlist))(userlistp userlist))))
        (envlist (:assert (and (not (endp envlist))(envlistp envlist))))
    )


;(proclistp '((ftp "/bin/ftp")(lpr "/bin/lpr")))
;(calllistp '((create)(open)(read)(write)(chmod)(chown)))
;(filelistp '(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1003)))
;(userlistp '((0 root "/") (23 tsong "/home/tsong")))
;(envlistp '((printpool "/temp/print")(printdir "/temp/print")))
;(sys-p '(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1003))((0 root 0 "/") (23 tsong 2 "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print"))))
;(((ftpd)())()()()())
    (defun getproclist (sys)
        (sys-proglist sys)
    )
    (defun getcalllist (sys)
        (sys-calllist sys)
    )
    (defun getfilelist (sys)
        (sys-filelist sys)
    )
    (defun getuserlist (sys)
        (sys-userlist sys)
    )
    (defun getenvlist (sys)
        (sys-envlist sys)
    )
    (defun getenv (envlist envname)
        (if (endp envlist)
	    nil
	    ( if (equal (env-obj-envname(car envlist)) envname)
	        (env-obj-envvalue(car envlist))
		(getenv (cdr envlist) envname)
	    )
	)
    )
    (defun getprinterdir(sys)
        (getenv (getenvlist sys ) 'printerdir)
    )
    (defun getprinterspool(sys)
        (getenv (getenvlist sys ) 'printerspool)
    )


    (defun homedir (userlist uid)
        (if (endp userlist)
	    nil
	    ( if (equal (user-obj-uid(car userlist)) uid)
	        (user-obj-homedir(car userlist))
		(homedir (cdr userlist) uid)
	    )
	)
    )
    (defun gethomedir (uid sys)
        (homedir (sys-userlist sys) uid)
    )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;     operation and relationship function of specs
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun operate (oper logrec)
  ( if  (equal oper 'openrd) (and (equal (getcallname logrec) 'open) (equal (getcallflag logrec) 'rd))
    (if(equal oper 'openrw) (and (equal (getcallname logrec) 'open) (equal (getcallflag logrec) 'rw))
    (if(equal oper 'openwr) (and (equal (getcallname logrec) 'open) (equal (getcallflag logrec) 'wr))
    (if (equal oper 'opencr) (and (equal (getcallname logrec) 'open) (equal (getcallflag logrec) 'cr))
    (if (equal oper 'open) (equal (getcallname logrec) 'open)
    (if (equal oper 'unlink) (equal (getcallname logrec) 'unlink)
    (if (equal oper 'link) (equal (getcallname logrec) 'link)
    (if (equal oper 'chmod) (equal (getcallname logrec) 'chmod)
    (if (equal oper 'fchmod) (equal (getcallname logrec) 'fchmod)
    (if (equal oper 'chown) (equal (getcallname logrec) 'chown)
    (if (equal oper 'fchown) (equal (getcallname logrec) 'fchown)
    (if (equal oper 'fork) (equal (getcallname logrec) 'fork)
    (if (equal oper 'vfork) (equal (getcallname logrec) 'vfork)
    (if (equal oper 'read) (equal (getcallname logrec) 'read)
    (if (equal oper 'write) (equal (getcallname logrec) 'write)
    (if (equal oper 'socket) (equal (getcallname logrec) 'socket)
    (if (equal oper 'connect) (equal (getcallname logrec) 'connect)
    (if (equal oper 'exit) (equal (getcallname logrec) 'exit)
    (if (equal oper 'setuid) (equal (getcallname logrec) 'setuid)
    (if (equal oper 'execvt) (equal (getcallname logrec) 'execvt)
    (if (equal oper 'create) (equal (getcallname logrec) 'create)
    (if (equal oper 'rename) (equal (getcallname logrec) 'rename)
    (if (equal oper 'setresuid) (equal (getcallname logrec) 'setresuid) nil))))))))))))))))))))
    ))
  )
)
;(operate 'opencr '((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open cr)))
    (defun filter (procname log)
        (cond ((endp log) nil)
	    ((equal procname (getprocname (car log))) (cons (car log) (filter procname (cdr log)))
	    )
	    (t (filter procname (cdr log))
	    )
	)
    )


    (defun spec-create(filecreated logrec)
        (if (and (or(operate 'create logrec)(operate 'opencr logrec)) (not(member (getfilename (logrec-fobj logrec)) filecreated)) )
	    (append (list (getfilename (logrec-fobj logrec))) filecreated)
	    filecreated
	)
    )


(defun WorldReadable(fileobj)
(equal (rwx-obj-r (pmode-obj-amode (file-obj-pmode fileobj))) '1)
)
;(WorldReadable '(/home/tsong/file 23 2 ((1 1 0)(1 0 0)(1 0 0)) 534))


(defun CreatedByProcTree(fileobj filelist)
(member(getfilename fileobj) filelist)
)
;(CreatedByProcTree '("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(1 0 0)) 534) '("/home/tsong/file" (/ etc passwd)))

(defun CreatedByProc(fileobj filelist)
(member (getfilename fileobj) filelist)
)
;(CreatedByProc '("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(1 0 0)) 534) '("/home/tsong/file" (/ etc passwd)))

(defun PathEqual(fileobj path)
(path-equal (getfilename fileobj) path)
)
;(pathequal '("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(1 0 0)) 534) '"/home/tsong/file")

(defun InDir(fileobj path)
(inpath(getfilename fileobj) path)

)
; ) ; extra paren removed by Matt K.
;(InDir '("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(1 0 0)) 534) '"/home/tsong")

(defun IsFile(fileobj target)
(path-equal (getfilename fileobj) target)
)
;(IsFile '("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(1 0 0)) 534) '"/home/tsong/file")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;how to describe regfiel, socket and pipe
(defun IsRegFile(fileobj)
  (equal (getreg fileobj) 1)
)

(defun IsSocket(fileobj)
  (> (getsocket fileobj) 0)
)

(defun GetPort(fileobj)
  (getsocket fileobj)
)

(defun IsPipe(fileobj)
  (equal (getpipe fileobj) 1)
)

(defun CreateBySelf(fileobj uid)
(equal (getfileouid fileobj) uid )
)

(defun InDirList(fileobj dirlist)
    (if (endp dirlist)
        nil
	(or (InDir fileobj (car dirlist)) (InDirList fileobj (cdr dirlist)))
    )
)
(defun InPathList(filename dirlist)
    (if (endp dirlist)
        nil
	(or (InPath filename (car dirlist)) (InPathList filename (cdr dirlist)))
    )
)
(defthm InDirList2InPathList
    (implies (and (InDirList fileobj dirlist)(file-obj-p fileobj))
        (InPathList (file-obj-name fileobj) dirlist)
    )
)
(defun OwnerofFile(logrec)
  (equal (getfileouid (logrec-fobj logrec)) (getprocruid logrec))
)

(defun PathMatch(fileobj path)
    (InDir fileobj path)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;         two spec samples
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(spec_ftpd '(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1))))((0 root "/") (23 tsong "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print"))) '(((ftpd 23 3405 0 0) ("/home/tsong/file" 23 2 ((1 1 0) (1 0 0) (1 0 0)(0 0 0 0))23021) (open r))) nil)
;(spec_ftpd '(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1))))((0 root "/") (23 tsong "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print"))) nil nil)
;(logp '(((ftpd 23 3405 0 0) ("/home/tsong/file" 23 2 ((1 1 0) (1 0 0) (1 0 0)(0 0 0 0))23021) (open r))))
;(sys-p '(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1)(0 0 0 0)) 1003))((0 root "/") (23 tsong "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print"))))
;
;(defun spec_lpr_rec (sys logrec filelist)
;    (if (or
;        (and (consp sys)(consp logrec)(consp filelist) (operate 'openrd logrec) (WorldReadable (logrec-fobj logrec)))
;	(and (operate 'openrd logrec) (OwnerofFile logrec))
;	(and (operate 'openrd logrec) (CreatedByProc (logrec-fobj logrec) filelist))
;	(and (operate 'openrd logrec) (IsFile (logrec-fobj logrec) '(/ etc spwd.db)))
;	(and (operate 'openwr logrec) (CreatedByProc (logrec-fobj logrec) filelist))
;	(and (operate 'openwr logrec) (pathmatch (logrec-fobj logrec) (path-append (getprinterspool sys) '(* seq))))
;	(and (operate 'opencr logrec) (InDirList (logrec-fobj logrec) (getprinterdir sys) ))
;	(and (operate 'unlink logrec) (CreatedByProc (logrec-fobj logrec) filelist))
;	(and (operate 'chmod logrec) (CreatedByProc (logrec-fobj logrec) filelist))
;	(and (operate 'fchmod logrec) (CreatedByProc (logrec-fobj logrec) filelist))
;	(and (operate 'chown logrec) (CreatedByProc (logrec-fobj logrec) filelist))
;	(operate 'fork logrec)
;	(operate 'vfork logrec)
;	)
;	t
;	nil
 ;   )
;)

;(defun spec_lpr (sys  log filelist)
;    (if (endp log)
;      t
;      (and  ( spec_lpr_rec sys  (car log) filelist)(spec_lpr sys (cdr log)(spec-create filelist (car log))))
;    )
;)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;                                 new version therom
;
;log: ((prog ruid pid euid egid) (name ouid ogid pmode inodeid)(syscall flags) (newowner, newmode, newpath, chpid))......
;(((ftpd 23 3405 0 0) (/home/tsong/file 23 2 ((1 1 0) (1 0 0) (1 0 0)(0 0 0 0))23021) (open r))))
;system:(((pname pdir)...)((callname)..)((dir ouid ogid pmode inodeid)...)((uid uname gid homedir)...)((envname envvalue)...))
;(((ftp "/bin/ftp")(lpr "/bin/lpr"))((create)(open)(read)(write)(chmod)(chown))(("/bin/ftp" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1001)("/bin/lpr" 0 0 ((1 1 1)(0 0 1)(0 0 1)) 1002)("/home/tsong/" 23 2 ((1 1 1)(0 0 1)(0 0 1))))((0 root "/") (23 tsong "/home/tsong")) ((printpool "/temp/print")(printdir "/temp/print")))
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun access-logrec (logrec)
  (if (and (not (equal (getprocruid logrec) 0))
	   (equal '(/ etc passwd) (getfilename (logrec-fobj logrec)) )
	   (or (equal 'open (getcallname logrec))
	       (equal 'chmod (getcallname logrec))
	       (equal 'chown (getcallname logrec))
	       (equal 'rename (getcallname logrec))
	       (equal 'delete (getcallname logrec)) ))
      t
    nil
    )
  )

(defun access-passwd (log)
  (if (not (logp log)) nil
    (if (endp log) nil
      (or (access-logrec  (car log))
	  (access-passwd  (cdr log) ))
      )
    )
)
(defun not-access-logrec (logrec)
  (if (or (equal (getprocruid logrec) 0)
	   (not(equal '(/ etc passwd) (getfilename (logrec-fobj logrec)) ))
	   (and (not (equal 'open (getcallname logrec)))
	       (not (equal 'chmod (getcallname logrec)))
	       (not (equal 'chown (getcallname logrec)))
	       (not (equal 'rename (getcallname logrec)))
	       (not (equal 'delete (getcallname logrec)) )))
      t
    nil
    )
  )

(defun not-access-passwd (log)
    (if (endp log) t
      (and (not-access-logrec  (car log))
	  (not-access-passwd  (cdr log) ))
      )
)

(defthm lemma-access-passwd
    (implies (and (logp log)(consp log))
    (equal (not-access-passwd log)(not (access-passwd log)))
    )
)
;(access-passwd2 '(((ftpd 23 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd))((ftpd 0 324 0 0) ((/ etc passwd) 0 0 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd)) ))
;(access-passwd3 '(((ftpd 23 324 0 0) ((/ etc passwd) 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd))))
;(filter 'ftpd '(((lpr 23 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd))((ftpd 0 324 0 0) ((/ etc passwd) 0 0 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd)) ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;                   assumptions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun checkhomedir-rec (userobj)
    (and (not (inpath '(/ etc passwd) (user-obj-homedir userobj)))(consp (user-obj-homedir userobj)))
)

(defun checkhomedir (userlist)
   (if (endp userlist) t
   	(and
	(checkhomedir-rec (car userlist))
	(checkhomedir(cdr userlist)) )
   )


)

(defun homedirsafe (sys)
    (checkhomedir (getuserlist sys))
)

;(checkhomedir '((23 tsong 2 "/home/tsong")(24 aaa 2 "/etc")))

(defun passwdsaferec (rec)
    (not(and (or (WorldReadable(logrec-fobj rec)) (not (equal (getfileouid (logrec-fobj rec)) 0)))(PathEqual (logrec-fobj rec)'(/ etc passwd)))
    )
)

(defun passwdsafe (log)
    (if (endp log) t
     (and (passwdsaferec (car log)) (passwdsafe(cdr log)))
    )
)

;(passwdsafe '(((ftpd 0 3405 0 0) ((/ etc passwd) 0 2 ((1 1 0) (1 0 0) (0 0 0)(0 0 0 0))23021) (open r))))

(defun userreccheck (userrec uid)
    (equal (user-obj-uid userrec) uid)
)

(defun userlistcheck (userlist uid)
    (if (endp userlist) nil
    	(or (userreccheck (car userlist) uid)
      	(userlistcheck (cdr userlist) uid))
    )
)

(defun validuserrec (sys rec)
  (userlistcheck (getuserlist sys) (getprocruid rec))
  )

(defun validuser (sys log)
    (if (endp log) t
	 (and (validuserrec sys (car log))
			 (validuser sys (cdr log)))
    )
  )
(defun validenv(sys envname)
    (and (not (inpath '(/ etc passwd) (getenv (getenvlist sys ) envname)))(consp (getenv (getenvlist sys ) envname)))
)
(defun validprinterdir(sys)
    (and (not (inpathlist '(/ etc passwd) (getenv (getenvlist sys ) 'printerdir)))(consp (getenv (getenvlist sys ) 'printerdir)))
)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;              theorem with one spec
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defun spec_ftpd_rec (sys logrec filelist)
    (if
        (or
        (and (operate 'openrd logrec) (WorldReadable (logrec-fobj logrec)))
	(and (operate 'openrd logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'openrd logrec) (OwnerofFile logrec))
	(and (operate 'openwr logrec) (PathEqual (logrec-fobj logrec) '"/var/log/wtmp"))
	(and (operate 'openwr logrec) (PathEqual (logrec-fobj logrec) '"/var/log/xferlog"))
	(and (operate 'openwr logrec) (PathEqual (logrec-fobj logrec) '"/var/log/ftp.pids-all"))
	(and (operate 'openrw logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'open logrec) (PathEqual (logrec-fobj logrec) '"/dev/dull"))
	(and (operate 'unlink logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'read logrec) (and (IsSocket (logrec-fobj logrec))(equal (getport (logrec-fobj logrec)) 21)))
	(and (operate 'write logrec) (and (IsSocket (logrec-fobj logrec))(equal (getport(logrec-fobj logrec)) 21)))
	(and (operate 'create logrec) (InDir (logrec-fobj logrec) (homedir (sys-userlist sys) (getprocruid logrec))))
	(and (operate 'execve logrec) (or (PathEqual (logrec-fobj logrec) '"/bin/tar" ) (PathEqual (logrec-fobj logrec) '"/bin/compress" )(PathEqual (logrec-fobj logrec) '"/bin/ls" )(PathEqual (logrec-fobj logrec) '"/bin/gzip" )))
	)
	t
	nil
    )
)


(defun spec_ftpd (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_ftpd_rec sys  (car log) filelist)(spec_ftpd sys (cdr log)(spec-create filelist (car log))))
    )
)

( defthm lemma81
(implies (and (consp userlist1)(userlistp userlist1)(integerp uid)
 (userlistcheck userlist1 uid)
 (checkhomedir userlist1)
 )
 ( consp(homedir userlist1 uid ))
)
;:hints (("Subgoal 1''" :induct (homedir (sys-userlist sys)uid )))
)

( defthm lemma82
(implies (and (consp userlist1)(userlistp userlist1)(integerp uid)
 (userlistcheck userlist1 uid)
 (checkhomedir userlist1)
 )
 (not (InPath '(/ etc passwd)(homedir userlist1 uid )) )
)
;:hints (("Subgoal 1''" :induct (homedir (sys-userlist sys)uid )))
)

(defthm lemma83
   (implies (and (consp sys)(sys-p sys))
       (and (consp (sys-userlist sys))(userlistp (sys-userlist sys)))
   )
)
(defthm lemma84
   (implies (homedirsafe sys)
       (checkhomedir (sys-userlist sys))
   )
)

( defthm lemma7
(implies (and (consp sys)(sys-p sys)(integerp uid)
 (userlistcheck (sys-userlist sys) uid)
 (homedirsafe sys)

 )
 (not (InPath '(/ etc passwd) (homedir (sys-userlist sys)uid )) )
)
;:hints (("Goal'" :do-not-induct (homedir (sys-userlist sys)uid )         :use lemma82   ))
)
( defthm lemma71
(implies
 (and
 (consp sys)
 (sys-p sys)
 (integerp uid)
 (userlistcheck
 (sys-userlist sys) uid)
 (homedirsafe sys)
 (InPath filename (homedir (sys-userlist sys)uid ))
 )
 (not (equal '(/ etc passwd) filename) )
)
)

( defthm lemma72
(implies
 (and
 (consp sys)
 (sys-p sys)
 (logrec-p logrec)
 (integerp uid)
 (userlistcheck
 (sys-userlist sys) uid)
 (homedirsafe sys)
 (InDir (logrec-fobj logrec) (homedir (sys-userlist sys)uid ))
 )
 (not (equal '(/ etc passwd) (file-obj-name (logrec-fobj logrec))) )
)
)
( defthm lemma73
(implies
 (and
 (consp sys)
 (sys-p sys)
 (logp log)
 (integerp uid)
 (userlistcheck
 (sys-userlist sys) uid)
 (homedirsafe sys)
 (InDir (logrec-fobj (car log)) (homedir (sys-userlist sys)uid ))
 )
 (not (equal '(/ etc passwd) (file-obj-name (logrec-fobj (car log)))) )
)
)
( defthm lemma74
(implies
 (and
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (logp log)
 (integerp uid)
 (userlistcheck
 (sys-userlist sys) uid)
 (homedirsafe sys)
 (InDir (logrec-fobj (car log)) (homedir (sys-userlist sys)uid ))
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
)
( defthm lemma75
(implies
 (and
 (sys-p sys)
 (logp log)
 (validuserrec sys (car log))
 )
 (userlistcheck (sys-userlist sys) (proc-obj-ruid(logrec-pobj(car log))))
)
)

( defthm lemma752
(implies
 (and
 (sys-p sys)
 (logp log)
 (consp log)
 (validuser sys log)
 )
 (userlistcheck (sys-userlist sys) (proc-obj-ruid(logrec-pobj(car log))))
)
)

( defthm lemma762
(implies
 (and
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (logp log)
 (integerp uid)
 (userlistcheck  (sys-userlist sys) uid)
 (homedirsafe sys)
 (InDir (logrec-fobj (car log)) (homedir (sys-userlist sys)uid ))
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
)


( defthm lemma763
(implies
 (and
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (logp log)
 (integerp (proc-obj-ruid(logrec-pobj(car log))))
 (userlistcheck  (sys-userlist sys) (proc-obj-ruid(logrec-pobj(car log))))
 (homedirsafe sys)
 (InDir (logrec-fobj (car log)) (homedir (sys-userlist sys)(proc-obj-ruid(logrec-pobj(car log))) ))
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
;:hints (("Goal" :use ((:instance lemma762 (id (proc-obj-ruid(logrec-pobj(car log))))))))
)

(defthm lemm764
    (implies
    (and
        (consp log)
        (logp log)
    )
    (integerp (proc-obj-ruid(logrec-pobj(car log))))
    )
)
(defthm lemm765
    (implies
    (and
    (consp log)
    (validuser sys log)
    )
    (userlistcheck  (sys-userlist sys) (proc-obj-ruid(logrec-pobj(car log))))
    )
)


( defthm lemma77
(implies
 (and
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
  (logp log)
  (validuser sys log)
 (homedirsafe sys)
 (InDir (logrec-fobj (car log)) (homedir (sys-userlist sys) (proc-obj-ruid(logrec-pobj(car log))) ))
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
)


( defthm lemma79
(implies
 (and
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (logp log)
 (validuser sys log)
 (homedirsafe sys)
 (spec_ftpd_rec sys (car log) created)
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
;:hints (("Goal" :uses lemma78 :uses lemma77))
)

(defthm passwd-ftp1-lemma
  (implies
   (not (member '(/ etc passwd) created))
   (implies
	(and
	(consp log)
	(consp sys)
	(logp log)
	(consp created)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not(access-passwd log))
   )
  )
)

(defthm passwd-ftp2-lemma
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp log)
	(consp sys)
	(logp log)
	(consp created)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not (access-passwd log) )
   )
  ;:hints (("Goal" :use (passwd-ftp1) ))
)
(defthm passwd-ftp2
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp log)
	(consp sys)
	(logp log)
	(consp created)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not-access-passwd log)
   )
  :hints (("Goal" :use (passwd-ftp2-lemma) ))
)
(defthm passwd-ftp-lemma
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp log)
	(consp sys)
	(logp log)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not(access-passwd log))
   )
 :hints (("Goal" :use (passwd-ftp2-lemma) ))
)
(defthm passwd-ftp
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp log)
	(consp sys)
	(logp log)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not-access-passwd log)
   )
 :hints (("Goal" :use (passwd-ftp-lemma) ))
)
(defthm passwd-ftp3-lemma
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp sys)
	(logp log)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not (access-passwd log) )
   )
 :hints (("Goal" :use (passwd-ftp-lemma) ))
)
(defthm passwd-ftp3
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp sys)
	(logp log)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validuser sys log)
	(spec_ftpd sys log created))
        (not-access-passwd log)
   )
 :hints (("Goal" :use (lemma-access-passwd passwd-ftp3-lemma) ))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun spec_lpr_rec (sys logrec filelist)
    (if (or
        (and (consp sys)(consp logrec)(consp filelist) (operate 'openrd logrec) (WorldReadable (logrec-fobj logrec)))
	(and (operate 'openrd logrec) (OwnerofFile logrec))
	(and (operate 'openrd logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'openrd logrec) (IsFile (logrec-fobj logrec) '(/ etc spwd.db)))
	(and (operate 'openwr logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (consp sys) (consp logrec)(consp filelist) (operate 'openwr logrec) (pathmatch (logrec-fobj logrec) (path-append (getprinterspool sys) '(* seq))))
;	(and (consp sys)(consp logrec)(consp filelist)(operate 'opencr logrec) (InDirList (logrec-fobj logrec) (getprinterdir sys) ))
	(and (operate 'unlink logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (logrec-fobj logrec) filelist))
	(operate 'fork logrec)
	(operate 'vfork logrec)
	)
	t
	nil
    )
)

(defun spec_lpr (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_lpr_rec sys  (car log) filelist)(spec_lpr sys (cdr log)(spec-create filelist (car log))))
    )
)


( defthm lemma2001
(implies (and
 (consp sys)
 (sys-p sys)
 (validenv sys 'printerspool)
 )
 ( consp (getprinterspool sys))
)
)
( defthm lemma2002
(implies (and
 (consp sys)
 (sys-p sys)
 (validenv sys 'printerspool)
 )
 ( not(inpath '(/ etc passwd) (getprinterspool sys)))
)
)

(defthm lemma2003
    (implies (not (inpath aaa bbb))
       (not (inpath aaa (path-append bbb ccc)))
    )
)
(defthm lemma2004
    (implies (not (inpath aaa bbb))
       (not (inpath aaa (path-append bbb ccc)))
    )
)
(in-theory (disable path-append getprinterspool))
(defthm lemma2005
    (implies  (not (inpath '(/ etc passwd) (getprinterspool sys)))
    (not (inpath '(/ etc passwd) (path-append (getprinterspool sys) '(* seq))))
    )
   ; :hints (("Goal" :use (:instance lemma2004(aaa '(/ etc passwd))( bbb (getprinterspool sys))( ccc '(* seq)))))
)
(defthm lemma2006
(implies (and (consp sys)(sys-p sys) (validenv sys 'printerspool))
    (not(inpath '(/ etc passwd) (path-append (getprinterspool sys) '(* seq))))
    )
    ;:hints (("Goal" :use (lemma2002 lemma2005) ))
)
(defthm lemma2007
    (implies (and (consp sys)(sys-p sys)(logrec-p logrec) (validenv sys 'printerspool) (pathmatch (logrec-fobj logrec) (path-append (getprinterspool sys) '(* seq))))
    (not (equal '(/ etc passwd)(file-obj-name(logrec-fobj logrec))))
    )
    ;:hints (("Goal" :use (lemma2002 lemma2005) ))
)
(defthm lemma2008
    (implies (and (consp sys)(sys-p sys)(logrec-p logrec) (validenv sys 'printerspool) (pathmatch (logrec-fobj logrec) (path-append (getprinterspool sys) '(* seq))))
    (not (access-logrec logrec))
    )
    ;:hints (("Goal" :use (lemma2002 lemma2005) ))
)



( defthm lemma201
(implies (and
 (consp sys)
 (sys-p sys)
 (validprinterdir sys)
 )
 ( consp (getprinterdir sys))
)
)
( defthm lemma202
(implies (and
 (consp sys)
 (sys-p sys)
 (validprinterdir sys)
 )
 ( not(InPathList '(/ etc passwd) (getprinterdir sys)))
)
)

( defthm lemma203
(implies
 (and
 (logrec-p logrec)
 (consp logrec)
 )
(file-obj-p (logrec-fobj logrec))
)
)

( defthm lemma204
(implies
 (and
 (logrec-p logrec)
 (consp logrec)
 (consp sys)
 (sys-p sys)
 (InDirList (logrec-fobj logrec) (getprinterdir sys) )
 )
 (InPathList (file-obj-name(logrec-fobj logrec)) (getprinterdir sys))
)
;:hints (("Goal" :use ((:instance InDirList2InPathList(fileobj (logrec-fobj logrec))))))
)

( defthm lemma205
(implies
 (and
 (logrec-p logrec)
 (consp logrec)
 (consp sys)
 (sys-p sys)
 (InDirList (logrec-fobj logrec) (getprinterdir sys) )
 (validprinterdir sys)
 )
 (and ( not(InPathList '(/ etc passwd) (getprinterdir sys)))(InPathList (file-obj-name(logrec-fobj logrec)) (getprinterdir sys)))
; (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj logrec))) )
)
)
(defthm lemma206
    (implies
    (and ( not(InPathList '(/ etc passwd) (getprinterdir sys)))(InPathList (file-obj-name(logrec-fobj logrec)) (getprinterdir sys)))
    (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj logrec))) )
    )
)

( defthm lemma207
(implies
 (and
 (logrec-p logrec)
 (consp logrec)
 (consp sys)
 (sys-p sys)
 (InDirList (logrec-fobj logrec) (getprinterdir sys) )
 (validprinterdir sys)
 )
; (and ( not(InPathList '(/ etc passwd) (getprinterdir sys)))(InPathList (file-obj-name(logrec-fobj logrec)) (getprinterdir sys)))
 (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj logrec))) )
)
:hints (("Goal" :use (lemma205 lemma206)))
)
( defthm lemma208
(implies
 (and
 (logp log)
 (consp log)
 )
 (and
 (consp (car log))
 (logrec-p (car log))
 )
)
)

( defthm lemma209
(implies
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
; (and ( not(InPathList '(/ etc passwd) (getprinterdir sys)))(InPathList (file-obj-name(logrec-fobj logrec)) (getprinterdir sys)))
 (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj (car log)))) )
)
:hints (("Goal" :use lemma207))
)

( defthm lemma210
(implies
 (and
 (not (member '(/ etc passwd) created))
 (logp log)
 (consp log)
 (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj (car log)))) )
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
)

( defthm lemma211
(implies
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
 (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj (car log)))) )
)
:hints (("Goal" :use lemma209))
)


( defthm lemma212
(implies
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
  (and
 (not (member '(/ etc passwd) created))
 (logp log)
 (consp log)
 )
)
)

( defthm lemma213
(implies
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
  (and
 (not (member '(/ etc passwd) created))
 (logp log)
 (consp log)
 (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj (car log)))) )
 )
)
)

( defthm lemma214
(implies
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
 (not (member '(/ etc passwd) (spec-create created (car log))))
)
:hints (("Goal" :use (lemma213 lemma210)))
)

(defun aa(log sys created)
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
)
(defun bb(log created)
  (and
 (not (member '(/ etc passwd) created))
 (logp log)
 (consp log)
 (not (equal '(/ etc passwd) (file-obj-name(logrec-fobj (car log)))) )
 )
)
(defun cc(log created)
(not (member '(/ etc passwd) (spec-create created (car log))))
)

(defthm lemma2152
    (implies (aa log sys created)
    (bb log created)
    )
:hints (("Goal" :use lemma213))
)
(defthm lemma216
    (implies
    (bb log created)
    (cc log created)
    )
:hints (("Goal" :use lemma210))
)
(defthm lemma217
    (implies (aa log sys created)
    (cc log created)
    )
:hints (("Goal" :use lemma2152))
)
( defthm lemma218
(implies
 (and
 (logp log)
 (consp log)
 (consp sys)
 (sys-p sys)
 (not (member '(/ etc passwd) created))
 (InDirList (logrec-fobj (car log)) (getprinterdir sys) )
 (validprinterdir sys)
 )
(not (member '(/ etc passwd) (spec-create created (car log))))

)
:hints (("Goal" :use lemma217))
)



(defthm passwd-lpr
   (implies
	(and
	(not (member '(/ etc passwd) created))
	(consp log)
	(consp sys)
	(logp log)
	(consp created)
	(sys-p sys)
	(passwdsafe log)
	(homedirsafe sys)
	(validenv sys 'printerspool)
	(validuser sys log)
	(spec_lpr sys log created))
        (not (access-passwd log) )
   )
 ;:hints (("Goal" :use (lemma2008) ))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;            spec functions of SHIM
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun vaildaccess (sys logrec )
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (OwnerofFile logrec))
       )
       )
       t
       nil
)
)
(defun spec_atcst_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (CreatedByProcTree (getfile logrec) filelist))
	(and (operate 'openwr logrec) (CreatedByProcTree (getfile logrec) filelist))
	(and (operate 'openwr logrec) (IsFile (getfile logrec) '"/var/spool/at/.SEQ"))
	(and (operate 'opencr logrec) (InDir (getfile logrec) '"/var/spool/at"))
	(and (operate 'unlink logrec) (CreatedByProcTree (getfile logrec) filelist))
	(and (operate 'unlink logrec) (InDir (getfile logrec) '"/var/spool/at/spool"))
	(and (operate 'chmod logrec) (CreatedByProcTree (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProcTree (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProcTree (getfile logrec) filelist))
	(and (operate 'fchown logrec) (CreatedByProcTree (getfile logrec) filelist))
	(operate 'fork logrec)
	(operate 'vfork logrec)
	))
	t
	nil
    )
)
;(spec_atcst_rec '( a b c) '((cst 0 324 0 0) ("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(1 0 0)(0 0 0 0)) 2345) (open rd)) nil)
;(spec_atcst_rec '( a b c) '((cst 0 324 0 0) ("/home/tsong/file" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd)) '("/home/tsong/file"))
;(spec_atcst_rec '( a b c) '((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open cr)) nil)
(defun spec_atcst (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_atcst_rec sys  (car log) filelist)(spec_atcst sys (cdr log)(spec-create filelist (car log))))
    )
)
;(spec_atcst '(a b c) '(((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open cr)) ) nil)
;(spec_atcst '(a b c) '(((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd)) ) nil)
;(spec_atcst '(a b c) '(((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd)) ) '("/var/spool/at/myfile"))
;(spec-create nil '((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open cr)))
;(spec_atcst '(a b c) '(((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open cr)) ((cst 0 324 0 0) ("/var/spool/at/myfile" 23 2 ((1 1 0)(1 0 0)(0 0 0)(0 0 0 0)) 2345) (open rd))) nil)
;create "/var/spool/at/myfile" then read it
(defun spec_chage_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/shadow"))
	(and (operate 'openrw logrec) (InDir (getfile logrec) '"/var/run/utmp"))
	(and (operate 'openrw logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchown logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'read logrec)
	(operate 'write logrec)
	(operate 'socket logrec)
	(operate 'connect logrec)
	(operate 'exit logrec)
	))
	t
	nil
    )
)
(defun spec_chage (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_chage_rec sys  (car log) filelist)(spec_chage sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_chsh_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/shadow"))
	(and (operate 'openrw logrec) (InDir (getfile logrec) '"/var/run/utmp"))
	(and (operate 'openrw logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchown logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'read logrec)
	(operate 'write logrec)
	(operate 'socket logrec)
	(operate 'connect logrec)
	(operate 'exit logrec)
	))
	t
	nil
    )
)
(defun spec_chsh (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_chsh_rec sys  (car log) filelist)(spec_chsh sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_chfn_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/shadow"))
	(and (operate 'openrw logrec) (InDir (getfile logrec) '"/var/run/utmp"))
	(and (operate 'openrw logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchown logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'read logrec)
	(operate 'write logrec)
	(operate 'socket logrec)
	(operate 'connect logrec)
	(operate 'exit logrec)
	))
	t
	nil
    )
)

(defun spec_chfn (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_chfn_rec sys  (car log) filelist)(spec_chfn sys (cdr log)(spec-create filelist (car log))))
    )
)


(defun spec_crontab_rec (sys logrec filelist)
    (let ((cronspooldir '"/var/cron/spool/")( username '"tsong"))
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openrw logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openrw logrec) (InDir (getfile logrec) (string-append cronspooldir username)))
	(and (operate 'opencr logrec) (InDir (getfile logrec) (string-append cronspooldir username)))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchown logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'fork logrec)
	(operate 'vfork logrec)
	))
	t
	nil
    )
    )

)
(defun spec_crontab (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_crontab_rec sys  (car log) filelist)(spec_crontab sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_dumpcst_rec (sys logrec)

    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(operate 'connect logrec)
	(operate 'fork logrec)
	(operate 'vfork logrec)
	))
	t
	nil
    )


)
(defun spec_dumpcst (sys  log )
    (if (endp log)
      t
      (and  ( spec_dumpcst_rec sys  (car log) )(spec_dumpcst sys (cdr log) ))
    )
)
;----------------------------------------------- later
;(defun spec_fingerd (sys  log)
;	     (and  ( spec_fingerd_rec sys  car log)(spec_fingerd sys (cdr log)))
;)
;(defun spec_stateftpd (sys  log)
;
;	     (and  ( spec_stateftpd_rec sys  car log)(spec_stateftpd sys (cdr log)))
;)

;--------------------------------------------------
(defun spec_gpasswd_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/gshadow"))
	(and (operate 'openrw logrec) (PathEqual (getfile logrec) '"/var/run/utmp"))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'rename logrec) (IsFile (getfile logrec) '"/etc/gshadow"))
	(and (operate 'rename logrec) (IsFile (getfile logrec) '"/etc/gpasswd"))

	))
	t
	nil
    )
)
(defun spec_gpasswd (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_gpasswd_rec sys  (car log) filelist)(spec_gpasswd sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_lpd_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (OwnerofFile logrec))
	(and (operate 'openrd logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/spwd.db"))
	(and (operate 'openwr logrec) (IsFile (getfile logrec) '"/var/spool/lpd/*/.seq"))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openrw logrec) (InDir (getfile logrec) '"/dev/null"))
	(and (operate 'open logrec) (InDirList (getfile logrec) (getprinterdir sys)))
	(and (operate 'unlink logrec) (InDirList (getfile logrec) (getprinterdir sys)))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (PathEqual (getfile logrec) '"/dev/printer"))
	(and (operate 'fchown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'rename logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'rename logrec) (InDirList (getfile logrec) (getprinterdir sys)))
	(and (operate 'execve logrec) (InDir (getfile logrec) '"/var/spool/lpd"))
	(and (operate 'execve logrec) (InDir (getfile logrec) '"/usr/bin"))
	(and (operate 'execve logrec) (InDir (getfile logrec) '"/bin"))
	(and (operate 'execve logrec) (InDir (getfile logrec) '"/usr/lib/rhs"))
	(operate 'fork logrec)
	(operate 'vfork logrec)
	))
	t
	nil
    )
)
;????????????????
(defun spec_lpd (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_lpd_rec sys  (car log) filelist)(spec_lpd sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_lpq_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (OwnerofFile logrec))
	(and (operate 'openrd logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/spwd.db"))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openwr logrec) (IsFile (getfile logrec) '"/var/spool/output/lpd/.seq"))
	(operate 'opencr logrec)
	(operate 'create logrec)
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'fork logrec)
	(operate 'vfork logrec)
	))
	t
	nil
    )
)
(defun spec_lpq (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_lpq_rec sys  (car log) filelist)(spec_lpq sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_lprm_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (OwnerofFile logrec))
	(and (operate 'openrd logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/spwd.db"))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openwr logrec) (IsFile (getfile logrec) '"/var/spool/output/lpd/.seq"))
	(operate 'opencr logrec)
	(operate 'create logrec)
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'fchmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'fork logrec)
	(operate 'vfork logrec)
	))
	t
	nil
    )
)
(defun spec_lprm (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_lprm_rec sys  (car log) filelist)(spec_lprm sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_mountcst_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'openwr logrec) (PathEqual (getfile logrec) '"/etc/mtab"))
	(and (operate 'opencr logrec) (PathMatch (getfile logrec) '"/etc/mtab"))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	))
	t
	nil
    )
)
(defun spec_mountcst (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_mountcst_rec sys  (car log) filelist)(spec_mountcst sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_netutil_rec (sys logrec )
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(operate 'connect logrec)
	(operate 'setuid logrec)
	(operate 'socket logrec)
	))
	t
	nil
    )
)
(defun spec_netutil (sys  log )
    (if (endp log)
      t
      (and  ( spec_netutil_rec sys  (car log) )(spec_netutil sys (cdr log)))
    )
)
(defun spec_passwd_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrd logrec) (IsFile (getfile logrec) '"/etc/gshadow"))
	(and (operate 'openrw logrec) (PathEqual (getfile logrec) '"/var/run/utmp"))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chown logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'rename logrec) (IsFile (getfile logrec) '"/etc/gshadow"))
	(and (operate 'rename logrec) (IsFile (getfile logrec) '"/etc/gpasswd"))

	))
	t
	nil
    )
)
(defun spec_passwd (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_passwd_rec sys  (car log) filelist)(spec_passwd sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_ping_rec (sys logrec )
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(operate 'connect logrec)
	(operate 'setuid logrec)
	(operate 'socket logrec)
	))
	t
	nil
    )
)
(defun spec_ping (sys  log )
    (if (endp log)
      t
      (and  ( spec_ping_rec sys  (car log) )(spec_ping sys (cdr log)))
    )
)
(defun spec_rcmd_rec (sys logrec filelist)
    (if (and (sys-p sys)
        (listp filelist)
	(or
        (vaildaccess sys logrec) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	(operate 'bind logrec)
	(operate 'setuid logrec)
	(operate 'socket logrec)
	))
	t
	nil
    )
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;???????????????????????????????
(defun spec_rcmd (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_rcmd_rec sys  (car log) filelist)(spec_rcmd sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_restore_rec (sys logrec filelist)
    (if (and (sys-p sys)
        (listp filelist)
	(or
        (vaildaccess sys logrec) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	(operate 'fork logrec)
	(operate 'vfork logrec)
	(operate 'connect logrec)
	))
	t
	nil
    )
)
(defun spec_restore (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_restore_rec sys  (car log) filelist)(spec_restore sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_rshacst_rec (sys logrec filelist)
    (if (and (sys-p sys)
        (listp filelist)
	(or
        (and (operate 'execve logrec)(IsFile (getfile logrec) '"/usr/bin/rlogin"))
	(vaildaccess sys logrec) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	(operate 'fork logrec)
	(operate 'setuid logrec)
	(operate 'connect logrec)
	))
	t
	nil
    )
)
(defun spec_rshacst (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_rshacst_rec sys  (car log) filelist)(spec_rshacst sys (cdr log)(spec-create filelist (car log))))
    )
)
;;;what's the use of this spec?
(defun spec_stdunix_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))

	))
	t
	nil
    )
)
(defun spec_stdunix (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_stdunix_rec sys  (car log) filelist)(spec_stdunix sys (cdr log)(spec-create filelist (car log))))
    )
)
(defun spec_syslogd_rec (sys logrec filelist)
    (if (and (sys-p sys)(or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(and (operate 'openrw logrec) (InDir (getfile logrec) '"/var/log"))
	(and (operate 'open logrec) (PathEqual (getfile logrec) '"/var/run/syslogd.pid"))
	(and (operate 'openwr logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'chmod logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'unlink logrec) (CreatedByProc (getfile logrec) filelist))
	(and (operate 'link logrec) (CreatedByProc (getfile logrec) filelist))
	(operate 'connect logrec)
	(operate 'socket logrec)
	))
	t
	nil
    )
)
(defun spec_syslogd (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_syslogd_rec sys  (car log) filelist)(spec_syslogd sys (cdr log)(spec-create filelist (car log))))
    )
)

(defun spec_traceroute_rec (sys logrec filelist)
    (if (and (sys-p sys)(listp filelist) (or
        (and (operate 'openrd logrec) (WorldReadable (getfile logrec)))
	(operate 'connect logrec)
	(operate 'setuid logrec)
	(operate 'socket logrec)
	))
	t
	nil
    )
)
(defun spec_traceroute (sys  log filelist)
    (if (endp log)
      t
      (and  ( spec_traceroute_rec sys  (car log) filelist)(spec_traceroute sys (cdr log)(spec-create filelist (car log))))
    )
)
