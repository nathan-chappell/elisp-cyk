;;on branch track-matches

;;need CNF to make sure we don't get confused..

;;;Lifting functions

;;A production rule is of the form: (HEAD . (NT1 NT2)), such that the rule:
;; HEAD -> NT1 NT2 would be in the grammar

(defun lift-rules-p (production-rules decode-pair)
  "gets matches from all rules vs one pair"
  (let ((ret '()))
    (mapcar (lambda (rule)
	      (if (equal (cdr rule) decode-pair) (setq ret (cons (car rule) ret))))
	    production-rules)
    ret))

(defun cartesian-product (list-a list-b)
  (let ((ret '()))
    (mapcar (lambda (a)
	      (mapcar (lambda (b) (setq ret (cons (cons a b) ret)))
		      list-b))
	    list-a)
    ret))

(defun lift-rules-x (production-rules decode-product)
  "gets matches from all rules vs current cartesian product"
  (let ((ret '()))
    (mapcar (lambda (decode-pair)
	      (let ((lift (lift-rules-p production-rules decode-pair)))
		(if lift
		    (setq ret (append lift ret)))))
	    decode-product)
    (delete-dups ret)))

;;CYK matrix is matrix of cells.  Cell i,j represents which Non-Terminals produce
;;the string of non-terminals nt_i, nt_i+1, ..., nt_j.  Dynamic-programming
;;shall be the recursive technique to calculate nt_1,n.

;;note: cell i,j is located in the matrix at (n-1 - i, j), the word is w_1.w_2.w_3. ... .w_n

(defun cell-index (i j n)
  (let ((d (- j i)))
    (cons (- (- n d) 1) (- (- j d) 1))))

(defun get-cell (M i j)
  (let ((i- (car (cell-index i j (length M))))
	(j- (cdr (cell-index i j (length M)))))
    (aref (aref M i-) j-)))

(defun set-cell (M i j what)
  (let ((i- (car (cell-index i j (length M))))
	(j- (cdr (cell-index i j (length M)))))
    (aset (aref M i-) j- what)))

;;gets the union of cartesian products of:
;;(i,i)x(i+1,j) + (i,i+1)x(i+2,j) + ... + (i,j-1)x(j,j)

;;;Note, the recursive pattern for dynamically filling up the CYK matrix is:
;;
;;get-prod-bases -> calc-cell -> get-partition-product -> get-prod-bases -> ...
;;
;;The recursion bottoms out at get-prod-bases, when it reaches the cells
;;that have been filled in from "lifting" the $word to non-terminals (and
;;later on, cells which have already been calculated).
;;

(defun get-partition-product (rules M i j)
  (let ((k i)
	(prod))
    (while (< k j)
      (setq prod (append
		  (cartesian-product
		   (get-prod-bases rules M i k) (get-prod-bases rules M (+ 1 k) j))
		  prod))
      (setq k (+ 1 k)))
    prod))

(defun calc-cell (rules M i j)
  (lift-rules-x rules (get-partition-product rules M i j)))

(defun get-prod-bases (rules M i j)
  (if (not (get-cell M i j)) (set-cell M i j (calc-cell rules M i j)))
  (get-cell M i j))

(defun lift-terminal (terminal-rules char)
  (let ((ret '()))
    (mapcar (lambda (rule)
	      (message (concat "rule: "  " : " (number-to-string (cdr rule))))
	      (if (equal (cdr rule) char) (setq ret (cons (car rule) ret))))
	    terminal-rules)
    ret))

(defun lift-terminals (terminal-rules word)
  (let ((nts (make-vector (length word) nil))
	(k 0)
	(n (length word)))
    (while (< k n)
      (aset nts k (lift-terminal terminal-rules (aref word k)))
      (setq k (+ k 1)))
    nts))

(defun blank-cyk-matrix (n)
  (let ((i 0)
	(M (make-vector n nil)))
    (while (< i n)
      (aset M i (make-vector (+ i 1) nil))
      (setq i (+ 1 i)))
    M))

;;Grammar is data type: (cons terminal-rules production-rules)
(defun get-cyk-matrix (grammar word)
  (let ((terminal-rules (car grammar))
	(production-rules  (cdr grammar))
	(M (blank-cyk-matrix (length word))))
    (aset M (- (length word) 1) (lift-terminals terminal-rules word))
    (get-prod-bases production-rules M 1 (length word))
    M))



;;;Grammar tokenization
;;By the book according to the RFC (rfc 5234).

(defun alternative-regexp (alts)
  (let ((ret "\\("))
    (mapcar (lambda (alt) (setq ret (concat ret alt "\\|"))) alts)
    (aset ret (- (length ret) 1) #x29)
    ret))

;;my helper rules
(setq lower-case "[\x61-\x7a]")
(setq upper-case "[\x41-\x5a]")
(setq def-symbol (alternative-regexp (list "=" "=/")))
(defun num-opt-arg (NUM-TYPE)
  (concat (alternative-regexp
	   (list (concat "\\(-" NUM-TYPE "+\\)")
		 (concat "\\(\\." NUM-TYPE "+\\)+"))) "?"))

;;;Core rules
(setq ALPHA (alternative-regexp (list lower-case upper-case)))
(setq BIT "[01]")
(setq CHAR "[\x01-\x7F]")
(setq CR "\x0D")
(setq LF "\x0A")
;;(setq CRLF (concat CR LF)) ;;unsuitable for development in Unix
(setq CRLF (alternative-regexp (list (concat CR LF) LF)))
(setq CTL (alternative-regexp (list "[\x00-\x1f]" "\x7f")))
(setq DIGIT "[\x30-\x39]")
(setq DQUOTE "\"")
(setq HEXDIG (alternative-regexp (list DIGIT "[A-Fa-f]")))
(setq HTAB "\x09")
(setq OCTET "[\x00-\xFF]")
(setq SP "\x20")
(setq VCHAR "[\x21-\x7e]")
(setq WSP (alternative-regexp (list SP HTAB)))
(setq LWSP (concat (alternative-regexp (list WSP (concat CRLF WSP))) "*"))

;;;Terminal objects as defined by RFC 5234
;;

(setq rulename (concat ALPHA (alternative-regexp (list ALPHA DIGIT "-")) "*")) 
(setq abnf-comment (concat ";" (alternative-regexp (list WSP VCHAR)) "*" CRLF))

(setq c-nl (alternative-regexp (list abnf-comment CRLF)))
(setq c-wsp (alternative-regexp (list WSP (concat "\\(" c-nl WSP "\\)"))))
(setq defined-as (concat WSP "*" def-symbol WSP "*")) 
(setq repeat (alternative-regexp (list (concat DIGIT "+") (concat DIGIT "*\\*" DIGIT "*"))))
(setq char-val (concat DQUOTE (alternative-regexp (list "[\x20-\x21]"
							"[\x23-\x7e]")) "*" DQUOTE))
(setq bin-val (concat "b" BIT "+" (num-opt-arg BIT)))
(setq dec-val (concat "d" DIGIT "+" (num-opt-arg DIGIT)))
(setq hex-val (concat "x" HEXDIG "+" (num-opt-arg HEXDIG)))
(setq num-val (concat "%" (alternative-regexp (list bin-val dec-val hex-val))))
(setq prose-val (concat "<" (alternative-regexp (list "[\x20-\x3d]" "[\x3f-\x7e]")) "*>"))

;;;Token classes
;;luckily these are all mutually exclusive, so can be attacked blindly
;;

;;rulename
;;comment
;;CRLF
;;WSP
;;asterisk "*"
;;slash "/"
;;open-paren "("
;;close-paren ")"
;;open-bracket "["
;;close-bracket "]"
;;char-val
;;num-val
;;prose-val
;;defined-as

(defun testcond (n)
  (cond
   ((= n 1) "one")
   (t "otherwise")))

(defun lex-err (what where)
  (error (concat "expected " what " at: " (number-to-string where))))

(defun testn (n start end rules what)
  (if (and (not (eq n start)) (not (eq end (length rules)))) (lex-err what start)))

(defun lex-next (rules start)
  (let ((cur-char (aref rules start)))
    (cond
     ((eq cur-char #x28) (cons (cons 'Topen-paren "(") (+ 1 start)))
     ((eq cur-char #x29) (cons (cons 'Tclose-paren ")") (+ 1 start)))
     ((eq cur-char #x5b) (cons (cons 'Topen-brace"[") (+ 1 start)))
     ((eq cur-char #x5d) (cons (cons 'Tclose-brace"]") (+ 1 start)))
     ((eq cur-char #x2f) (cons (cons 'Tslash "/") (+ 1 start)))
     ((eq cur-char #x2a) (cons (cons 'Tasterisk "*") (+ 1 start)))
     ((eq cur-char #x3d) (let ((n (string-match def-symbol rules start))) ;;=
			   (testn n start (match-end 0) rules "defined-as")
			   (cons (cons 'Tdefined-as (match-string 0 rules)) (match-end 0))))
     ((eq cur-char #x25) (let ((n (string-match num-val rules start))) ;;%
			   (testn n start (match-end 0) rules "num-val")
			   (cons (cons 'Tnum-val (match-string 0 rules)) (match-end 0))))
     ((eq cur-char #x22) (let ((n (string-match char-val rules start))) ;;"
			   (testn n start (match-end 0) rules "char-val")
			   (cons (cons 'Tchar-val (match-string 0 rules)) (match-end 0))))
     ((eq cur-char #x3c) (let ((n (string-match prose-val rules start))) ;;<
			   (testn n start (match-end 0) rules "prose-val")
			   (cons (cons 'Tprose-val (match-string 0 rules)) (match-end 0))))
     ((eq cur-char #x3b) (let ((n (string-match abnf-comment rules start))) ;;;
			   (testn n start (match-end 0) rules "abnf-comment")
			   (cons (cons 'Tabnf-comment (match-string 0 rules)) (match-end 0))))
     ((or (eq cur-char #x20)
	  (eq cur-char #x09)) (let ((n (string-match WSP rules start))) ;;space
				(testn n start (match-end 0) rules "WSP")
				(cons (cons 'TWSP (match-string 0 rules)) (match-end 0))))
     ((or (eq cur-char #x0d)
	  (eq cur-char #x0a)) (let ((n (string-match CRLF rules start))) ;;CRLF
				(testn n start (match-end 0) rules "CRLF")
				(cons (cons 'TCRLF (match-string 0 rules)) (match-end 0))))
     ((and (>= cur-char #x30)
	   (<= cur-char #x39)) (let ((n (string-match (concat DIGIT "+") rules start))) ;;repetition
				 (testn n start (match-end 0) rules "DIGITS")
				 (cons (cons 'TDIGITS (match-string 0 rules)) (match-end 0))))
     (t (let ((n (string-match rulename rules start))) ;;rulename
	  (testn n start (match-end 0) rules "rulename")
	  (cons (cons 'Trulename (match-string 0 rules)) (match-end 0)))))))

;;;
(defun abnf-lex (rules)
  (let ((lex)
	(cur 0))
    (while (< cur (length rules))
      (let ((next (lex-next rules cur)))
	(setq lex (cons (car next) lex))
	(setq cur (cdr next))))
    (reverse lex)))

(defun parse-err (what where)
  (error (concat "expected " what " at: " (format "%s" where))))

(defun parse-rulename (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Trulename) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-defined-as (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Tdefined-as) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-WSP (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'TWSP) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-DIGITS (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'TDIGITS) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-asterisk (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Tasterisk) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-CRLF (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'TCRLF) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-abnf-comment (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Tabnf-comment) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-c-nl (tokens)
  (parse-alternatives (list 'parse-abnf-comment 'parse-CRLF) tokens))

(defun parse-c-wsp (tokens)
  (parse-alternatives (list
		       'parse-WSP
		       (lambda(x) (parse-concat (list 'parse-c-nl 'parse-WSP) x)))
		      tokens))

(defun parse-repeat-1 (tokens)
  (parse-concat-meta (list 'parse-DIGITS 'parse-asterisk) tokens))

(defun parse-repeat-2 (tokens)
  (parse-concat-meta (list 'parse-asterisk 'parse-DIGITS) tokens))

(defun parse-repeat-3 (tokens)
  (parse-concat-meta (list 'parse-DIGITS 'parse-asterisk 'parse-DIGITS) tokens))

(defun parse-repeat (tokens)
  (parse-alternatives-meta
   (list 'parse-repeat-3 'parse-repeat-2 'parse-repeat-1 'parse-DIGITS) tokens))

(defun parse-element (tokens)
  (parse-alternatives-meta
   (list 'parse-rulename 'parse-group 'parse-option
	 'parse-char-val 'parse-num-val 'parse-prose-val))) 

(defun parse-char-val (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Tchar-val) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-num-val (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Tnum-val) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-prose-val (tokens)
  (let ((tok (car (car tokens))))
    (if (equal tok 'Tprose-val) (cons (car tokens) (cdr tokens))
      (cons nil tokens))))

(defun parse-element (tokens)
  (parse-alternatives-meta (list 'parse-rulename 'parse-group 'parse-option
				 'parse-char-val 'parse-num-val 'parse-prose-val)))

;;;"meta-parsing"

(defun parse-repetition-meta (what min max tokens)
  (let ((i 0)
	(ret)
	(cur (cons t nil)))
    (while (and (car cur) (or (< i max) (= max -1)))
      (setq cur (funcall what tokens))
      (if (car cur)
	  (progn
	    (setq ret (cons (car cur) ret))
	    (setq tokens (cdr cur))
	    (setq i (+ 1 i)))))
    (if (< i min) (cons nil tokens)
      (cons (reverse ret) tokens))))

(defun parse-alternatives-meta (alternatives tokens)
  (let ((cur (funcall (car alternatives) tokens)))
    (if (car cur) cur
      (if (cdr alternatives) (parse-alternatives (cdr alternatives) tokens)
	(cons nil tokens)))))

(defun parse-concat-meta (what tokens)
  (let ((this-parse)
	(toks tokens)
	(fail nil))
    (dolist (cur-parse what toks)
      (let ((cur-res (funcall cur-parse toks)))
	(setq toks (cdr toks))
	(setq this-parse (cons (car cur-res) this-parse))
	(if (not (car this-parse)) (setq fail t))))
    (if fail (cons nil tokens)
      ;;(debug)
      (cons (reverse this-parse) toks))))



;;;Testing
(car (parse-repeat (abnf-lex "4*3 Fool") ))

(parse-repetition 'parse-c-wsp 0 -1 (abnf-lex grammar))

(list (cons 'TWSP " ") (cons 'TCRLF "\n"))

(parse-alternatives (list 'parse-CRLF 'parse-WSP) (list (cons 'TWSP " ") (cons 'TCRLF "\n")))

(cdr (parse-repetition
      (lambda (tokens)
	(parse-alternatives (list 'parse-c-nl 'parse-WSP) tokens))
      0 -1 (abnf-lex grammar)))

(cdr (parse-repetition
      'parse-c-wsp 0 -1 (abnf-lex grammar)))

(cdr (parse-repetition 'parse-CRLF 0 -1 (abnf-lex grammar)))

(parse-CRLF (abnf-lex grammar))

(format "%s" (abnf-lex grammar))

(parse-rulename (abnf-lex grammar))



(let ((rules "rule = %b101 foo bar / balls ( something *[stuff]) ; comment\n" )
      (lex)
      (cur 0))
  (while (< cur (length rules))
    (let ((next (lex-next rules cur)))
      (setq lex (cons (car next) lex))
      (setq cur (cdr next))))
  (reverse lex))




(format "%s" (abnf-lex grammar))

(setq grammar
      "
   ;;man this is foobar
    

elements       =  alternation *c-wsp ; foo bar
balls = foo bar ; another comment
")

(setq grammar
      "

elements       =  alternation *c-wsp

	 c-wsp          =  WSP / (c-nl WSP)

	 c-nl           =  comment / CRLF
				; comment or newline

	 comment        =  \";\" *(WSP / VCHAR) CRLF

	 alternation    =  concatenation
			   *(*c-wsp \"/\" *c-wsp concatenation)

	 concatenation  =  repetition * (  1  * c-wsp  repetition  ) 

")

(abnf-lex grammar)

repetition     =  [repeat] element

repeat         =  1*DIGIT / (*DIGIT \"*\" *DIGIT)

element        =  rulename / group / option /
char-val / num-val / prose-val

")"

(let (res)
  (dolist (cur '("a" "b" "c" "d") res) (setq res (cons cur res))))

(defun my-fact (n)
  (if (< n 2) 1 (* n (my-fact (- n 1)))))

(let (l)
  (dolist (cur '(1 2 3 4 5 6 7 8 9 10 11) l)
    (setq l (cons (my-fact cur) l))))
 
(let ((ret '(1 2)))
  (dolist (cur '(1 2 3 4 5 6 7 ))
    (setq ret (cons (my-fact cur) ret))
    (message (concat "foo: " (number-to-string cur))))
  (if (> (car ret) 10) 100
    ret))

(let ((k 0))
  (dolist (cur '(1 2 3 4) k) (setq k (+ k cur))))

(let ((res)
      (T 10.0))
  (dotimes (cur T res) (setq res (cons (sin (/ (* cur pi) T)) res))))

