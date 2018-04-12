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
  (let ((ret "\\(?:"))
    (mapcar (lambda (alt) (setq ret (concat ret alt "\\|"))) alts)
    (aset ret (- (length ret) 1) #x29)
    ret))

;;my helper rules
(setq lower-case "[\x61-\x7a]")
(setq upper-case "[\x41-\x5a]")
(defun num-opt-arg (NUM-TYPE)
      (concat (alternative-regexp
	       (list (concat "\\(?:-" NUM-TYPE "+\\)")
		     (concat "\\(?:\\." NUM-TYPE "+\\)+"))) "?"))

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
(setq LWSP (concat (alternative-regexp (list WSP (concat CRLF WSP))) "*"))
(setq OCTET "[\x00-\xFF]")
(setq SP "\x20")
(setq VCHAR "[\x21-\x7e]")
(setq WSP (alternative-regexp (list SP HTAB)))

;;;Lexical objects
;;note that "c-wsp" from the standard will be avoided by the 'first pass operations'
;;

(setq rulename (concat ALPHA (alternative-regexp (list ALPHA DIGIT "-")) "*"))
(setq abnf-comment (concat ";" (alternative-regexp (list WSP VCHAR)) "*" CRLF))
(setq c-nl (alternative-regexp (list abnf-comment CRLF)))
(setq c-wsp (alternative-regexp (list WSP (concat "\\(?:" c-nl WSP "\\)"))))
(setq defined-as (concat WSP "*" (alternative-regexp (list "=" "=/")) WSP "*"))
(setq repeat (alternative-regexp (list (concat DIGIT "+") (concat DIGIT "*\\*" DIGIT "*"))))
(setq char-val (concat DQUOTE (alternative-regexp (list "[\x20-\x21]"
							"[\x23-\x7e]")) "*" DQUOTE))
(setq bin-val (concat "b" BIT "+" (num-opt-arg BIT)))
(setq dec-val (concat "d" DIGIT "+" (num-opt-arg DIGIT)))
(setq hex-val (concat "x" HEXDIG "+" (num-opt-arg HEXDIG)))
(setq num-val (concat "%" (alternative-regexp (list bin-val dec-val hex-val))))
(setq prose-val (concat "<" (alternative-regexp (list "[\x20-\x3d]" "[\x3f-\x7e]")) "*>"))

;;;Lexical Analysis
;;The end of a rule declaration can be found difinitivel by the
;;lexical form CRLF[^ WSP CRLF], that is, a newline followed by
;;something that is not a newline.
(setq end-of-rule (alternative-regexp
		   (list (concat CRLF "[^" WSP CRLF "]"))))

(defun get-end-of-rule (rule-str start)
  (let ((end (string-match end-of-rule rule-str start)))
    (if end end (length rule-str))))

(defun get-rule (rule-str start)
  (let ((rule-end (get-end-of-rule rule-str start)))
    (apply 'concat (split-string
		     (substring rule-str start rule-end) CRLF t ";.*"))))

;;(cons 'a (cons 'b (cons 'c nil)))

(let ((rule (get-rule rule-str 0)))
  (string-match rulename rule)
  (match-end 0))

(defun lex-rule (rule-str)
  (let ((name-pos (string-match rulename rule-str)))
    (if (equla name-pos 0)
	(cons (substring rule-str 0 (match-end 0))
	      (lex-

  
(get-rule rule-str 0)

(get-end-of-rule rule-str 59)

(apply 'concat (split-string (get-rule rule-str 0) CRLF t ";.*"))

;;;<testing>


(string-match abnf-comment (get-rule rule-str 0))

(setq rule-str
"rule =  rulename defined-as
        elements c-nl ; rule 

char-val =  DQUOTE *(%x20-21 / %x23-7E) DQUOTE
              ; quoted string of SP and VCHAR
              ;  without DQUOTE
")

(defun my-mover (n)
  (interactive "nhow far?")
  (goto-char (+ (point) n)))

(let ((rule-str (get-register #x67)))
  (string-match end-of-rule rule-str))

;;;</testing>

;;;
;;;abnf rules:
;;;
;;;rulelist -> rule*
;;;rule -> rulename := alternation
;;;alternation -> {m}*{n}element ("/" {m}*{n}element)*
;;;element -> rule | group | option | string | number
;;;group -> "(" alternation ")"
;;;option -> "[" alternation "]"
;;;
;;;
;;;
;;;elements -> alternation
;;;alternation -> concatenation ("/" concatenation)*
;;;concatenation -> repetition (repetition)*
;;;repetition -> {m}*{n}element



;;;Lexical testing...

(let ((str "stuff.. d8-9 <rule-name...\"\" ~ho>"))
  (string-match prose-val str)
  (match-string 0 str))

(let ((str "ax%b100.1010-100.1"))
  (string-match num-val str)
  (match-string 0 str))

(let ((str "axbx%d100.1010.100-1"))
  (string-match num-val str)
  (match-string 0 str))

(let ((str "axbx%x100-d1010-100.1"))
  (string-match num-val str)
  (match-string 0 str))

(string-match bin-val "foo1* b0ar=s")

(string-match "a\\{2,3\\}b" "ba ab aaaab")
(string-match "[\x20-\x2d]" "fo(o - bar")
(string-match "1\\*" "foo1* bar=s")


(let ((str " 0name-and-stuf __["))
  (string-match rulename str)
  (match-string 0 str))


(string-match ALPHA "0123abc")
(string-match BIT "a2100")
(string-match CR "a21\n\r00")
(string-match CRLF "a21\n\r\r\n00")
(string-match CTL "a\x00\x32\x31\n\r\r\n00")
(string-match DIGIT "a\x00\x32\x31\n\r\r\n00")
(string-match DQUOTE "\"foobar\"")
(string-match HEXDIG " x8fa")
(string-match HTAB "bar	foo")
(string-match LF "a21\r\n00")


;;;Grammar Modification (conversion to CNF)
;;A double underscore will prefix Non-Terminals to introduce new symbols, so should not be used
;;in the specification of a grammar...
;;
;;This algorithm is basically ripped from the wikipedia page:
;;https://en.wikipedia.org/wiki/Chomsky_normal_form

;;Here, a list of production rules from the read grammar is passed to be converted.  The rules will be of the form (Head (list Rule1

;;It is assumed that the first production rule in the grammar is from
;;the Start symbol
(defun CNF-START (G)
  (let ((terminal-rules (car G))
	(production-rules (cdr G))
	(start-symbol (car (cdr G))))
    (cons terminal-rules (cons (cons "__S" start-symbol) production-rules))))

;;Since non-terminals are held as strings in the computer, it is
;;assumed that every terminal symbol T appearing in a production rule
;;is of the form "__LITERAL__T".  For example, a colon (";") would be
;;of the form "__LITERAL__;"

(substring "__LITERAL__" 0 (length "__LITERAL__"))

(defun CNF-TERM (G)
  (let ((terminal-rules (car G))
	(production-rules (cdr G))
	(new-rules '())
	(prefix "__LITERAL__")
	(plength (length  "__LITERAL__")))
    (mapcar (lambda (rule)
	      

;;;Testing
(get-partition-product my-rules curM 1 2)

(calc-cell my-rules curM 1 2)

(lift-rules-x my-rules (get-partition-product my-rules curM 1 2))

my-rules
curM
;;

(car (get-cell curM 1 2))

(car (get-cell curM 2 3))

(cartesian-product (get-cell curM 1 2) (get-cell curM 1 2))

(lift-rules-x my-rules (list (cons 'A 'A)))

(lift-rules-p my-rules (cons 'A 'A))

(let ((a '(1 2 3))) (setq a (append a '(2 3 4))) a)




(setq my-rules '((S (A V-)) (S (A B)) (V- (M B)) (M (A B)) (M (A V-))))
(setq my-gram (cons my-term-rs my-rules))

(setq my-rules (list (cons "S" (cons "A" "B")) (cons "A" (cons "A" "A")) (cons "B" (cons "A" "B"))))

(setq my-term-rs (list (cons "A" (aref "a" 0)) (cons "B" (aref "b" 0))))

(setq my-gram (cons my-term-rs my-rules))

(setq curM (get-cyk-matrix my-gram "aab"))



(aref (aref (blank-cyk-matrix (length "aaaab")) 0) 0)

(if (get-cell (blank-cyk-matrix 5) 1 5) "foo" "bar")

(get-cell (blank-cyk-matrix 5) 1 1)

(let ((M (blank-cyk-matrix (length my-word))))
  (aset M (- (length my-word) 1) (lift-terminals (car my-gram) my-word))
  M)

(let ((M (blank-cyk-matrix (length my-word))))
  (aset M (- (length my-word) 1) (lift-terminals (car my-gram) my-word))
  (get-prod-bases (cdr my-gram) M 1 2)
  M)

(cdr my-gram)

(setq my-M [[nil] [(A) (B)]])

(let ((A (make-vector 3 nil)))
  (aset A 1 [1 2 3])
  A)

(if (not my-M) "foo" "bar")


(lift-rules-x my-rules (get-partition-product my-rules my-M 1 2))

(calc-cell my-rules my-M 1 2)

(set-cell my-M 1 2 ())

(setq my-M [ [nil] [nil nil] [(A) (A) (B)] ])

(get-prod-bases my-rules my-M 1 3)

my-M

(car (cdr '((1 1) (2 2))))

;;(cartesian-product ((get-cell my-M 1 1) (get-cell my-M (+ 1 1) 2))
(get-partition-product my-M 1 3)


;;(lift-terminals '((A "a") (A "A") (B "b") (B "B")) "abBAa") ;;(substring "abBAa" 0 1))
;;(equal "a" (substring "abc" 2 1))

;;(substring "abc" 2 3)

;;(length "abdc")

;;(setq my-M [ ["1-3"] ["1-2" "2-3"] ["1-1" "2-2" "3-3"] ])
;;(get-cell my-M 2 2)
;;(setq my-M [[(a b) (c d)] [(e f)] []])

;;(set-cell my-M 1 2 "foo")


;;current testing:

(lift-rules-p ps '(A A))
(lift-rules-nts ps '((A) (A) (B) (C)))

;;grammar:

(setq ps '((S . (A B)) (S . (A A))
	   (A . (A A)) (A . (A C))
	   (B . (A A)) (B . (B C))
	   (C . (C C))))

;;

(setq PRules '((A . (a a)) (A- . (a a)) (B . (b b)) (BA . (a b))(C . (c c))))

(lift-rules-p PRules '(a a))
(car (cartesian-product '(a b c) '(a c)))
(equal '(a a) (list 'a 'a))

(lift-rules-x PRules (cartesian-product '(a b c) '(a c)))

(lift-rules-nts PRules '((a) (a) (a) (b) (b) (b) (c)))

(let ((M (make-vector 3 nil)))
  (aset M 0 [1 2 3])
  (aset M 1 [4 5 6])
  (aset M 2 [7 8 9])
  (aset (aref M 1) 1 0)
  M)


(setq split-height-threshold nil)
(setq split-width-threshold 0)
