; Adam Gastineau and Austin Derrow-Pinion


;; Cell

(define cell
	(lambda (val)
		(cons val 'cell)))

(define cell-ref car)

(define set-cell! set-car!)

(define cell?
	(lambda (obj)
		(and
			(pair? obj)
			(eqv? (cdr obj) 'cell))))

;; Parsed expression datatypes

(define is-literal?
	(lambda (x)
		(or (boolean? x)
			(number? x)
			(string? x)
			(symbol? x)
			(vector? x)
			(null? x)
			(pair? x))))

(define-datatype expression expression?
	[lit-exp
		(id is-literal?)]
	[var-exp
		(id symbol?)]
	[lambda-exp
		(ids (list-of symbol?))
		(body (list-of expression?))]
	[lambda-list-exp
		(idlist symbol?)
		(body (list-of expression?))]
	[lambda-improper-exp
		(ids (list-of symbol?))
		(idlist symbol?)
		(body (list-of expression?))]
	[let-exp
		(ids (list-of symbol?))
		(values (list-of expression?))
		(body (list-of expression?))]
	[let*-exp
		; Identical to let-exp
		(ids (list-of symbol?))
		(values (list-of expression?))
		(body (list-of expression?))]
	[letrec-exp
		; Identical to let-exp
		(ids (list-of symbol?))
		(values (list-of expression?))
		(body (list-of expression?))]
	[named-let-exp
		(name symbol?)
		(ids (list-of symbol?))
		(values (list-of expression?))
		(body (list-of expression?))]
	[if-exp
		(test expression?)
		(result expression?)]
	[if-else-exp
		(test expression?)
		(result expression?)
		(elseRes expression?)]
	[begin-exp
		(body (list-of expression?))]
	[set!-exp
		(id symbol?)
		(exp expression?)]
	[cond-exp
		(tests (list-of expression?))
		(results (list-of (list-of expression?)))]
	[and-exp
		(bodies (list-of expression?))]
	[or-exp
		(bodies (list-of expression?))]
	[case-exp
		(key expression?)
		(tests (list-of (list-of expression?)))
		(results (list-of expression?))]
	[while-exp
		(test expression?)
		(bodies (list-of expression?))]
	[define-exp
		(name symbol?)
		(bind expression?)]
	[app-exp
		(rator expression?)
		(rands (list-of expression?))])

(define let-symbols
	(lambda (x)
		(parse-exp (cadr x))))

(define let-def-invalid-length?
	(lambda (x)
		(or (null? (cdr x)) (not (null? (cddr x))))))

(define let-def-symbol?
	(lambda (x)
		(symbol? (car x))))

(define improper-lambda-helper
	(lambda (ils)
		(if (pair? (cdr ils))
			(let ([var (improper-lambda-helper (cdr ils))])
				(list
					(cons (car ils) (car var))
					(cadr var)))
			(list (list (car ils)) (cdr ils)))))

;; environment type definitions

(define scheme-value?
	(lambda (x) #t))

(define-datatype environment environment?
	[empty-env-record]
	[extended-env-record
		(syms (list-of symbol?))
		(vals (list-of cell?))
		(env environment?)])
	
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
	[prim-proc
		(name symbol?)]
	[closure
		(params (list-of symbol?))
		(bodies (list-of expression?))
		(env environment?)]
	[closure-list
		(listsymbol symbol?)
		(bodies (list-of expression?))
		(env environment?)]
	[closure-improper
		(params (list-of symbol?))
		(listsymbol symbol?)
		(bodies (list-of expression?))
		(env environment?)])
	 
