; Adam Gastineau and Austin Derrow-Pinion

; top-level-eval evaluates a form in the global environment

(define *prim-proc-names* '(+ - * / add1 sub1 zero? not = < > >= <= cons car cdr caar cdar cadr cddr
								caddr caadr cdadr cdddr caaar cadar cdaar cddar list null?
								assq eq? equal? atom? length list->vector list? pair? procedure?
								vector->list vector make-vector vector-ref vector? number?
								symbol? set-car! set-cdr! vector-set! display newline
								map apply ))

(define global-env
	(extend-env
		*prim-proc-names*
		(map prim-proc *prim-proc-names*)
		(empty-env)))

(define top-level-eval
	(lambda (form)
		; later we may add things that are not expressions.
		(eval-exp form global-env)))

; eval-exp is the main component of the interpreter

(define identity-proc
	(lambda (x) x))

(define eval-exp
	(lambda (exp env)
		(cases expression exp
			[lit-exp (datum) datum]
			[var-exp (id)
				(apply-env env id; look up its value.
					identity-proc ; procedure to call if id is in the environment 
					(lambda () 
					   	(apply-env global-env
					   		id
					   		identity-proc
					   		(lambda ()
					   			(eopl:error 'apply-env ; procedure to call if id not in env
					   				"variable not found in environment: ~s" id)))))]
			[lambda-exp (ids body)
				(closure ids body env)]
			[lambda-list-exp (idlist body)
				(closure-list idlist body env)]
			[lambda-improper-exp (ids idlist body)
				(closure-improper ids idlist body env)]
			[let-exp (ids idlist body)
				(eopl:error 'eval-exp "let-exp should have been transformed into a lambda-exp by syntax-expand: ~a" exp)]
			[let*-exp (ids values body)
				(eopl:error 'eval-exp "let*-exp should have been transformed into a lambda-exp by syntax-expand: ~a" exp)]
			;[letrec-exp (ids values body)
			; TODO: not yet implemented
			;[named-let-exp (name ids values body)
			; TODO: not yet implemented
			[if-exp (test result)
				(if (eval-exp test env)
					(eval-exp result env))]
			[if-else-exp (test result elseRes)
				(if (eval-exp test env)
					(eval-exp result env)
					(eval-exp elseRes env))]
			[begin-exp (body)
				(eopl:error 'eval-exp "begin-exp should have been transformed into a lambda-exp by syntax-expand: ~a" exp)]
			;[set!-exp (id rvalue)
			; TODO: not yet implemented
			[cond-exp (tests results)
				(eopl:error 'eval-exp "cond-exp should have been transformed into if-exp's by syntax-expand: ~a" exp)]
			[and-exp (bodies)
				(eopl:error 'eval-exp "and-exp should have been transformed into a if-exp's by syntax-expand: ~a" exp)]
			;[or-exp
			;[case-exp
			; TODO: not yet implemented
			[app-exp (rator rands)
				(let ([proc-value (eval-exp rator env)]
						[args (eval-rands rands env)])
					(apply-proc proc-value args))]
			[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define syntax-expand
	(lambda (exp)
		(cases expression exp
			[lit-exp (datum) (lit-exp datum)]
			[var-exp (id) (var-exp id)]
			[lambda-exp (ids body)
				(lambda-exp ids (map syntax-expand body))]
			[lambda-list-exp (idlist body)
				(lambda-list-exp idlist (map syntax-expand body))]
			[lambda-improper-exp (ids idlist body)
				(lambda-improper-exp ids idlist (map syntax-expand body))]
			[let-exp (ids values body)
				(app-exp (lambda-exp ids (map syntax-expand body)) (map syntax-expand values))]
			;[let*-exp (ids values body)
			; TODO: not yet implemented
			;[letrec-exp (ids values body)
			; TODO: not yet implemented
			;[named-let-exp (name ids values body)
			; TODO: not yet implemented
			[if-exp (test result)
				(if-exp 
					(syntax-expand test)
					(syntax-expand result))]
			[if-else-exp (test result elseRes)
				(if-else-exp
					(syntax-expand test)
					(syntax-expand result)
					(syntax-expand elseRes))]
			[begin-exp (body)
				(app-exp (lambda-exp '() (map syntax-expand body)) '())]
			;[set!-exp (id rvalue)
			; TODO: not yet implemented
			[cond-exp (tests results)
				(if (null? (cdr tests))
					(if-exp
						(syntax-expand (car tests))
						(app-exp (lambda-exp '() (map syntax-expand (car results))) '()))
					(if-else-exp 
						(syntax-expand (car tests))
						(app-exp (lambda-exp '() (map syntax-expand (car results))) '())
						(syntax-expand (cond-exp (cdr tests) (cdr results)))))]
			[and-exp (bodies)
				(if (null? (cdr bodies))
					(if-else-exp
						(syntax-expand (car bodies))
						(syntax-expand (car bodies))
						(lit-exp #f))
					(if-else-exp
						(syntax-expand (car bodies))
						(syntax-expand (and-exp (cdr bodies)))
						(lit-exp #f)))]
			;[or-exp
			; TODO: not yet implemented
			;[case-exp
			; TODO: not yet implemented
			[app-exp (rator rands)
				(app-exp
					(syntax-expand rator)
					(map syntax-expand rands))]
			[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env)
		(map (lambda (x)
				(eval-exp x env))
			rands)))

; Evaluates a series of bodies in the given environment.
(define eval-bodies
	(lambda (bodies env)
		(let loop ([bodies bodies])
			(if (null? (cdr bodies))
				(eval-exp (car bodies) env)
				(begin (eval-exp (car bodies) env) (loop (cdr bodies)))))))


(define extract-extra-args-closure-improper
	(lambda (params args)
		(if (null? params)
			(list args)
			(cons (car args) (extract-extra-args-closure-improper (cdr params) (cdr args))))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
			[prim-proc (op)
				(apply-prim-proc op args)]
			[closure (params bodies env)
				(eval-bodies bodies (extend-env params args env))]
			[closure-list (listsymbol bodies env)
				(eval-bodies bodies (extend-env (list listsymbol) (list args) env))]
			[closure-improper (params listsymbol bodies env)
				(eval-bodies bodies (extend-env (append params (list listsymbol)) (extract-extra-args-closure-improper params args) env))]
			; You will add other cases
			[else (error 'apply-proc
				"Attempt to apply bad procedure: ~s" 
				proc-value)])))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-procedure-to-all
	(lambda (procedure args result)
		(if (null? args)
			result
			(apply-procedure-to-all procedure (cdr args) (procedure result (car args))))))

(define apply-map
	(lambda (f args)
		(if (null? (caar args))
			'()
			(append (map (lambda (x) (apply-proc f x)) (map (lambda (x) (map car x)) args)) 
				(apply-map f (map (lambda (x) (map cdr x)) args))))))

(define apply-prim-proc
	(lambda (prim-proc args)
		(case prim-proc
			; TODO: Add exception handler
			[(+) (apply-procedure-to-all + (cdr args) (car args))]
			[(-) (apply-procedure-to-all - (cdr args) (car args))]
			[(*) (apply-procedure-to-all * (cdr args) (car args))]
			[(/) (apply-procedure-to-all / (cdr args) (car args))]
			[(add1) (+ (1st args) 1)]
			[(sub1) (- (1st args) 1)]
			[(zero?) (= (1st args) 0)]
			[(not) (not (1st args))]
			[(=) (= (1st args) (2nd args))]
			[(<) (< (1st args) (2nd args))]
			[(>) (> (1st args) (2nd args))]
			[(>=) (>= (1st args) (2nd args))]
			[(<=) (<= (1st args) (2nd args))]
			[(cons) (cons (1st args) (2nd args))]
			[(car) (car (1st args))]
			[(cdr) (cdr (1st args))]
			[(caar) (caar (1st args))]
			[(cdar) (cdar (1st args))]
			[(cadr) (cadr (1st args))]
			[(cddr) (cddr (1st args))]
			[(caddr) (caddr (1st args))]
			[(caadr) (caadr (1st args))]
			[(cdadr) (cdadr (1st args))]
			[(cdddr) (cdddr (1st args))]
			[(caaar) (caaar (1st args))]
			[(cadar) (cadar (1st args))]
			[(cdaar) (cdaar (1st args))]
			[(cddar) (cddar (1st args))]
			[(list) args]
			[(null?) (null? (1st args))]
			[(assq) (assq (1st args) (2nd args))]
			[(eq?) (eq? (1st args) (2nd args))]
			[(equal?) (equal? (1st args) (2nd args))]
			[(atom?) (not (pair? (1st args)))]
			[(length) (length (1st args))]
			[(list->vector) (list->vector (1st args))]
			[(list?) (list? (1st args))]
			[(pair?) (pair? (1st args))]
			[(procedure?) (proc-val? (1st args))]
			[(vector->list) (vector->list (1st args))]
			[(vector) (list->vector args)]
			[(make-vector) (make-vector (1st args))]
			[(vector-ref) (vector-ref (1st args) (2nd args))]
			[(vector?) (vector? (1st args))]
			[(number?) (number? (1st args))]
			[(symbol?) (symbol? (1st args))]
			[(set-car!) (set-car! (1st args) (2nd args))]
			[(set-cdr!) (set-cdr! (1st args) (2nd args))]
			[(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
			[(display) (display (1st args))]
			[(newline) (newline)]
			[(map) (apply-map (1st args) (list (cdr args)))]
			[(apply) (apply-proc (1st args) (2nd args))]
			[else (error 'apply-prim-proc 
				"Bad primitive procedure name: ~s" 
				prim-op)])))

(define rep      ; "read-eval-print" loop.
	(lambda ()
		(display "--> ")
		;; notice that we don't save changes to the environment...
		(let ([answer (eval-one-exp (read))])
			;; TODO: are there answers that should display differently?
			(eopl:pretty-print answer) (newline)
			(rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
	(lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))
