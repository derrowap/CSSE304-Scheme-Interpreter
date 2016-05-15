; Adam Gastineau and Austin Derrow-Pinion

; top-level-eval evaluates a form in the global environment

(define *prim-proc-names* '(call/cc + - * / add1 sub1 zero? not = < > >= <= cons car cdr caar cdar cadr cddr
								caddr caadr cdadr cdddr caaar cadar cdaar cddar list null? append list-tail
								assq eq? eqv? equal? atom? length list->vector list? pair? procedure?
								vector->list vector make-vector vector-ref vector? number?
								symbol? set-car! set-cdr! vector-set! display newline
								map apply quotient void call-with-values values))

(define make-init-env
	(lambda ()
		(extend-env
		*prim-proc-names*
		; TODO: Convert to map-cps?
		(map prim-proc *prim-proc-names*)
		(empty-env))))

(define global-env (make-init-env))

(define reset-global-env
	(lambda () 
		(set! global-env (make-init-env))))

(define identity-proc
	(lambda (x) x))

(define top-level-eval
	(lambda (form)
		; later we may add things that are not expressions.
		(eval-exp form (empty-env) (init-k))))

; eval-exp is the main component of the interpreter

(define eval-exp
	(lambda (exp env k)
		(cases expression exp
			[lit-exp (datum) (apply-k k datum)]
			[var-exp (id)
				(apply-env env id k; look up its value.
					identity-proc ; procedure to call if id is in the environment 
					(lambda () 
					   	(apply-env-ref global-env id
					   		identity-proc
					   		(lambda ()
					   			(eopl:error 'apply-env ; procedure to call if id not in env
					   				"variable not found in environment: ~s" id)))))]
			[lambda-exp (ids body)
				(apply-k k (closure ids body env))]
			[lambda-list-exp (idlist body)
				(apply-k k (closure-list idlist body env))]
			[lambda-improper-exp (ids idlist body)
				(apply-k k (closure-improper ids idlist body env))]
			[let-exp (ids idlist body)
				(eopl:error 'eval-exp "let-exp should have been transformed into a lambda-exp by syntax-expand: ~a" exp)]
			[let*-exp (ids values body)
				(eopl:error 'eval-exp "let*-exp should have been transformed into a lambda-exp by syntax-expand: ~a" exp)]
			[letrec-exp (ids values body)
				(eopl:error 'eval-exp "letrec-exp should have been transformed by syntax-expand: ~a" exp)]
			[named-let-exp (name ids values body)
				(eopl:error 'eval-exp "name-let-exp should have been transformed by syntax-expand: ~a" exp)]
			[if-exp (test result)
				(eval-exp test env (if-k result env k))]
			[if-else-exp (test result elseRes)
				(eval-exp test env (if-else-k result elseRes env k))]
			[begin-exp (body)
				(eopl:error 'eval-exp "begin-exp should have been transformed into a lambda-exp by syntax-expand: ~a" exp)]
			[set!-exp (id exp)
				; TODO: Handle?
				(set-ref!
					(apply-env-ref env id
						identity-proc ; procedure to call if id is in the environment 
						(lambda () 
						   	(apply-env-ref global-env id
						   		identity-proc
						   		(lambda ()
						   			(eopl:error 'apply-env-ref ; procedure to call if id not in env
						   				"variable not found in environment: ~s" id)))))
					(eval-exp exp env k))]
			[cond-exp (tests results)
				(eopl:error 'eval-exp "cond-exp should have been transformed into if-exp's by syntax-expand: ~a" exp)]
			[and-exp (bodies)
				(eopl:error 'eval-exp "and-exp should have been transformed into if-exp's by syntax-expand: ~a" exp)]
			[or-exp (bodies)
				(eopl:error 'eval-exp "or-exp should have been transformed into if-exp's by syntax-expand: ~a" exp)]
			[case-exp (key tests results)
				(eopl:error 'eval-exp "case-exp should have been transformed by syntax-expand: ~a" exp)]
			[while-exp (test bodies)
				(eopl:error 'eval-exp "while-exp should have been transformed by syntax-expand: ~a" exp)]
			[define-exp (id exp)
				(set! global-env (extend-env (list id) (list (eval-exp exp env (init-k))) global-env))]
			;[do2-exp (bodies test)
			;	; TODO: Handle/Remove?
			;	(begin
			;		(eval-bodies bodies env)
			;		(if (eval-exp test env)
			;			(eval-exp (do2-exp bodies test) env)))]
			[app-exp (rator rands)
				; TODO: Handle.  Should this stay as apply-proc or should it become simply an eval-exp as suggested in the slides?
				;(let ([proc-value (eval-exp rator env)]
				;		[args (eval-rands rands env)])
				;	(apply-proc proc-value args))]
				(eval-exp rator env (rator-k rands env k))]
			[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define case-or-expression
	(lambda (key test)
		; TODO: Convert to map-cps?
		(syntax-expand (or-exp (map (lambda (x) (app-exp (var-exp `equal?) (list key x))) test)))))

(define build-temps
	(lambda (values)
		; TODO: Convert to map-cps?
		(map syntax->datum (generate-temporaries values))))

(define make-set!-list
	(lambda (ids values)
		(if (null? ids)
			'()
			(cons
				(set!-exp (car ids) (parse-exp (car values)))
				(make-set!-list (cdr ids) (cdr values))))))

(define syntax-expand
	(lambda (exp)
		(cases expression exp
			[lit-exp (datum) (lit-exp datum)]
			[var-exp (id) (var-exp id)]
			[lambda-exp (ids body)
				; TODO: Convert to map-cps?
				(lambda-exp ids (map syntax-expand body))]
			[lambda-list-exp (idlist body)
				; TODO: Convert to map-cps?
				(lambda-list-exp idlist (map syntax-expand body))]
			[lambda-improper-exp (ids idlist body)
				; TODO: Convert to map-cps?
				(lambda-improper-exp ids idlist (map syntax-expand body))]
			[let-exp (ids values body)
				; TODO: Convert to map-cps?
				(app-exp (lambda-exp ids (map syntax-expand body)) (map syntax-expand values))]
			[let*-exp (ids values body)
				(app-exp (lambda-exp 
							(list (car ids))
							(if (null? (cdr ids))
								; TODO: Convert to map-cps?
								(map syntax-expand body)
								(list (syntax-expand (let*-exp (cdr ids) (cdr values) body)))))
					(list (syntax-expand (car values))))]
			[letrec-exp (ids values body)
				(syntax-expand
					(let-exp
						ids
						; TODO: Convert to map-cps?
						(map (lambda (x) (lit-exp #f)) ids)
						(list (let ([temps (build-temps values)])
							(let-exp
								temps
								values
								(list (begin-exp
									(append
										(make-set!-list ids temps)
										(list (let-exp '() '() body))))))))))]
				; Equivalent to EOPL
				;(let ((var #f) ...)
				;	(let ((temp expr) ...)
				;		(set! var temp) ...
				;		(let () body1 body2 ...)))	
			[named-let-exp (name ids values body)
				(syntax-expand
					(app-exp
						(letrec-exp
							(list name)
							(list (lambda-exp ids body))
							(list (var-exp name)))
						values))]
				; Equivalent to EOPL
				;((letrec ((name (lambda (var ...) body1 body2 ...)))
				;		name)
				;	expr ...)

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
				; TODO: Convert to map-cps?
				(app-exp (lambda-exp '() (map syntax-expand body)) '())]
			[set!-exp (id exp)
				(set!-exp id (syntax-expand exp))]
			[cond-exp (tests results)
				; TODO: Convert to map-cps?
				(if (null? (cdr tests))
					(if-exp
						(syntax-expand (1st tests))
						(app-exp (lambda-exp '() (map syntax-expand (1st results))) '()))
					(if-else-exp 
						(syntax-expand (1st tests))
						(app-exp (lambda-exp '() (map syntax-expand (1st results))) '())
						(syntax-expand (cond-exp (cdr tests) (cdr results)))))]
			[and-exp (bodies)
				(if (null? (cdr bodies))
					(if-else-exp
						(syntax-expand (1st bodies))
						(syntax-expand (1st bodies))
						(lit-exp #f))
					(if-else-exp
						(syntax-expand (1st bodies))
						(syntax-expand (and-exp (cdr bodies)))
						(lit-exp #f)))]
			[or-exp (bodies)
				(app-exp
					(lambda-exp 
						(list 'if-else-test)
						(list
							(if-else-exp
								(var-exp 'if-else-test)
								(var-exp 'if-else-test)
								(if (null? (cdr bodies))
									(lit-exp #f)
									(syntax-expand (or-exp (cdr bodies)))))))
					(list (syntax-expand (car bodies))))]
				; Equivalent to:
				; (let ((test (1st bodies)))
				;	(if test
				;		test
				;		(let ((test (2nd bodies)))
				; 			(if test
				;				test
				;				...))))
			[case-exp (key tests results)
				(if (null? (cdr tests))
					(if-exp (case-or-expression key (1st tests))
						(syntax-expand (1st results)))
					(if-else-exp (case-or-expression key (1st tests))
						(syntax-expand (1st results))
						(syntax-expand (case-exp key (cdr tests) (cdr results)))))]
			[while-exp (test bodies)
				(app-exp (lambda-exp (list 'x) (list (app-exp (var-exp 'x) (list (var-exp 'x)))))
					(list (lambda-exp (list 'y) (list (if-exp
						(syntax-expand test)
						(app-exp (lambda-exp '()
							(append bodies
									(list (app-exp (var-exp 'y) (list (var-exp 'y))))))
							'()))))))]
				; equivalent to:
				;((lambda (x) (x x))
				;	(lambda (y)
				;		(if test
				;			((lambda ()
				;				bodies
				;				(y y))))))
			[define-exp (id exp)
				(define-exp id (syntax-expand exp))]
			[do1-exp (bodies test)
				(syntax-expand
					(begin-exp
						(append bodies (list (while-exp test bodies)))))]
			[do2-exp (bodies test)
				(do2-exp bodies test)]
			[app-exp (rator rands)
				(app-exp
					(syntax-expand rator)
					; TODO: Convert to map-cps
					(map syntax-expand rands))]
			[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env k)
		(map-cps (lambda (x k) (eval-exp x env k)) rands k)))

; Evaluates a series of bodies in the given environment.
;(define eval-bodies
;	(lambda (bodies env k)
;		(if (null? (cdr bodies))
;			(eval-exp (car bodies) env k)
;			(eval-exp (car bodies) env (eval-bodies-k (cdr bodies) env k)))))


				;(lambda (last-in-body-k) ; v1 is result from right most body
				;	(eval-exp
				;		(car bodies)
				;		env
				;		(lambda (inner-body-k) ; v2 is result of some inner body
				;			(apply-k k v1))))))))

		; TODO: this isn't CPS
		;(let loop ([bodies bodies])
		;	(if (null? (cdr bodies))
		;		(eval-exp (car bodies) env k)
		;		(begin (eval-exp (car bodies) env (init-k)) (loop (cdr bodies)))))))


(define extract-extra-args-closure-improper
	(lambda (params args)
		(if (null? params)
			(list args)
			(cons (car args) (extract-extra-args-closure-improper (cdr params) (cdr args))))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args k)
		(cases proc-val proc-value
			[continuation-proc (k)
				(apply-k k (car args))]
			[prim-proc (op)
				; TODO: Handle
				(apply-prim-proc op args k)]
			[closure (params bodies env)
				; TODO: Handle
				(apply-k
					(eval-bodies-k
						bodies
						(extend-env params args env)
						k)
					k)]
				;(eval-bodies bodies (extend-env params args env) k)]
			[closure-list (listsymbol bodies env)
				; TODO: Handle
				(apply-k
					(eval-bodies-k
						bodies
						(extend-env (list listsymbol) (list args) env)
						k)
					k)]
				;(eval-bodies bodies (extend-env (list listsymbol) (list args) env) k)]
			[closure-improper (params listsymbol bodies env)
				; TODO: Handle
				(apply-k
					(eval-bodies-k
						bodies
						(extend-env 
							(append params (list listsymbol)) 
							(extract-extra-args-closure-improper params args)
							env)
						k)
					k)]
				;(eval-bodies bodies (extend-env (append params (list listsymbol)) (extract-extra-args-closure-improper params args) env) k)]
			[else (error 'apply-proc
				"Attempt to apply bad procedure: ~s" 
				proc-value)])))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
	(lambda (prim-proc args k)
		(case prim-proc
			; TODO: Add exception handler
			[(call/cc)
				(apply-proc
					(car args)
					(list (continuation-proc k))
					k)]
			; TODO: Convert all to CPS
			[(+) (apply-k k (apply + args))]
			[(-) (apply-k k (apply - args))]
			[(*) (apply-k k (apply * args))]
			[(/) (apply-k k (apply / args))]
			[(add1) (apply-k k (+ (1st args) 1))]
			[(sub1) (apply-k k (- (1st args) 1))]
			[(zero?) (apply-k k (= (1st args) 0))]
			[(not) (apply-k k (not (1st args)))]
			[(=) (apply-k k (= (1st args) (2nd args)))]
			[(<) (apply-k k (< (1st args) (2nd args)))]
			[(>) (apply-k k (> (1st args) (2nd args)))]
			[(>=) (apply-k k (>= (1st args) (2nd args)))]
			[(<=) (apply-k k (<= (1st args) (2nd args)))]
			[(cons) (apply-k k (cons (1st args) (2nd args)))]
			[(car) (apply-k k (car (1st args)))]
			[(cdr) (apply-k k (cdr (1st args)))]
			[(caar) (apply-k k (caar (1st args)))]
			[(cdar) (apply-k k (cdar (1st args)))]
			[(cadr) (apply-k k (cadr (1st args)))]
			[(cddr) (apply-k k (cddr (1st args)))]
			[(caddr) (apply-k k (caddr (1st args)))]
			[(caadr) (apply-k k (caadr (1st args)))]
			[(cdadr) (apply-k k (cdadr (1st args)))]
			[(cdddr) (apply-k k (cdddr (1st args)))]
			[(caaar) (apply-k k (caaar (1st args)))]
			[(cadar) (apply-k k (cadar (1st args)))]
			[(cdaar) (apply-k k (cdaar (1st args)))]
			[(cddar) (apply-k k (cddar (1st args)))]
			[(list) (apply-k k args)]
			[(null?) (apply-k k (null? (1st args)))]
			[(append) (apply-k k (append (1st args) (2nd args)))]
			[(list-tail) (apply-k k (list-tail (1st args) (2nd args)))]
			[(assq) (apply-k k (assq (1st args) (2nd args)))]
			[(eq?) (apply-k k (eq? (1st args) (2nd args)))]
			[(eqv?) (apply-k k (eqv? (1st args) (2nd args)))]
			[(equal?) (apply-k k (equal? (1st args) (2nd args)))]
			[(atom?) (apply-k k (not (pair? (1st args))))]
			[(length) (apply-k k (length (1st args)))]
			[(list->vector) (apply-k k (list->vector (1st args)))]
			[(list?) (apply-k k (list? (1st args)))]
			[(pair?) (apply-k k (pair? (1st args)))]
			[(procedure?) (apply-k k (proc-val? (1st args)))]
			[(vector->list) (apply-k k (vector->list (1st args)))]
			[(vector) (apply-k k (list->vector args))]
			[(make-vector) (apply-k k (make-vector (1st args)))]
			[(vector-ref) (apply-k k (vector-ref (1st args) (2nd args)))]
			[(vector?) (apply-k k (vector? (1st args)))]
			[(number?) (apply-k k (number? (1st args)))]
			[(symbol?) (apply-k k (symbol? (1st args)))]
			[(set-car!) (set-car! (1st args) (2nd args))]
			[(set-cdr!) (set-cdr! (1st args) (2nd args))]
			[(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
			[(display) (display (1st args))]
			[(newline) (newline)]
			[(map) (apply-k k (map (lambda (x) (apply-proc (car args) (list x) (init-k))) (cadr args)))]
			[(apply) (apply-proc (1st args) (2nd args) k)]
			[(quotient) (apply-k k (quotient (1st args) (2nd args)))]
			[(void) (apply-k k (void))]
			[(call-with-values)
				(apply-proc (2nd args) (apply-proc (1st args) '()))]
			[(values) args]
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
