#lang racket

;; Assignment 3: A CE (Control and Environment) interpreter for Scheme

(provide interp-ce)

; Your task is to write a CE interpreter for a substantial subset of Scheme/Racket. 
; A CE interpreter is meta-circular to a large degree (e.g., a conditional in the target
; language (scheme-ir?) can be implemented using a conditional in the host language (Racket),
; recursive evaluation of a sub-expression can be implemented as a recursive call to the
; interpreter, however, it's characterized by creating an explicit closure value for lambdas
; that saves its static environment (the environment when it's defined). For example, a CE
; interpreter for the lambda calculus may be defined:
(define (interp-ce-lambda exp [env (hash)])
  (match exp
         [`(lambda (,x) ,body)
          ; Return a closure that pairs the code and current (definition) environment
          `(closure (lambda (,x) ,body) ,env)]
         [`(,efun ,earg)
          ; Evaluate both sub-expressions
          (define vfun (interp-ce-lambda efun env))  
          (define varg (interp-ce-lambda earg env))
          ; the applied function must be a closure
          (match-define `(closure (lambda (,x) ,body) ,env+) vfun)
          ; we extend the *closure's environment* and interp the body
          (interp-ce-lambda body (hash-set env+ x varg))]
         [(? symbol? x)
          ; Look up a variable in the current environment
          (hash-ref env x)]))

(define test_env (hash-set (hash) 'x 1))
;(hash-ref test_env 'x)

;(interp-ce-lambda `((lambda (x y) x) x) test_env)

; Following is a predicate for the target language you must support. You must support any
; syntax allowed by scheme-ir that runs without error in Racket, returning a correct value..
(define (scheme-ir? exp)
  ; You should support a few built-in functions bound to the following variables at the top-level
  (define (prim? s) (member s '(+ - * = equal? list cons car cdr null?)))
  (match exp
         [`(lambda ,(? (listof symbol?)) ,(? scheme-ir?)) #t] ; fixed arguments lambda
         [`(lambda ,(? symbol?) ,(? scheme-ir?)) #t] ; variable argument lambda
         [`(if ,(? scheme-ir?) ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [`(let ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(let* ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(and ,(? scheme-ir?) ...) #t]
         [`(or ,(? scheme-ir?) ...) #t]
         [`(apply ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [(? (listof scheme-ir?)) #t]
         [(? prim?) #t]
         [(? symbol?) #t]
         [(? number?) #t]
         [(? boolean?) #t]
         [''() #t]
         [_ #f]))

; Interp-ce must correctly interpret any valid scheme-ir program and yield the same value
; as DrRacket, except for closures which must be represented as `(closure ,lambda ,environment).
; (+ 1 2) can return 3 and (cons 1 (cons 2 '())) can yield '(1 2). For programs that result in a 
; runtime error, you should return `(error ,message)---giving some reasonable string error message.
; Handling errors and some trickier cases will give bonus points. 
(define (interp-ce exp)
  ; Might add helpers or other code here...
  (define (interp exp env)
    (match exp
      
      #;[`(lambda ,xs ,body)
       `(closure (lambda ,xs ,body) ,env)]

      [`(lambda (,x) ,body)
       `(closure (lambda (,x) ,body) ,env)]

      [`(lambda (,xs ..) ,body)
       `(closure (lambda (,@xs) ,body) ,env)]
      
     [`(closure (lambda (,x) ,body) ,env+)
      (interp `(lambda (,x) ,body)  env)]
      ;5]
      ; ...
      ; Add match cases for other language forms
      ; ...

      ;Single Let 
      [`(let ([,x ,rhs]) ,body)
        (interp `((lambda (,x) ,body) ,rhs) env)]

      ;Multiple Let 
     [`(let ([,xs ,rhs] ...) ,body)
        (interp `((lambda (,@xs) ,body) ,@rhs) env)]

      #;[`(let ([,xs ,rhs] . ,rst) ,body)
       (if (equal? rst '())
           (interp `((lambda (,xs) ,body) ,rst) env)
           (interp `((lambda (,xs) (let ,rst ,body)) ,rhs) env))]

      ;Let* (evaluate in place)
      [`(let* ([,x ,val] . ,rst) ,body)
       (if (equal? rst '())
          (interp `((lambda (,x) ,body) ,val) env)
          (interp `((lambda (,x) (let* ,rst ,body)) ,val) env))]
       
       ;(interp `((lambda ,x ,@rst) ,val) env)]
       ;(interp `((lambda (,x) ,(interp `(let ,rst ,body) env)) ,val) env)]

      
      
      [(? boolean? n)
       n]
      

      [`(if ,p ,a ,b)
       (if (interp p env)
           (interp a env)
           (interp b env))]
      
      ['()
       '()]

      [''()
       '()]
      ;apply
      #;[`(apply ,f ,e0)
       (let ([veo (interp  e0 env)]
             ;[func (interp-ce f)]
             )
         
         (apply f veo))]

      [`(apply ,f ,e0)
       (let ([veo (interp  e0 env)]
             [func (interp f env)]
             )
         
         (apply func veo)
         ;veo
         )]
     
      ;+
      ['+
       +]
      ['*
       *]
      ['-
       -]
      ['/
       /]
      
      ['add1
       add1]
     #;[`(+ ,a ,b)
       (+ (interp a env) (interp b env)) ]
      
      [`(+ ,a . ,rst)
       (if (equal? rst '()) 
           (interp a env)
           (+ (interp a env) (interp `(+ ,@rst) env)))]
      ;*
       [`(* ,a . ,rst)
       (if (equal? rst '()) 
           (interp a env)
           (* (interp a env) (interp `(* ,@rst) env)))]
      
      ;-
       [`(- ,a . ,rst)
       (if (equal? rst '()) 
           (interp a env)
           (- (interp a env) (interp `(- ,@rst) env)))]
      
      ;/
       [`(/ ,a . ,rst)
       (if (equal? rst '()) 
           (interp a env)
           (/ (interp a env) (interp `(/ ,@rst) env)))]
      
       ;/
       [`(= ,a . ,rst)
       (if (equal? rst '()) 
           (interp a env)
           (= (interp a env) (interp `(= ,@rst) env)))]
      
      [`(equal? ,a ,b)
       (equal? (interp a env)
               (interp b env))]

      [`(null? ,a)
       (null? (interp a env))]
      
      ;and
      [`(and)
       #t]
      
      [`(and ,a ,b)
       (and
        (interp a env)
        (interp b env))
       ]
      
      [`(and ,a ,b ,c ...)
       (define val (interp `(and ,a ,b) env)) 
       (interp `(and ,val ,@c) env)]

      ;or
      [`(or)
       #t]
      
      [`(or ,a ,b)
       (or
        (interp a env)
        (interp b env))]
      
      [`(or ,a ,b ,c ...)
       (define val (interp `(or ,a ,b) env)) 
       (interp `(or ,val ,@c) env)]

      ;cons
      [`(cons ,a ,b)
       (cons
        (interp a env)
        (interp b env))]

      [`(cons ,a ,b ,c ...)
       (define val (interp `(cons ,a ,b) env)) 
       (interp `(cons ,val ,@c) env)]

      ;list
      #;[`(((? number? ,a) (? number? ,b) ...))
       (if (equal? b '())
           (interp `(cons ,a ,b) env)
           (cons (interp a env)  (interp b env)))]
      
      [`(list ,a ,b ... )
       (if (equal? b '())
           (interp `(cons ,a ,b) env)
           (cons (interp a env)  (interp `(list ,@b) env)))]
       
      [`(car ,lst)
       (car (interp lst env))]

       [`(cdr ,lst)
       (cdr (interp lst env))]

      #;[`(car ,lst)
       (car lst)]

       #;[`(cdr ,lst)
       (cdr lst)]

      ;map
      [`(map ,e0 ,e1)
       (let* ([ve0 (interp e0 env)]
              [ve1 (interp e1 env)]
              )
         ;(interp (ve0 (first ve1)) env))
        (map (λ (x y) (interp `(,x ,y) env)) e0 e1))]


      [`(,efun ,earg)

       
       ; Evaluate both sub-expressions 
       (define vfun (interp efun env))  
       (define varg (interp earg env))
       ; the applied function must be a closure
       (match vfun
         [`(closure (lambda (,x) ,body) ,env+)
          (interp body  (hash-set env+ x varg))])]
       ; we extend the *closure's environment* and interp the body

      
      [`(,efun ,earg0 ,eargs ...)
      
         (define vfun (interp efun env))
         (define vargs (interp earg0 env))
         (match vfun

           ;if first arg is a closure
           [`(closure (lambda (,xs) ,body) ,env+)
            ;varg]
            (interp `(,body ,@eargs) (hash-set env+ xs vargs))]

           ; if it it s list of argumetns
           
         )]
          
      #;[`(,efun ,eargs ...)
      
         (define vfun (interp efun env))
         (define vargs (map (lambda (exp) ...) eargs))
         (match vfun

           ;if first arg is a closure
           [`(closure (lambda (,xs ...) ,body) ,env+)
            ;varg]
            (interp body (foldl (lambda (x v env+) ...) env+ xs vargs))]
           [`(closure (lambda ,x ,body) ,env+)
            ]

           ; if it it s list of argumetns
           
         )]
  

      [(? number? n)
       n]

      [(? integer? n)
       n]
      
      [(? symbol? x)
          ; Look up a variable in the current environment
          (hash-ref env x)]
      ; Untagged application case goes after all other forms

      
      [_ exp]
      ))
  
  (interp exp (hash)))

;(interp-ce '(+ 2 3 2))
#;(interp-ce `(map (lambda (m) (+ m 1))
          (list 2 3 4 5 6)))

#;(interp-ce '(let* ([U (lambda (u) (u u))]
          [Y (U (lambda (y) (lambda (f) (f (lambda (x) (((y y) f) x))))))]
          [fact (Y (lambda (fact) (lambda (n) (if (= n 0) 1 (* n (fact (- n 1)))))))])
     (fact 5)))
               ;fact))

#;(interp-ce `(let* ([U (lambda (u) (u u)) ]
                   ;[y x]
                   )
              U))
;(interp-ce `(add1 1))
;(interp-ce `((lambda(x) (lambda(y) y)) 1 x))
;(interp-ce `((lambda (x y) (+ x y))1 x))
;(interp-ce `((lambda(x y) y) 1 x))
;(interp-ce `((lambda(x y) y) 1 x))
;(interp-ce `(list 1 2 3 4))
#;(interp-ce '(let ([x 5] [y 7] [z 9])
              ;z))
              (let ([y x] [x y])
       x;(let ([z (- z y)])
         ;(+ x y z)
       )))

#;(interp-ce '(let ([x 5] [y 2])
              y))


;(interp-ce `(map * (list 1 2 3 4)))


;(interp-ce `())
;(interp-ce `1 2)




