#lang racket
(require redex/reduction-semantics)

(define-language STLC
  (e ::= x (λ (x τ) e) (e e) v)
  (τ ::= Int (→ τ τ))
  (Γ ::= ((x τ) ...))
  (env ::= ((x v) ...))
  (v ::= integer ((λ (x) e) env))
  (x ::= variable-not-otherwise-mentioned))

; (lookup env x) retrieves x's value from env
(define-metafunction STLC
  lookup : env x -> any
  [(lookup ((x_1 v_1)  ... (x v) (x_2 v_2) ...) x)
   v
   (side-condition (not (member (term x) (term (x_1 ...)))))]
   [(lookup env x) ;defined diff. in the tutorial why???
     #f])


(define-metafunction STLC
    extend : x v env -> any
    [(extend x v ((x_1 v_1) ... (x v_2) (x_3 v_3) ...)) ((x_1 v_1) ... (x v) (x_3 v_3) ...)]
    [(extend x v ((x_1 v_1) ...)) ((x v) (x_1 v_1) ...)]
  )



(define eval
  (reduction-relation
   STLC
   #:domain (e env)
   (--> (x env)
        ((lookup env x) env))

   (--> (integer env) (integer env))

   (--> ((λ (x τ) e_1) env)
        (((λ (x) e_1) env) env))

   (--> ((e_1 e_2) env)
        ((e_new e_2) env)
        (where ((e_new env)) ,(apply-reduction-relation eval (term (e_1 env)))))
   
   
 #| (--> ((((λ (x) e_1) env_lam) e) env_2)
       ((((λ (x) e_1) env_lam) e_new) env_2)
       (where ((e_new env)) ,(apply-reduction-relation eval (term (e_1 env_2))))) 
       
 |#

    (--> ((((λ (x) e_1) env_lam) v) env)
       (e_1 (extend x v env_lam))
       ) 
   
   ))

(redex-match? STLC (e env)  (term (((λ (x Int) x) 3) ())))

(test--> eval (term (5 ())) (term (5 ())))
(test--> eval (term ((λ (x Int) x) ()))  (term (((λ (x) x) ()) ())) )
(test--> eval (term (((λ (x Int) x) 3) ())) (term ((((λ (x) x) ()) 3) ())))
(test--> eval  (term ((((λ (x) x) ()) 3) ())) (term (x ((x 3)))))
(test--> eval  (term (x ((x 3)))) (term (3 ((x 3)))))


;(test-equal (term (eval (term 5) (term ()))) 5)

;tests
(test-equal (term (lookup ((x 3)) x)) (term 3))
(test-equal (term (lookup ((y 3)) x)) #f)
(test-equal (term (lookup () x)) #f)

(test-equal (term (extend x 3 ())) (term ((x 3))))
(test-equal (term (extend x 4 ((x 3)))) (term ((x 4))))


(define Γ? (redex-match? STLC Γ))

(test-equal (Γ? (term [(x Int)])) #t)
(test-equal (Γ? (term [(x (→ Int Int))])) #t)
(test-equal (Γ? (term ((x Int) (x (→ Int Int))))) #t)


(define-judgment-form STLC
  #:mode (infer-type I I O)
  #:contract (infer-type Γ e τ)

 [--------------------------
  (infer-type Γ integer Int)]
  
  [(infer-type Γ e_1 (→ τ_2 τ_3))
   (infer-type Γ e_2 τ_2)
   ------------------------------
   (infer-type Γ (e_1 e_2) τ_3)]
  
 [(where ((x_3 τ_3) ...) Γ)
  (where Γ_1 ((x_1 τ_1) (x_3 τ_3) ...))
  (infer-type Γ_1 e τ_2)
 -------------------------------------
  (infer-type Γ (λ (x_1 τ_1) e) (→ τ_1 τ_2))]

  [(where ((x_1 τ_1) ... (x τ) (x_2 τ_2) ...) Γ)
  ----------------------------------------------
   (infer-type Γ x τ)]
  )

(test-judgment-holds (infer-type () 3 Int))
(test-judgment-holds (infer-type () (λ (x Int) x) (→ Int Int)))
(test-judgment-holds (infer-type () ((λ (x Int) x) 3) Int))


; (side-condition ,(printf "HI gamma is ~a~n" (term Γ_1)))





(test-results)