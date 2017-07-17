#lang racket
(require redex/reduction-semantics)


(define-language STLC
  (e ::= x (λ (x τ) e) (e e) v)
  (τ ::= Int (→ τ τ))
  (Γ ::= ((x τ) ...))
  (env ::= ((x v) ...))
  (x ::= variable-not-otherwise-mentioned)
  (v ::= integer ((λ (x) e) env)))

; (lookup env x) retrieves x's value from env
(define-metafunction STLC
  [(lookup ((x_1 v_1) ... (x v) (x_2 v_2) ...) x)
   v
   (side-condition (not (member (term x) (term (x_1 ...)))))]
   [(lookup ((x_2 v_2) ...) x) ;defined diff. in the tutorial why???
     #f])

;tests
(test-equal (term (lookup ((x 3)) x)) (term 3))
(test-equal (term (lookup ((y 3)) x)) #f)
(test-equal (term (lookup () x)) #f)


#|
(define eval
  (reduction-relation
   STLC
   (--> 
        )))|#



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