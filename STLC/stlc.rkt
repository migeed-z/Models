#lang racket
(require redex/reduction-semantics)


(define-language STLC
  (e ::= x (λ (x τ) e) (e e) integer)
  (τ ::= Int (→ τ τ))
  (Γ ::= ((x τ) ...))
  (x ::= variable-not-otherwise-mentioned))

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

(test-equal (judgment-holds (infer-type () 3 Int)) #t)
(test-equal (judgment-holds (infer-type () (λ (x Int) x) (→ Int Int))) #t)
(test-equal (judgment-holds (infer-type () ((λ (x Int) x) 3) Int)) #t)


; (side-condition ,(printf "HI gamma is ~a~n" (term Γ_1)))


  

(test-results)