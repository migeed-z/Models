#lang racket

(require redex)
(require rackunit)

(define-language L
  (t ::= (→ t t)
          int
          ⊤
          ⊥)
  
  (e ::= 0
         x 
         (λ (x) e)
         (e e)
         (succ e))

  (q ::= (0 : int)
         (x : t)
         (λ (x) q : t)
         (q q : t)
         (succ q : t))  
  
  (x ::= variable-not-otherwise-mentioned)
  )

;subtype
(define-relation L
  subtype ⊆ t × t
  [(subtype t t)]
  [(subtype (→ t_1 t_2) (→ t_3 t_4))
   (and (subtype t_3 t_1)
        (subtype t_4 t_3))]
  [(subtype t ⊤)]
  [(subtype ⊥ t)])

;tests
(test-equal (term (subtype int int)) #t)
(test-equal (term (subtype (→ int int) (→ ⊥ ⊤))) #t)


(define-extended-language L+Γ L
  [Γ · (x : t Γ)])

;judgment
(define-judgment-form
  L+Γ
  #:mode (types I I)
  #:contract (types Γ q)

  [----------------  Rule1
   (types Γ (0 : int))]

  [(types Γ (q_1 : int))
   ------------------------ Rule2
   (types Γ (succ q_1 : int))]

   [
    (where t (lookup Γ x))
    ----------------------- "variable"
   (⊢ Γ x t)]

   [---------------------------- Rule3
   (types (x : t Γ) (x : t))] ;lookup -- where

  [(types (x : t_1 Γ) (q : t_2))
   ------------------------------------ Rule4
   (types Γ (λ (x) q : (→ t_1 t_2)))]



  [(types Γ q_1)
   (types Γ q_2)
   ------------------------------ Rule5
   (types Γ (q_1 q_2 : t_3))]


   [(subtype t_1 t_2)
    (types Γ (q_1 : t_1))
   ------------------------------------- Rule6
   (types Γ (q_1 : t_2))]


  )
  

;tests
(test-equal (judgment-holds (types · (0 : int))) #t)
(test-equal (judgment-holds (types · (x : int)) (types · ((x : int))) #t)


(test-results)

