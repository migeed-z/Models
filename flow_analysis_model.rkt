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

(redex-match L q (term (0 : int)))

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

  [----------------  ;(1)
   (types Γ (0 : int))]

  [(types Γ (q_1 : int))
   ------------------------ ;(2)
   (types Γ (succ q_1 : int))]

  [(types (x : t Γ) (x : t))
   ---------------------------- ;(3)
   (types Γ (x : t))]

  [(types (x : t_1 Γ) (q : t_2))
   ------------------------------------  ;(4)
   (types Γ (λ (x) q : (→ t_1 t_2)))]

  [(types Γ (q_1 : (→ t_1 t_2)))
   (types Γ (q_2 : t_1))
   ------------------------------   ;(5)
   (types Γ ((q_1 : t_1) q_2 : t_2))]

  [(types Γ (q_1 : t_1))
   (subtype t_1 t_2)
   ------------------------------ ;(6)
   (types Γ ((q_1 : t_1) : t_2))]
   
  )
  

(test-results)

