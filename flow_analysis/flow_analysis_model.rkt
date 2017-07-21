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
         ((λ (x) q) : t)
         ((q q) : t)
         ((succ q) : t))
  
  (x ::= variable-not-otherwise-mentioned)
  (Γ ::= ((x t) ...))

  )
(define q? (redex-match? L q))

(define-metafunction L
  lookup : Γ x -> any
  [(lookup ((x_1 t_1)  ... (x t) (x_2 t_2) ...) x)
   t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
   [(lookup Γ x) 
     #f])

(define-metafunction L
    extend : x t Γ -> Γ
    [(extend x t ((x_1 t_1) ... (x t_2) (x_3 t_3) ...)) ((x_1 t_1) ... (x t) (x_3 t_3) ...)]
    [(extend x t ((x_1 t_1) ...)) ((x t) (x_1 t_1) ...)]
  )

;tests
(test-equal (term (lookup ((x int)) x)) (term int))
(test-equal (term (lookup ((y int)) x)) #f)
(test-equal (term (lookup () x)) #f)
(test-equal (term (extend x int ()) ) (term ((x int))) )
(test-equal (term (extend x int ((x ⊤)))) (term ((x int))))

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


;judgment
(define-judgment-form
  L
  #:mode (types I I)
  #:contract (types Γ q)

  [(side-condition ,(printf "1\n"))
   ----------------  Rule1
   (types Γ (0 : int))]

 
  [(side-condition ,(printf "2\n"))
   (where (_ : t_body) q)
   (where int t_body)
   (types Γ q)
   ------------------------ Rule2
   (types Γ ((succ q) : int))]

   [(side-condition ,(printf "3\n"))
    (where t (lookup Γ x))
    ----------------------- Rule3
   (types Γ (x : t))]

  [(side-condition ,(printf "4\n"))
   (where (_ : t_2) q)
   (types (extend x t_1 Γ) q)
   ------------------------------------ Rule4
   (types Γ ((λ (x) q) : (→ t_1 t_2)))]

  [(side-condition ,(printf "5\n"))
   (where (_ : t_1) q_2)
   (where (_ : (→ t_1 t_2)) q_1)
   (types Γ q_2)
   (types Γ q_1)   
   ------------------------------ Rule5
   (types Γ ((q_1 q_2) : t_2))]

    
 #;[(subtype t_1 t_2)
   (types Γ (q_1 : t_1))
   ;(where x_new ,(gensym 'x))
   ------------------------------------- Rule6
   (types Γ (q_1 : t_2))] 
  )

(check-true (redex-match? L q (term ((succ (0 : int)) : int))))
(check-true (redex-match? L q (term ((λ (x) (x : int)) : (→ int int)) )))
(check-true (redex-match? L q (term (x : int))))
(check-true (redex-match? L ((q_1 q_2) : t) (term ((((λ (x) (x : int)) : (→ int int))
                                                (0 : int)) : int) )))
(check-true (q? (term ((λ (x) (((x : (→ int int)) (0 : int)) : int))
                                     : (→ (→ int int) int)))))


;tests
(test-judgment-holds (types () (0 : int)))
(test-judgment-holds (types () ((succ (0 : int)) : int)))
(test-judgment-holds (types ((x int)) (x : int)))
(test-judgment-holds (types () ((λ (x) (x : int)) : (→ int int))))
(test-judgment-holds (types () ((((λ (x) (x : int)) : (→ int int)) (0 : int)) : int)))
(test-judgment-holds (types () ((λ (x) (((x : (→ int int)) (0 : int)) : int)) : (→ (→ int int) int))))

;xe and ye (judgment)

(test-results)

