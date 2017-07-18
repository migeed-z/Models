#lang racket
(require redex/reduction-semantics)
(require rackunit)

(define-language STLC
  (e ::= x (λ (x τ) e) (e e) v)
  (τ ::= Int (→ τ τ))
  (Γ ::= ((x τ) ...))
  (env ::= ((x v) ...))
  (v ::= integer ((λ (x) e) env))
  (x ::= variable-not-otherwise-mentioned))



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

;tests
(test-equal (term (lookup ((x 3)) x)) (term 3))
(test-equal (term (lookup ((y 3)) x)) #f)
(test-equal (term (lookup () x)) #f)

(test-equal (term (extend x 3 ())) (term ((x 3))))
(test-equal (term (extend x 4 ((x 3)))) (term ((x 4))))

(define eval
  (reduction-relation
   STLC
   #:domain (e env)
   (--> (x env)
        ((lookup env x) env))

   (--> ((λ (x τ) e_1) env)
        (((λ (x) e_1) env) env))

   (--> ((e_1 e_2) env)
        ((e_new e_2) env_new)
        (where ((e_new env_new)) ,(apply-reduction-relation eval (term (e_1 env)))))

   (--> ((((λ (x) e_1) env_lam) e) env)
      ((((λ (x) e_1) env_lam) e_2) env_new)
      (where ((e_2 env_new)) ,(apply-reduction-relation eval (term (e env)))))
     
   (--> ((((λ (x) e_1) env_lam) v) env)
       (e_1 (extend x v env_lam)))
   
   ))

(check-true (redex-match? STLC ((e_1 e_2) env) (term  ((((λ (x) x) ()) 3) ())) ))
(check-true (redex-match? STLC ((e v) env) (term  ((((λ (x) x) ()) 3) ()))))
(check-true (redex-match? STLC (e_1 e_2) (term ((λ (x Int) x) 3))))

(test--> eval (term (((λ (x Int) x) 3) ())) (term ((((λ (x) x) ()) 3) ())))
(test--> eval  (term ((((λ (x) x) ()) 3) ())) (term (x ((x 3)))))
(test--> eval  (term (x ((x 3)))) (term (3 ((x 3)))))

(test--> eval
         (term [([(λ (x) x) ()] ((λ (y Int) y) 3)) ()]) 
         (term [([(λ (x) x) ()] ([(λ (y) y) ()] 3)) ()]))

(test-->> eval
         (term [([(λ (x) x) ()] ((λ (y Int) y) 3)) ()]) 
         (term (3 ((x 3)))))


(define-judgment-form STLC
  #:mode (==>* I I O)
  #:contract (==>* e env v)

  [-------------------
  (==>* x env (lookup env x))]

  [-------------------
  (==>* integer env integer)]
  
  [(==>* e_1 env ((λ (x) e) env_lam))
   (==>* e_2 env v)
   (where env_new (extend x v env_lam))
   (==>* e env_new v_2)
   -------------------------
   (==>* (e_1 e_2) env v_2)]

  [--------------------------------------
   (==>* (λ (x τ) e) env ((λ (x) e) env))]
  )


(test-judgment-holds (==>*  x ((x 3)) 3))
(test-judgment-holds (==>* (λ (x Int) x) () ((λ (x) x) ())))


(test-judgment-holds (==>* ((λ (x Int) x) 3) () 3))



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


(test-results)