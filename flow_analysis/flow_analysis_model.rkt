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

  (YE ::= 0
          x 
          (λ (x) YE)
          (YE YE)
          (succ YE))
  
  (XE ::= x) ;set of bound variables

  (v ::= XE
         YE)
  (W ::= (v -> v (λ (x) YE))
          W*)

  (W+ ::= (v -> v (YE YE))
           W*)

  (W* ::= Int
          v)
  
  (Const ::= (W ≤ W+)
             (Const ...))

  (P-or-F ::= ((W ≤ W+)(W ≤ W+))
               #f)
  (Bool ::= #t
            #f)
  
  (x ::= variable-not-otherwise-mentioned)
  (Γ ::= ((x t) ...)))




(define-metafunction L
  ;returns the first occurrence of transitive pair
  trans-aux : (Const ...) (W ≤ W+) -> P-or-F
  [(trans-aux () (W ≤ W+)) #f]
  [(trans-aux ((W* ≤ W+) (W_c ≤ W+_d) ...) (W ≤ W*)) ((W ≤ W*) (W* ≤ W+))]
  [(trans-aux ((W ≤ W*) (W_c ≤ W+_d) ...) (W* ≤ W+)) ((W ≤ W*)  (W* ≤ W+))]
  [(trans-aux ((W ≤ W+) (W_c ≤ W+_d) ...) (W_other ≤ W+_other)) (trans-aux  ((W_c ≤ W+_d) ...)
                                                                         (W_other ≤ W+_other))]
  )
        
       
(define-metafunction L
  ;scans all const. for a transitive pair
  get-trans : (Const ...) -> P-or-F
  [(get-trans ()) #f]
  
  [(get-trans  ((W_1 ≤ W+_1) (W_3 ≤ W+_3) ...))
   ,(or 
        (term P-or-F)
        (term (get-trans ((W_3 ≤ W+_3) ...))))

   (where P-or-F (trans-aux ((W_3 ≤ W+_3) ...) (W_1 ≤ W+_1)))])


(test-equal (term (get-trans(((succ x) ≤ x)
                      ((x -> x (λ (x) x)) ≤ ((λ (x) x)  -> 0 ((λ (x) x) 0))))))
            (term #f))

(test-equal (term (get-trans (((succ x) ≤ x)
                             (x ≤ 0))))
            (term  (((succ x) ≤ x)
                             (x ≤ 0))))


(test-equal (term (get-trans (((succ x) ≤ x)
                             (x ≤ 0)
                             (0 ≤ x))))
            (term  (((succ x) ≤ x)
                             (x ≤ 0))))

(test-equal (term (get-trans (((succ x) ≤ x)
                             (x ≤ 0)
                             ((succ x) ≤ 0)
                             (0 ≤ x))))
            (term  (((succ x) ≤ x)
                             (x ≤ 0))))

(define-metafunction L
  ;given T(e) returns T'(e)
  T- : Const -> Const
          
  [(T- ((W_1 ≤ W_2+)... ((v_s1 -> v_t1 (λ (x) YE)) ≤ (v_s2 -> v_t2 (YE_g YE_h))) (W ≤ W+) ...))  
     (T- ((W_1 ≤ W_2+)... ((v_s1 -> v_t1 (λ (x) YE)) ≤ (v_s2 -> v_t2 (YE_g YE_h)))
          (W ≤ W+) ...
          (v_s2 ≤ v_s1)
          (v_t1 ≤ v_t2)))

     (side-condition (and (not (member (term (v_s2 ≤ v_s1))
                                  (term (((v_s1 -> v_t1 (λ (x) YE)) ≤ (v_s2 -> v_t2 (YE_g YE_h)))
                                         (W ≤ W+) ...))))
                          (not (member (term (v_t1 ≤ v_t2))
                                  (term (((v_s1 -> v_t1 (λ (x) YE)) ≤ (v_s2 -> v_t2 (YE_g YE_h)))
                                         (W ≤ W+) ...))))))]

 [(T- (Const ...))
  (T- ((W ≤ W+) Const ...))
  (where ((W ≤ W*)(W* ≤ W+)) (get-trans (Const ...)))
  (side-condition (not (member (term (W ≤ W+)) (term (Const ...)))))]
  

  
  [(T- Const) Const])


(check-true (redex-match? L ((W_1 ≤ W_2+)...
                             ((v_s1 -> v_t1 (λ (x) YE)) ≤ (v_s2 -> v_t2 (YE_g YE_h)))
                              (W ≤ W+) ...)
                          (term (((succ x) ≤ x)
                                 ((x -> x (λ (x) x)) ≤ ((λ (x) x)  -> 0 ((λ (x) x) 0)))))))

(check-true (redex-match? L Const (term ((x -> x (λ (x) x)) ≤ ((λ (x) x) -> 0 ((λ (x) x) 0))))))

(check-true (redex-match? L Const (term (((0 ≤ Int) (Int ≤ 0))))))
(check-true (redex-match? L (W ≤ W+) (term (Int ≤ Int))))
(check-true (redex-match? L  ((W ≤ W+)... (W_1 ≤ W+_1) ... (W_2 ≤ W+_2))
                             (term ((x ≤ (succ x)) ((succ x) ≤ Int)))))
(check-true (redex-match? L  (((v_s1 -> v_t1 (λ (x) YE)) ≤ (v_s2 -> v_t2 (YE_g YE_h))) (W ≤ W+) ...)
          (term              (((x -> 0 (λ (x) 0)) ≤ (x -> 0 ((λ (x) 0) 0))) ))))


(define-syntax-rule (test-set= t0  t1)
  (test-equal t0 t1 #:equiv set=?))

(test-set= (term  (T- (((x -> 0 (λ (x) 0)) ≤ (x -> 0 ((λ (x) 0) 0)))) ))
            (term  (((x -> 0 (λ (x) 0)) ≤ (x -> 0 ((λ (x) 0) 0)))
                    (x ≤ x)
                    (0 ≤ 0))))
(test-set= (term (T-((0 ≤ Int) (Int ≤ 0)))) (term((0 ≤ Int) (Int ≤ 0) (0 ≤ 0))))
(test-equal (term (T-((x ≤ (succ x)) ((succ x) ≤ Int))))
            (term ((x ≤ (succ x)) ((succ x) ≤ Int) (x ≤ Int))) #:equiv set=?)

(test-set= 
            (term (T-(((succ x) ≤ x)
                      ((x -> x (λ (x) x)) ≤ ((λ (x) x)  -> 0 ((λ (x) x) 0))))))
            (term (((succ x) ≤ x)
                    ((x -> x (λ (x) x)) ≤ ((λ (x) x)  -> 0 ((λ (x) x) 0)))
                   ((λ (x) x) ≤ x)
                   ((succ x) ≤ 0)
                   (x ≤ 0))))
                  
(define-metafunction L
  ;generate a system of constraints for e
  T : e -> Const
  [(T  0) ((Int ≤ 0))]
  [(T x) ((x ≤ x))]
  
  [(T (succ e)) ,(append (term ((Int ≤ (succ e))
                                       (e  ≤ Int)))
                                 (term (T e)))]
  
  [(T (λ (x) e)) ,(append  (term (((x -> e (λ (x) e)) ≤  (λ (x) e))))
                                   (term (T e)))]
  
  [(T (e_g e_h)) ,(append (term ((e_g ≤ (e_h -> (e_g e_h) (e_g e_h)))))
                                 (term (T e_g))
                                 (term (T e_h)))]) 
  

(test-equal (term (T 0)) (term ((Int ≤ 0))))
(test-equal (term (T (succ 0)))
            (term ((Int ≤ (succ 0)) (0 ≤ Int) (Int ≤ 0))))

(test-equal (term (T x)) (term ((x ≤ x))))

(test-equal (term (T (λ (x) 0)))
            (term (((x -> 0 (λ (x) 0)) ≤  (λ (x) 0)) (Int ≤ 0))))

(test-equal (term (T ((λ (x) x) 0)))
            (term (((λ (x) x) ≤ (0 -> ((λ (x) x) 0) ((λ (x) x) 0)))
                    ((x -> x (λ (x) x)) ≤ (λ (x) x))
                    (x ≤ x)
                    (Int ≤ 0))))

(test-equal (term (T (λ (x) (x (succ x)))))
(term (((x -> (x (succ x)) (λ (x) (x (succ x)))) ≤ (λ (x) (x (succ x))))
  (x ≤ ((succ x) -> (x (succ x)) (x (succ x))))
  (x ≤ x)
  (Int ≤ (succ x))
  (x ≤ Int)
  (x ≤ x))))


(define-metafunction L
  ;Is this set of constraints typable?
  typable? : (Const ...) -> any
  [(typable? ()) #t]
  [(typable? ((W ≤ W+) (W_1 ≤ W+_1) ...))
   ,(and (and
        (not (redex-match? L ((v_1 -> v_2 (λ (x) YE)) ≤ Int) (term (W ≤ W+))))
        (not (redex-match? L (Int ≤ (v_1 -> v_2 (YE_1 YE_2))) (term (W ≤ W+)))))
        (term (typable? ((W_1 ≤ W+_1) ...))))])


(test-equal (term (typable? ())) #t)
(test-equal (term (typable?
                   (((λ (x) x) ≤ (0 -> ((λ (x) x) 0) ((λ (x) x) 0)))
                    ((x -> x (λ (x) x)) ≤ (λ (x) x))
                    (x ≤ x)
                    (Int ≤ 0)))) #t)

(test-equal (term (typable? ((Int ≤ 0)
                             (x ≤ x)
                             (Int ≤ (0 -> ((λ (x) x) 0) ((λ (x) x) 0))) ))) #f)
                             
(test-equal (term (typable?
                   ((Int ≤ (0 -> ((λ (x) x) 0) ((λ (x) x) 0)))
                    ((x -> x (λ (x) x)) ≤ (λ (x) x))
                    (x ≤ x)
                    (Int ≤ 0)))) #f)


(define-metafunction L
  ;returns a set of bound variables
  ;assumes e is λ_converted (all bound var. are unique)
  get_xe : e -> any
  [(get_xe 0) []]
  [(get_xe x) []]
  [(get_xe (λ (x) e)) ,(append (term [x]) (term (get_xe e)))]
  [(get_xe (e_1 e_2)) ,(append (term (get_xe e_1)) (term (get_xe e_2)))]
  [(get_xe (succ e))  (get_xe e)])

(test-equal (term (get_xe 0)) (term []))
(test-equal (term (get_xe x)) (term []))
(test-equal (term (get_xe (λ (x) 0))) (term [x]))
(test-equal (term (get_xe (λ (x) (λ (y) y)))) (term [x y]))
(test-equal (term (get_xe ((λ (x) x) 0))) (term [x]))
(test-equal (term (get_xe (succ x))) (term []))

(define-metafunction L
  ;returns a set of all expressions e 
  get_ye : e -> any
  [(get_ye 0) [0]]
  [(get_ye x) [x]]
  [(get_ye (λ (x) e)) ,(append (term [(λ (x) e)])
                               (term (get_ye e)))]
  [(get_ye (e_1 e_2)) ,(append (term [(e_1 e_2)])
                               (term (get_ye e_1))
                               (term (get_ye e_2)))]
  [(get_ye (succ e))  ,(append (term [(succ e)])
                               (term (get_ye e)))])


(test-equal (term (get_ye 0)) (term [0]))
(test-equal (term (get_ye x)) (term [x]))
(test-equal (term (get_ye (λ (x) 0))) (term [(λ (x) 0) 0]))
(test-equal (term (get_ye (λ (x) (λ (y) y)))) (term [(λ (x) (λ (y) y)) (λ (y) y) y]))
(test-equal (term (get_xe ((λ (x) x) 0))) (term [x]))
(test-equal (term (get_xe (succ x))) (term []))

(define e? (redex-match? L e))
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

  [;(side-condition ,(printf "1\n"))
   ----------------  Rule1
   (types Γ (0 : int))]

 
  [(where (_ : t_body) q)
   (where int t_body)
   (types Γ q)
   ------------------------ Rule2
   (types Γ ((succ q) : int))]

   [(where t (lookup Γ x))
    ----------------------- Rule3
   (types Γ (x : t))]

  [(where (_ : t_2) q)
   (types (extend x t_1 Γ) q)
   ------------------------------------ Rule4
   (types Γ ((λ (x) q) : (→ t_1 t_2)))]

  [(where (_ : t_1) q_2)
   (where (_ : (→ t_1 t_2)) q_1)
   (types Γ q_2)
   (types Γ q_1)   
   ------------------------------ Rule5
   (types Γ ((q_1 q_2) : t_2))]

    
 #;[(subtype t_1 t_2)
   (types Γ (q_1 : t_1))
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


;xe and ye
;(where x_new ,(gensym 'x))
;(side-condition ,(printf "3\n"))

(test-results)

