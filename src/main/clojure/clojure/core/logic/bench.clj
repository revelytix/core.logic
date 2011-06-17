(ns clojure.core.logic.bench
  (:refer-clojure :exclude [reify inc ==])
  (:use clojure.core.logic.minikanren
        [clojure.core.logic.prelude :only [defne]]
        [clojure.core.logic.disequality :only [!=]])
  (:require [clojure.core.logic.nonrel :as nonrel]
            [clojure.core.logic.arithmetic :as a]))

;; =============================================================================
;; Utilities

(defn conso [a d l]
  (== (lcons a d) l))

(defne membero [x l]
  ([_ [x . ?tail]])
  ([_ [?head . ?tail]]
     (membero x ?tail)))

;; =============================================================================
;; flatten
;; =============================================================================

;; =============================================================================
;; append

(defne appendo [x y z]
  ([() _ y])
  ([[?a . ?d] _ [?a . ?r]] (appendo ?d y ?r)))

(defn appendo-fast [x y z]
  (conde
    ((if (or (lvar? x) (lvar? y))
       (all
        (== x ())
        (== y z))
       (if (= x ()) (== y z) u#)))
    ((if (or (lvar? x) (lvar? y))
       (exist [a d r]
         (conso a d x)
         (conso a r z)
         (appendo-fast d y r))
       (if (empty? x)
         u#
         (let [a (first x)
               d (rest x)]
           (exist [r]
             (conso a r z)
             (appendo-fast d y r))))))))

(comment
  (run 1 [q]
    (exist [x y]
      (appendo x y q)))
  
  ;; 1.4s
  (dotimes [_ 10]
    (time
     (dotimes [_ 1]
       (run 700 [q]
         (exist [x y]
           (appendo x y q))))))

  (run* [q]
    (appendo-fast [1 2] [3 4] q))

  ;; 100ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e4]
       (run* [q]
         (appendo-fast [1 2] [3 4] q)))))

  ;; 200ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e4]
       (run* [q]
         (appendo [1 2] [3 4] q)))))

  ;; if we do groudness testing, we optimize only a certain kinds of usages
  ;; common usages. for example optimizing reverse runs?
  )

;; =============================================================================
;; nrev
;; =============================================================================

(defne nrevo [l o]
  ([() ()])
  ([[?a . ?d] _]
     (exist [r]
       (nrevo ?d r)
       (appendo r [?a] o))))

(defn nrevo-fast [l o]
  (conde
    ((if (lvar? l)
       (all (== l ()) (== o ()))
       (if (empty? l) (== o ()) u#)))
    ((if (lvar? l)
       (exist [a d r]
         (conso a d l)
         (nrevo-fast d r)
         (appendo r [a] o))
       (if (empty? l) u#
           (let [a (first l)
                 d (rest l)]
             (exist [r]
               (nrevo-fast d r)
               (appendo r [a] o))))))))

(comment
  ;; we can run backwards, unlike Prolog
  (run 1 [q] (nrevo q (range 30)))
  (run 1 [q] (nrevo-fast (range 30) q))

  ;; SWI-Prolog 0.06-0.08s
  ;; ~4.1s
  (let [data (into [] (range 30))]
    (binding [*occurs-check* false]
      (dotimes [_ 5]
        (time
         (dotimes [_ 1e3]
           (run 1 [q] (nrevo data q)))))))

  ;; ~3s
  (let [data (into [] (range 30))]
    (binding [*occurs-check* false]
      (dotimes [_ 5]
        (time
         (dotimes [_ 1e3]
           (run 1 [q] (nrevo-fast data q)))))))

  ;; the LIPS are ridiculously high for SWI-Prolog
  ;; clearly nrev is a case that SWI-Prolog can optimize away
  )

;; =============================================================================
;; zebra
;; =============================================================================

(defn firsto [l a]
  (exist [d]
    (conso a d l)))

(defn resto [l d]
  (exist [a]
    (== (lcons a d) l)))

(defn membero [x l]
  (conde
    ((firsto l x))
    ((exist [r]
       (resto l r)
       (membero x r)))))

(defne righto [x y l]
  ([_ _ [x y . ?r]])
  ([_ _ [_ . ?r]] (righto x y ?r)))

(defn nexto [x y l]
  (conde
    ((righto x y l))
    ((righto y x l))))

(defn zebrao [hs]
  (all
   (== [(lvar) (lvar) [(lvar) (lvar) 'milk (lvar) (lvar)] (lvar) (lvar)] hs)                         
   (firsto hs ['norwegian (lvar) (lvar) (lvar) (lvar)])                         
   (nexto ['norwegian (lvar) (lvar) (lvar) (lvar)] [(lvar) (lvar) (lvar) (lvar) 'blue] hs)       
   (righto [(lvar) (lvar) (lvar) (lvar) 'ivory] [(lvar) (lvar) (lvar) (lvar) 'green] hs)         
   (membero ['englishman (lvar) (lvar) (lvar) 'red] hs)                    
   (membero [(lvar) 'kools (lvar) (lvar) 'yellow] hs)                      
   (membero ['spaniard (lvar) (lvar) 'dog (lvar)] hs)                      
   (membero [(lvar) (lvar) 'coffee (lvar) 'green] hs)                      
   (membero ['ukrainian (lvar) 'tea (lvar) (lvar)] hs)                     
   (membero [(lvar) 'lucky-strikes 'oj (lvar) (lvar)] hs)                  
   (membero ['japanese 'parliaments (lvar) (lvar) (lvar)] hs)              
   (membero [(lvar) 'oldgolds (lvar) 'snails (lvar)] hs)                   
   (nexto [(lvar) (lvar) (lvar) 'horse (lvar)] [(lvar) 'kools (lvar) (lvar) (lvar)] hs)          
   (nexto [(lvar) (lvar) (lvar) 'fox (lvar)] [(lvar) 'chesterfields (lvar) (lvar) (lvar)] hs)))

(comment
  ;; SWI-Prolog 6-8.5s
  ;; ~2.4s
  (binding [*occurs-check* false]
    (dotimes [_ 5]
      (time
       (dotimes [_ 1e3]
         (run 1 [q] (zebrao q))))))

  ;; < 3s
  (dotimes [_ 5]
    (time
     (dotimes [_ 1e3]
       (run 1 [q] (zebrao q)))))
  )

;; =============================================================================
;; fast-zebra

;; experiment with groundness checking here
;; avoid unification, avoid var creation, avoid consing

(defn firsto [l a]
  (exist [d]
    (conso a d l)))

(comment
  ;; if l is ground, we can use first
  ;; if a is ground, we can just do ==
  ;; if a is not ground, unify

  (defn firsto-fast [l a]
    (if (lvar? l)
      (exist [d]
        (conso a d l))
      (if (lvar? a)
        (== (first l) a)
        (if (= (first l) a) s# u#))))

  (defn resto-fast [l d]
    (if (lvar? l)
      (exist [a]
        (== (lcons a d) l))
      (if (lvar? d)
        (== (rest l) d)
        (if (= (rest l) d) s# u#))))

  (defn membero-fast [x l]
    (conde
      ((firsto-fast l x))
      ((if (lvar? l)
         (exist [r]
           (resto-fast l r)
           (membero-fast x r))
         (if-let [r (next l)]
           (membero-fast x r)
           u#)))))

  (defn righto-fast [x y l]
    (conde
      ((if (or (lvar? x) (lvar? y) (lvar? l))
         (exist [r]
           (== (llist x y r) l))
         (let [lx (first l)
               ly (second l)]
           (if (and (= x lx) (= y ly))
             s# u#))))
      ((cond
        (lvar? l) (exist [r]
                    (resto-fast l r)
                    (righto-fast x y r))
        (nil? l) u#
        :else (righto-fast x y (next l))))))

  (defn nexto-fast [x y l]
    (conde
      ((righto-fast x y l))
      ((righto-fast y x l))))

  (defn zebrao-fast [hs]
    (all
     (== [(lvar) (lvar) [(lvar) (lvar) 'milk (lvar) (lvar)] (lvar) (lvar)] hs)                         
     (firsto-fast hs ['norwegian (lvar) (lvar) (lvar) (lvar)])                         
     (nexto-fast ['norwegian (lvar) (lvar) (lvar) (lvar)] [(lvar) (lvar) (lvar) (lvar) 'blue] hs)       
     (righto-fast [(lvar) (lvar) (lvar) (lvar) 'ivory] [(lvar) (lvar) (lvar) (lvar) 'green] hs)         
     (membero-fast ['englishman (lvar) (lvar) (lvar) 'red] hs)                    
     (membero-fast [(lvar) 'kools (lvar) (lvar) 'yellow] hs)                      
     (membero-fast ['spaniard (lvar) (lvar) 'dog (lvar)] hs)                      
     (membero-fast [(lvar) (lvar) 'coffee (lvar) 'green] hs)                      
     (membero-fast ['ukrainian (lvar) 'tea (lvar) (lvar)] hs)                     
     (membero-fast [(lvar) 'lucky-strikes 'oj (lvar) (lvar)] hs)                  
     (membero-fast ['japanese 'parliaments (lvar) (lvar) (lvar)] hs)              
     (membero-fast [(lvar) 'oldgolds (lvar) 'snails (lvar)] hs)                   
     (nexto-fast [(lvar) (lvar) (lvar) 'horse (lvar)] [(lvar) 'kools (lvar) (lvar) (lvar)] hs)          
     (nexto-fast [(lvar) (lvar) (lvar) 'fox (lvar)] [(lvar) 'chesterfields (lvar) (lvar) (lvar)] hs)))

  (run* [q]
    (zebrao-fast q))

  ;; 2.2s, interesting slightly slower
  (binding [*occurs-check* false]
    (dotimes [_ 5]
      (time
       (dotimes [_ 1e3]
         (run 1 [q] (zebrao-fast q))))))

  (run* [q]
    (nexto-fast 'b 'c '[c a b]))

  (run* [q]
    (firsto-fast '[a b] 'a))

  ;; 486ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (exist [x]
           (== x 'a)
           (firsto '[a b] x))))))

  ;; 400ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (resto '[1 2 3 4] q)))))

  ;; 2.7s
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (membero 4 [1 2 3 4])))))

  ;; ~2s
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e4]
       (run* [q]
         (righto 'a 'b '[c d a b])))))

  ;; 263ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (exist [x]
           (== x 'a)
           (firsto-fast '[a b] x))))))

  ;; 270ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (resto-fast '[1 2 3 4] q)))))

  ;; 180ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (resto-fast [1 2 3 4] [2 3 4])))))

  (run* [q]
    (resto-fast [1 2 3 4] q))

  (run* [q]
    (firsto-fast [1 2 3 4] q))

  ;; 350ms!
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (membero-fast 4 [1 2 3 4])))))

  ;; 400ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (righto-fast 'a 'b '[c d a b])))))

  ;; 700ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e5]
       (run* [q]
         (nexto-fast 'a 'b '[c d a b])))))
  )

;; =============================================================================
;; nqueens

;; Bratko pg 103

(declare noattacko)

(defne nqueenso [l]
  ([()])
  ([[[?x ?y] . ?others]]
     (nqueenso ?others)
     (membero ?y [1 2 3 4 5 6 7 8])
     (noattacko [?x ?y] ?others)))

(defne noattacko [q others]
  ([_ ()])
  ([[?x ?y] [[?x1 ?y1] . ?others]]
     (!= ?y ?y1)
     (nonrel/project [?y ?y1 ?x ?x1]
       (!= (- ?y1 ?y) (- ?x1 ?x))
       (!= (- ?y1 ?y) (- ?x ?x1)))
     (noattacko [?x ?y] ?others)))

(defn solve-nqueens []
  (run* [q]
    (exist [y1 y2 y3 y4 y5 y6 y7 y8]
      (== q [[1 y1] [2 y2] [3 y3] [4 y4] [5 y5] [6 y6] [7 y7] [8 y8]])
      (nqueenso q))))

(comment
  (take 1 (solve-nqueens))

  ;; 92 solutions
  (count (solve-nqueens))

  ;; < 3s for 100x
  ;; about 18X slower that SWI
  (binding [*occurs-check* false]
    (dotimes [_ 5]
      (time
       (dotimes [_ 1]
         (take 1 (solve-nqueens))))))

  ;; ~550ms
  (binding [*occurs-check* false]
    (dotimes [_ 10]
      (time
       (dotimes [_ 1]
         (solve-nqueens)))))

  ;; ~610ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1]
       (solve-nqueens))))

  ;; nqueens benefits from constraints
  )

;; Bratko pg 344, constraint version

;; =============================================================================
;; send more money

(defne takeouto [x l y]
  ([_ [x . y] _])
  ([_ [?h . ?t] [?h . ?r]] (takeouto x ?t ?r)))
 
(defn digito [x l y]
  (takeouto x l y))
  
(defn first-digito [x l y]
  (all
   (digito x l y)
   (a/> x 0)))

(defne do-send-moolao [q l ll]
  ([[?send ?more ?money] _ _]
     (exist [s e n d m o r y
             l1 l2 l3 l4 l5 l6 l7 l8 l9]
       (first-digito s l l1)
       (first-digito m l1 l2)
       (digito e l2 l3)
       (digito n l3 l4)
       (digito d l4 l5)
       (digito o l5 l6)
       (digito r l6 l7)
       (digito y l7 l8)
       (nonrel/project [s e n d m o r y]
         (== ?send (+ (* s 1000) (* e 100) (* n 10) d))
         (== ?more (+ (* m 1000) (* o 100) (* r 10) e))
         (== ?money (+ (* m 10000) (* o 1000) (* n 100) (* e 10) y))
         (nonrel/project [?send ?more]
           (== ?money (+ ?send ?more)))))))

(defn send-money-quicklyo [send more money]
  (exist [l]
    (do-send-moolao [send more money] (range 10) l)))

(comment
  ;; ~16-17s, w/o occurs-check
  ;; SWI-Prolog takes 4s, so 3.8X faster
  ;; again I suspect the overhead here is from
  ;; interleaving, need to figure
  (time
   (binding [*occurs-check* false]
     (run 1 [q]
       (exist [send more money]
         (send-money-quicklyo send more money)
         (== [send more money] q)))))
  )

;; =============================================================================
;; Quick Sort

(declare partitiono)

(defne qsorto [l r r0]
  ([[] _ r])
  ([[?x . ?lr] _ _]
     (exist [l1 l2 r1]
       (partitiono ?lr ?x l1 l2)
       (qsorto l2 r1 r0)
       (qsorto l1 r (lcons ?x r1)))))

(defne partitiono [a b c d]
  ([[?x . ?l] _ [?x . ?l1] _]
     (nonrel/conda
      ((nonrel/project [?x b]
         (== (<= ?x b) true))
       (partition ?l b ?l1 d))
      (partition ?l b c d))))