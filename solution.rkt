;Jarosław Kadecki 332771

#lang racket
(require data/heap)

(provide sim? wire?
         (contract-out
          [make-sim        (-> sim?)]
          [sim-wait!       (-> sim? positive? void?)]
          [sim-time        (-> sim? real?)]
          [sim-add-action! (-> sim? positive? (-> any/c) void?)]

          [make-wire       (-> sim? wire?)]
          [wire-on-change! (-> wire? (-> any/c) void?)]
          [wire-value      (-> wire? boolean?)]
          [wire-set!       (-> wire? boolean? void?)]

          [bus-value (-> (listof wire?) natural?)]
          [bus-set!  (-> (listof wire?) natural? void?)]

          [gate-not  (-> wire? wire? void?)]
          [gate-and  (-> wire? wire? wire? void?)]
          [gate-nand (-> wire? wire? wire? void?)]
          [gate-or   (-> wire? wire? wire? void?)]
          [gate-nor  (-> wire? wire? wire? void?)]
          [gate-xor  (-> wire? wire? wire? void?)]

          [wire-not  (-> wire? wire?)]
          [wire-and  (-> wire? wire? wire?)]
          [wire-nand (-> wire? wire? wire?)]
          [wire-or   (-> wire? wire? wire?)]
          [wire-nor  (-> wire? wire? wire?)]
          [wire-xor  (-> wire? wire? wire?)]

          [flip-flop (-> wire? wire? wire? void?)]))

(struct sim ([current-time #:mutable] [action-queue #:mutable]))
(struct wire ([value #:mutable] [actions #:mutable] sim))

;make-sim zwraca symulację
(define (make-sim)
  (sim 0 (make-heap compare-actions)))

;sim-time zwraca current-time symulacji s
(define (sim-time s)
  (sim-current-time s))

;perform-actions wykonuje te akcje znajdujące się na kopcu h,
;których czas wywołania jest <= t
(define (perform-actions h t)
  (if (or (= (heap-count h) 0) (> (cdr (heap-min h)) t))
      (void)
      (begin
        ((car (heap-min h)))
        (heap-remove-min! h)
        (perform-actions h t))))

;sim-wait! zwiększa o n current-time symulacji s
;dodatkowo wywołuje funkcję perform-actions 
(define (sim-wait! s n)
  (if (<= n 0)
      (void)
      (let ([h (sim-action-queue s)])
        (begin
          (set-sim-current-time! s (+ (sim-time s) (if
                                                    (>= n 1)
                                                    1
                                                    n)))
          (perform-actions h (sim-time s))
          (sim-wait! s (- n 1))))))

;sim-add-action! dodaje na kopiec parę (cons funkcja czas-wykonania)
(define (sim-add-action! s n f)
  (heap-add! (sim-action-queue s) (cons f (+ n (sim-time s)))))

;compare-actoins porownuje funkcje ze względu na czas wykonania
(define (compare-actions a1 a2)
  (<= (cdr a1) (cdr a2)))

;make-wire zwraca przewód należący do symulacji s
(define (make-wire s)
  (wire #f null s))

;wire-set! przy zmianie wartości kabla wyołuje akcje do niego przypięte
(define (wire-set! w v)
  (if (eq? v (wire-value w))
      (void)
      (begin
        (set-wire-value! w v)
        (for-each (lambda (x) (x)) (wire-actions w)))))

;wire-on-change! dodaje do kabla akcje które mają się wywołać przy zmianie jego wartości,
;dodatkowow wywoluje akcję przy dodaniu jej.
(define (wire-on-change! w f)
  (set-wire-actions! w (cons f (wire-actions w)))
  (f))

;Procedury które definują akcje i dodają je do kabla funkcją wire-on-change!.
;Akcje są funkcjami dodającymi do kopca funkcje wire-set! ustawiające kabel wyjściowy w odpowiedni sposób.
(define (gate-not b a)
  (define (not-action)
      (sim-add-action! (wire-sim b)
                       1
                      (lambda ()
                        (wire-set! b (not (wire-value a))))))
  (wire-on-change! a not-action))

(define (gate-and c a b)
  (define (and-action)
    (sim-add-action! (wire-sim c)
                   1
                   (lambda ()
                     (wire-set! c (and (wire-value a) (wire-value b))))))
  (wire-on-change! a and-action)
  (wire-on-change! b and-action))

(define (gate-nand c a b)
  (define (nand-action)
    (sim-add-action! (wire-sim c)
                   1
                   (lambda ()
                     (wire-set! c (not (and (wire-value a) (wire-value b)))))))
  (wire-on-change! a nand-action)
  (wire-on-change! b nand-action))

(define (gate-or c a b)
  (define (or-action)
    (sim-add-action! (wire-sim c)
                   1
                   (lambda ()
                     (wire-set! c (or (wire-value a) (wire-value b))))))
  (wire-on-change! a or-action)
  (wire-on-change! b or-action))

(define (gate-nor c a b)
  (define (nor-action)
    (sim-add-action! (wire-sim c)
                   1
                   (lambda ()
                     (wire-set! c (not (or (wire-value a) (wire-value b)))))))
  (wire-on-change! a nor-action)
  (wire-on-change! b nor-action))

(define (gate-xor c a b)
  (define (xor-action)
    (sim-add-action! (wire-sim c)
                   2
                   (lambda ()
                     (wire-set! c (not (eq? (wire-value a) (wire-value b)))))))
  (wire-on-change! a xor-action)
  (wire-on-change! b xor-action))

;Łączenie tworzenia przewodów z tworzeniem bramki

(define (wire-not a)
  (define b (make-wire (wire-sim a)))
  (gate-not b a)
  b)

(define (wire-and a b)
  (define c (make-wire (wire-sim a)))
  (gate-and c a b)
  c)

(define (wire-nand a b)
  (define c (make-wire (wire-sim a)))
  (gate-nand c a b)
  c)

(define (wire-or a b)
  (define c (make-wire (wire-sim a)))
  (gate-or c a b)
  c)

(define (wire-nor a b)
  (define c (make-wire (wire-sim a)))
  (gate-nor c a b)
  c)

(define (wire-xor a b)
  (define c (make-wire (wire-sim a)))
  (gate-xor c a b)
  c)

(define (bus-set! wires value)
  (match wires
    ['() (void)]
    [(cons w wires)
     (begin
       (wire-set! w (= (modulo value 2) 1))
       (bus-set! wires (quotient value 2)))]))

(define (bus-value ws)
  (foldr (lambda (w value) (+ (if (wire-value w) 1 0) (* 2 value)))
         0
         ws))

(define (flip-flop out clk data)
  (define sim (wire-sim data))
  (define w1  (make-wire sim))
  (define w2  (make-wire sim))
  (define w3  (wire-nand (wire-and w1 clk) w2))
  (gate-nand w1 clk (wire-nand w2 w1))
  (gate-nand w2 w3 data)
  (gate-nand out w1 (wire-nand out w3)))

#|
(require rackunit)

(define s1 (make-sim))
(define a (make-wire s1))
(define b (make-wire s1))
(define c (make-wire s1))
(set-wire-value! a #t)
(gate-and c a b)
(gate-not b c)
(check-equal? (wire-value a) #t)
(check-equal? (wire-value b) #f)
(check-equal? (wire-value c) #f)

(sim-wait! s1 0)
(check-equal? (wire-value a) #t)
(check-equal? (wire-value b) #f)
(check-equal? (wire-value c) #f)

(sim-wait! s1 0.5)
(check-equal? (wire-value a) #t)
(check-equal? (wire-value b) #f)
(check-equal? (wire-value c) #f)

(sim-wait! s1 0.5)
(check-equal? (wire-value a) #t)
(check-equal? (wire-value b) #t)
(check-equal? (wire-value c) #t)

(sim-wait! s1 2)
(check-equal? (wire-value a) #t)
(check-equal? (wire-value b) #t)
(check-equal? (wire-value c) #t)


(define s2 (make-sim))

(define (make-counter n clk en)
  (if (= n 0)
      '()
      (let [(out (make-wire s2))]
        (flip-flop out clk (wire-xor en out))
        (cons out (make-counter (- n 1) clk (wire-and en out))))))

(define clk (make-wire s2))
(define en  (make-wire s2))
(define counter (make-counter 4 clk en))

(wire-set! en #t)

(define (tick)
  (wire-set! clk #t)
  (sim-wait! s2 20)
  (wire-set! clk #f)
  (sim-wait! s2 20)
  (bus-value counter))

(check-equal? (tick) 7)
(check-equal? (tick) 8)
(check-equal? (tick) 9)
(check-equal? (tick) 10)
(check-equal? (tick) 11)
(check-equal? (tick) 12)
(check-equal? (tick) 13)
(check-equal? (tick) 14)
(check-equal? (tick) 15)
(check-equal? (tick) 0)
(check-equal? (tick) 1)
|#