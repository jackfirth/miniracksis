#lang racket/base

(require data/gvector
         rebellion/binary/bit
         rebellion/collection/list
         rebellion/collection/vector
         rebellion/type/enum
         rebellion/type/object)

;@------------------------------------------------------------------------------

(define (run-test test
                  #:max-examples [max-examples 100]
                  #:quiet? [quiet? #f])

  (define (mark-failures-interesting case)
    (with-handlers
        ([(λ (_) #t)
          (λ (raised-value)
            (when (test-case-status case)
              (raise raised-value))
            (test-case-mark-status! case interesting))])
      (test case)))

  (define state
    (make-testing-state
     #:test-function mark-failures-interesting
     #:max-examples max-examples))

  (testing-state-run! state)

  (when (zero? (testing-state-valid-test-cases state))
    (raise (unsatisfiable)))

  (define result (testing-state-result state))
  (when result
    (test (test-case-for-choices result #:print-results? (not quiet?)))))

;@------------------------------------------------------------------------------
;; Possibilities

(define-object-type possibility (producer)
  #:constructor-name constructor:possibility)

(define (make-possibility producer #:name [name #f])
  (constructor:possibility #:producer producer #:name name))

(define (possibility-map possibility map-function)
  (make-possibility
   (λ (case) (map-function (test-case-any case possibility)))
   #:name 'mapped))

(define (possible-integers m n)
  (define (produce case) (+ m (test-case-choice case (- n m))))
  (make-possibility produce #:name 'possible-integers))

(define (possible-lists element-possibility)
  (define (produce case)
    (if (test-case-weighted case 0.9)
        (cons (test-case-any case element-possibility) (produce case))
        empty-list))
  (make-possibility produce #:name 'possible-lists))

(define (possible-value value)
  (make-possibility (λ (_) value) #:name 'possible-value))

(define impossibility
  (make-possibility (λ (case) (test-case-reject! case)) #:name 'impossibility))

;@------------------------------------------------------------------------------
;; Test cases

(struct test-case
  (prefix
   max-size
   print-results?
   [status #:mutable]
   choices
   depth-parameter)
  #:constructor-name constructor:test-case)

(define (test-case-for-choices choices #:print-results? [print-results? #f])
  (define choice-vector (sequence->vector choices))
  (define max-size (vector-length choice-vector))
  (make-test-case
   #:prefix choice-vector
   #:max-size max-size
   #:print-results? print-results?))

(define (make-test-case
         #:prefix prefix
         #:max-size [max-size +inf.0]
         #:print-results? [print-results? #f])
  (define prefix-vector (sequence->vector prefix))
  (constructor:test-case
   prefix-vector
   max-size
   print-results?
   #f
   (gvector)
   (make-parameter 0)))

(define (test-case-choice case n)
  (define result
    (test-case-make-choice case n (λ () (random n))))
  (when (test-case-should-print? case)
    (printf "choice(~a) = ~a\n" n result))
  result)

(define (test-case-weighted case p)
  (define (random-function) (boolean->bit (<= (random) p)))
  (define result (bit->boolean (test-case-make-choice case 1 random-function)))
  (when (test-case-should-print? case)
    (printf "weighted(~a) = ~a\n" p result))
  result)

(define (test-case-reject! case)
  (test-case-mark-status! case invalid))

(define (test-case-assume! case precondition)
  (unless (precondition) (test-case-reject! case)))

(define (test-case-any case possibility)
  (define depth ((test-case-depth-parameter case)))
  (define result
    (parameterize ([(test-case-depth-parameter case) (add1 depth)])
      ((possibility-producer possibility) case)))
  (when (test-case-should-print? case)
    (printf "any(~a) = ~a\n" possibility result))
  result)

(define (test-case-mark-status! case status)
  (when (test-case-status case)
    (raise (frozen)))
  (set-test-case-status! case status)
  (raise (stop-test)))

(define (test-case-should-print? case)
  (and (test-case-print-results? case)
       (zero? ((test-case-depth-parameter case)))))

(define (test-case-make-choice case n random-function)
  (when (test-case-status case)
    (raise (frozen)))
  (define choices (test-case-choices case))
  (define num-choices (gvector-count choices))
  (when (>= num-choices (test-case-max-size case))
    (test-case-mark-status! case overrun))
  (define prefix (test-case-prefix case))
  (define result
    (if (< num-choices (vector-length prefix))
        (vector-ref prefix num-choices)
        (random-function)))
  (gvector-add! choices result)
  (when (> result n)
    (test-case-mark-status! case invalid))
  result)

;@------------------------------------------------------------------------------
;; Test function caching

(define (cache-test-function test-function)
  (define tree (make-hash))
  (λ (choices)
    (define num-choices (gvector-count choices))
    (define (loop node previous-cached? previous-known? i)
      (cond
        [(equal? i num-choices)
         (values node previous-cached? previous-known?)]
        [else
         (define c (gvector-ref choices i))
         (cond
           [(not (hash-has-key? node c)) (values node #f #f)]
           [else
            (define next-node (hash-ref node c))
            (cond
              [(case-status? next-node)
               (when (equal? next-node overrun)
                 (error "Assertion failed."))
               (values next-node #t #t)]
              [else (loop next-node #f #t (add1 i))])])]))
    (define-values (node cached? known?) (loop tree #f #t 0))
    (cond
      [cached? node]
      [(not known?) overrun]
      [else
       (define case (test-case-for-choices choices))
       (test-function case)
       (invariant-assertion case-status? (test-case-status case))
       (define case-choices (test-case-choices case))
       (define num-case-choices (gvector-count case-choices))
       (for/fold ([node tree] #:result (void))
                 ([c (in-gvector case-choices)] [i (in-naturals)])
         (cond
           [(or (< (add1 i) num-case-choices)
                (equal? (test-case-status case) overrun))
            (hash-ref node c make-hash)]
           [else
            (hash-set! node c (test-case-status case))
            node]))
       (test-case-status case)])))

;@------------------------------------------------------------------------------
;; Testing states

(struct testing-state
  (internal-test-function
   max-examples
   [valid-test-cases #:mutable]
   [calls #:mutable]
   [result #:mutable]
   [best-scoring #:mutable]
   [test-is-trivial? #:mutable])
  #:constructor-name constructor:testing-state)

(define (make-testing-state
         #:test-function test-function
         #:max-examples max-examples)
  (constructor:testing-state test-function max-examples 0 0 #f #f #f))

(define (testing-state-test-function state case)
  (with-handlers ([exn:stop-test? void])
    ((testing-state-internal-test-function state) case))
  (unless (test-case-status case)
    (set-test-case-status! case valid))
  (set-testing-state-calls! state (add1 (testing-state-calls state)))
  (define choices (test-case-choices case))
  (define num-choices (gvector-count choices))
  (when (and (not (equal? (test-case-status case) invalid))
             (zero? num-choices))
    (set-testing-state-test-is-trivial?! state #t))
  (when (or (equal? (test-case-status case) valid)
            (equal? (test-case-status case) interesting))
    (set-testing-state-valid-test-cases!
     state (add1 (testing-state-valid-test-cases state))))
  (when (and (equal? (test-case-status case) interesting)
             (or (not (testing-state-result state))
                 (choices< choices (testing-state-result state))))
    (set-testing-state-result! state choices)))

(define (testing-state-run! state)
  (testing-state-generate! state)
  (testing-state-shrink! state))

(define (testing-state-should-keep-generating? state)
  (and (not (testing-state-test-is-trivial? state))
       (not (testing-state-result state))
       (< (testing-state-valid-test-cases state)
          (testing-state-max-examples state))
       (< (testing-state-calls state)
          (* (testing-state-max-examples state) 10))))

(define (testing-state-generate! state)
  (when (and (testing-state-should-keep-generating? state)
             (or (not (testing-state-best-scoring state))
                 (<= (testing-state-valid-test-cases state)
                     (quotient (testing-state-max-examples state) 2))))
    (define case (make-test-case #:prefix (list) #:max-size buffer-size))
    (testing-state-test-function state case)))

(define (testing-state-shrink! state)
  (cond
    [(testing-state-result state) (testing-state-result state)]
    [(not (testing-state-result state)) (void)]
    [else
     (define cached
       (cache-test-function
        (λ (case) (testing-state-test-function state case))))
     (define (consider choices) (equal? (cached choices) interesting))
     (unless (consider (testing-state-result state))
       (error "Assertion failed."))

     (define (loop old-prev)
       (when (not (equal? old-prev (testing-state-result state)))
         (define prev (testing-state-result state))

         ;; First try deleting each choice we made in chunks
         (for ([k (in-list (list 8 4 2 1))])
           (define (delete-loop i)
             (when (>= i 0)
               (define attempt (make-gvector (+ i (- k i))))
               (for ([j (in-range i)])
                 (define v (gvector-ref (testing-state-result state) j))
                 (gvector-set! attempt j v))
               (for ([j (in-range (+ i k)
                                  (gvector-count (testing-state-result state)))]
                     [j* (in-naturals i)])
                 (define v (gvector-ref (testing-state-result state) j))
                 (gvector-set! attempt j* v))
               (unless (< (gvector-count attempt)
                          (gvector-count (testing-state-result state)))
                 (error "Assertion failed."))
               (if (consider attempt) (delete-loop i) (delete-loop (sub1 i)))))
           (delete-loop (- (gvector-count (testing-state-result state)) k 1)))

         ;; Now try replacing blocks of choices with zeroes
         (for ([k (in-list (list 8 4 2 1))])
           (define (zero-loop i)
             (when (>= i 0)
               (define attempt
                 (make-gvector (gvector-count (testing-state-result state))))
               (for ([j (in-range
                         (gvector-count (testing-state-result state)))])
                 (define v
                   (if (or (< j i) (>= j (+ i k)))
                       (gvector-ref (testing-state-result state) j)
                       0))
                 (gvector-set! attempt j v))
               (if (consider attempt)
                   (zero-loop (- i k))
                   (zero-loop (sub1 i)))))
           (zero-loop (- (gvector-count (testing-state-result state)) k 1)))

         ;; Now try replacing each choice with a smaller value  by doing a
         ;; binary search.
         (define max-i (sub1 (gvector-count (testing-state-result state))))
         (for ([i (in-range max-i -1 -1)])
           (define (replace-loop lo hi)
             (when (< (add1 lo) hi)
               (define mid (quotient (+ lo (- hi lo)) 2))
               (define attempt
                 (make-gvector (gvector-count (testing-state-result state))))
               (for ([j (in-range
                         (gvector-count (testing-state-result state)))])
                 (define v
                   (if (equal? j i)
                       mid
                       (gvector-ref (testing-state-result state))))
                 (gvector-set! attempt j v))
               (if (consider attempt)
                   (replace-loop lo mid)
                   (replace-loop mid hi))))
           (replace-loop 0 (gvector-ref (testing-state-result state) i)))))

     (loop #f)]))

(define buffer-size (* 8 1024))

(define (choices< choices1 choices2)
  (define count1 (gvector-count choices1))
  (define count2 (gvector-count choices2))
  (define (elements< i)
    (cond
      [(equal? i count1) #f]
      [else
       (define x (gvector-ref choices1 i))
       (define y (gvector-ref choices2 i))
       (or (< x y) (and (= x y) (elements< (add1 i))))]))
  (or (< count1 count2) (and (= count1 count2) (elements< 0))))

;@------------------------------------------------------------------------------

(struct exn:frozen exn:fail ())

(define (frozen)
  (exn:frozen "This test case is frozen." (current-continuation-marks)))

(struct exn:unsatisfiable exn:fail ())

(define (unsatisfiable)
  (exn:unsatisfiable
   "This test case is unsatisfiable." (current-continuation-marks)))

(struct exn:stop-test exn:fail ())

(define (stop-test)
  (exn:stop-test "This test case is stopped." (current-continuation-marks)))

(define-enum-type case-status (overrun invalid valid interesting))

(define (overrun? v) (equal? v overrun))

;@------------------------------------------------------------------------------
;; Tests

(module+ test
  (require (only-in rackunit
                    check-equal?
                    check-exn))

  (define stdout (open-output-string 'stdout))
  (check-exn
   (λ (e) (equal? e "Failure!"))
   (λ ()
     (parameterize ([current-output-port stdout])
       (run-test
        (λ (case)
          (define ints
            (test-case-any case (possible-lists (possible-integers 0 10000))))
          (unless (<= (apply + ints) 1000)
            (raise "Failure!")))))))
  (check-equal? (get-output-string stdout)
                "any(#<possibility:possible-lists>) = (1001)"))
  