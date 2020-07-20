#lang racket/base

(require (for-syntax syntax/parse/lib/function-header)
         data/gvector
         math/base
         racket/contract/base
         racket/contract/region
         racket/math
         rebellion/binary/bit
         rebellion/collection/list
         rebellion/collection/vector
         rebellion/type/enum
         rebellion/type/object
         syntax/parse/define)

;@------------------------------------------------------------------------------
;; Comment this definition out to enable contracts

(define-simple-macro (define/contract header contract body ...)
  (define header body ...))

;@------------------------------------------------------------------------------
;; Use this instead of define to search for loops that run forever

(define-simple-macro (define/loop-logging header:function-header body ...)
  (begin
    (define call-counter (box 0))
    (define header
      (set-box! call-counter (add1 (unbox call-counter)))
      (when (power-of-two? (unbox call-counter))
        (printf "~a called ~a times\n" header.name (unbox call-counter)))
      body ...)))

;@------------------------------------------------------------------------------
;; Type definitions that need to be at the top so they can be used in contracts.

(struct test-case
  (prefix
   max-size
   print-results?
   [status #:mutable]
   choices
   depth-parameter)
  #:constructor-name constructor:test-case)

(define-enum-type case-status (overrun invalid valid interesting))

;@------------------------------------------------------------------------------

(define/contract (run-test test
                           #:max-examples [max-examples 100]
                           #:quiet? [quiet? #f])
  (->* ((-> test-case? void?)) (#:max-examples natural? #:quiet? boolean?)
       void?)

  (define/contract (mark-failures-interesting case)
    (-> test-case? void?)
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

(define/contract (cache-test-function test-function)
  (-> (-> test-case? void?) (-> gvector? case-status?))
  (λ (choices)
    (define num-choices (gvector-count choices))
    (define case (test-case-for-choices choices))
    (test-function case)
    (unless (case-status? (test-case-status case))
      (error "Assertion failed."))
    (test-case-status case)))

(define/contract (proper-cache-test-function test-function)
  (-> (-> test-case? void?) (-> gvector? case-status?))
  (define tree (make-hash))
  (λ (choices)
    (define num-choices (gvector-count choices))
    (define/contract (loop node previous-cached? previous-known? i)
      (-> hash? boolean? boolean? natural? (values any/c boolean? boolean?))
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
       (unless (case-status? (test-case-status case))
         (error "Assertion failed."))
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

(define/contract (make-testing-state
                  #:test-function test-function
                  #:max-examples max-examples)
  (-> #:test-function (-> test-case? void?) #:max-examples natural?
      testing-state?)
  (constructor:testing-state test-function max-examples 0 0 #f #f #f))

(define/contract (testing-state-test-function state case)
  (-> testing-state? test-case? void?)
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

(define/contract (testing-state-run! state)
  (-> testing-state? void?)
  (testing-state-generate! state)
  (testing-state-shrink! state))

(define/contract (testing-state-should-keep-generating? state)
  (-> testing-state? boolean?)
  (and (not (testing-state-test-is-trivial? state))
       (not (testing-state-result state))
       (< (testing-state-valid-test-cases state)
          (testing-state-max-examples state))
       (< (testing-state-calls state)
          (* (testing-state-max-examples state) 10))))

(define/contract (testing-state-generate! state)
  (-> testing-state? void?)
  (when (and (testing-state-should-keep-generating? state)
             (or (not (testing-state-best-scoring state))
                 (<= (testing-state-valid-test-cases state)
                     (quotient (testing-state-max-examples state) 2))))
    (define case (make-test-case #:prefix (list) #:max-size buffer-size))
    (testing-state-test-function state case)))

(define/contract (testing-state-shrink! state)
  (-> testing-state? void?)
  (cond
    [(not (testing-state-result state)) (void)]
    [else
     (define/contract cached
       (-> gvector? case-status?)
       (cache-test-function
        (λ (case) (testing-state-test-function state case))))
     (define/contract (consider choices)
       (-> gvector? boolean?)
       (equal? (cached choices) interesting))
     (unless (consider (testing-state-result state))
       (error "Assertion failed."))

     (define/loop-logging (shrink-loop old-prev)
       (when (not (equal? old-prev (testing-state-result state)))
         (define prev (testing-state-result state))

         ;; First try deleting each choice we made in chunks
         (for ([k (in-list (list 8 4 2 1))])
           (define/loop-logging (delete-loop i)
             (when (>= i 0)
               (define size (gvector-count (testing-state-result state)))
               (define attempt
                 (gvector-delete-range (testing-state-result state) i (+ i k)))
               (unless (< (gvector-count attempt) size)
                 (error "Assertion failed."))
               (if (consider attempt) (delete-loop i) (delete-loop (sub1 i)))))
           (delete-loop (- (gvector-count (testing-state-result state)) k 1)))

         ;; Now try replacing blocks of choices with zeroes
         (for ([k (in-list (list 8 4 2 1))])
           (define/loop-logging (zero-loop i)
             (when (>= i 0)
               (define attempt
                 (gvector-set-range-to-zero
                  (testing-state-result state) i (+ i k)))
               (if (consider attempt)
                   (zero-loop (- i k))
                   (zero-loop (sub1 i)))))
           (zero-loop (- (gvector-count (testing-state-result state)) k 1)))

         ;; Now try replacing each choice with a smaller value  by doing a
         ;; binary search.
         (define max-i (sub1 (gvector-count (testing-state-result state))))
         (for ([i (in-range max-i -1 -1)])
           (define/loop-logging (replace-loop lo hi)
             (when (< (add1 lo) hi)
               (define mid (+ lo (quotient (- hi lo) 2)))
               (define attempt (gvector-set (testing-state-result state) i mid))
               (if (consider attempt)
                   (replace-loop lo mid)
                   (replace-loop mid hi))))
           (replace-loop 0 (gvector-ref (testing-state-result state) i)))

         (shrink-loop prev)))

     (shrink-loop #f)]))

(define buffer-size (* 8 1024))

(define/contract (choices< choices1 choices2)
  (-> gvector? gvector? boolean?)
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

(define (gvector-delete-range gvector start [stop* +inf.0])
  (define stop (min stop* (gvector-count gvector)))
  (define size (- stop start))
  (define modified (make-gvector-with-bugfix #:capacity size))
  (for ([i (in-range start stop)]
        [j (in-naturals)])
    (gvector-set! modified j (gvector-ref gvector i)))
  modified)

(define (gvector-set-range-to-zero gvector start [stop* +inf.0])
  (define stop (min stop* (gvector-count gvector)))
  (define size (gvector-count gvector))
  (define modified (make-gvector-with-bugfix #:capacity size))
  (for ([i (in-range 0 start)])
    (gvector-set! modified i (gvector-ref gvector i)))
  (for ([i (in-range start stop)])
    (gvector-set! modified i 0))
  (for ([i (in-range stop size)])
    (gvector-set! modified i (gvector-ref gvector i)))
  modified)

(define (gvector-set gvector position replacement)
  (define size (gvector-count gvector))
  (define modified (make-gvector-with-bugfix #:capacity size))
  (for ([i (in-range 0 position)])
    (gvector-set! modified i (gvector-ref gvector i)))
  (gvector-set! modified position replacement)
  (for ([i (in-range (add1 position) size)])
    (gvector-set! modified i (gvector-ref gvector i)))
  modified)

;; TODO(https://github.com/racket/data/issues/18): fix make-gvector
(define (make-gvector-with-bugfix #:capacity [capacity 10])
  (if (zero? capacity) (gvector) (make-gvector #:capacity capacity)))

;@------------------------------------------------------------------------------
;; Tests

(module+ test
  (run-test
   (λ (case)
     (define ints
       (test-case-any case (possible-lists (possible-integers 0 10000))))
     (unless (<= (apply + ints) 1000)
       (raise "Failure!")))))
