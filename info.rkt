#lang info

(define collection "miniracksis")

(define scribblings
  (list (list "main.scrbl"
              (list 'multi-page)
              (list 'library)
              "miniracksis")))

(define deps
  (list "base"
        "rebellion"))

(define build-deps
  (list "racket-doc"
        "rackunit-lib"
        "scribble-lib"))
