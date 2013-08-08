;; testing-example.scm ---

;; Author: Sergey Vinokurov <serg.foo@gmail.com>
;; Created: Thursday,  8 August 2013

(cond-expand
 (chibi
  (import (testing) (util)))
 (gambit
  #f)
 (else
  #f))


(define (ignore . args)
  #f)

(define (sample-test-runner)
  (let ((runner (%test-runner-alloc)))
    (test-runner-reset runner)
    (test-runner-on-group-begin!  runner test-on-group-begin)
    (test-runner-on-group-end!    runner ignore)
    (test-runner-on-final!        runner test-on-final)
    (test-runner-on-test-begin!   runner ignore)
    (test-runner-on-test-end!     runner test-on-test-end)
    (test-runner-on-bad-count!    runner ignore)
    (test-runner-on-bad-end-name! runner ignore)
    runner))

(define (test-on-group-begin runner suite-name count)
  (format #t "Starting ~a\n" suite-name))

(define (test-runner-reset-counts runner)
  (test-runner-pass-count! runner 0)
  (test-runner-fail-count! runner 0)
  (test-runner-xpass-count! runner 0)
  (test-runner-xfail-count! runner 0)
  (test-runner-skip-count! runner 0)
  (%test-runner-total-count! runner 0))



(define (test-on-final runner)
  (let ((passed (test-runner-pass-count runner))
        (failed (test-runner-fail-count runner))
        (xpass  (test-runner-xpass-count runner))
        (xfail  (test-runner-xfail-count runner))
        (total (%test-runner-total-count runner)))
    ;; (assert (and (= 0 xfail) (= 0 xpass))
    ;;         "No unexpected passes/failures should be present")
    (if (= 0 failed)
        (format #t "PASSED ~a TESTS" passed)
        (format #t "FALIED ~a TEST~a"
                failed
                (if (= failed 1) "" "S")))
    (format #t "\n\n"))
  (test-runner-reset-counts runner))

(define (test-on-test-end runner)
  ;; (define (maybe x y)
  ;;   (if x y ""))
  (define-syntax maybe
    (syntax-rules ()
      ((_ x y)
       (if x y ""))))
  (let ((kind (test-result-ref runner 'result-kind)))
    (if (eq? kind 'fail)
        (let* ((results (test-result-alist runner))
               (test-name   (assq 'test-name results))
               (source-file (assq 'source-file results))
               (source-line (assq 'source-line results))
               (source-form (assq 'source-form results)))
          (format #t "FAILED ~a:~a\n~a\n"
                  (maybe source-file (cdr source-file))
                  (maybe source-line (cdr source-line))
                  (cdr source-form))))))



(define (sample-tests)
  (test-runner-current (sample-test-runner))
  (test-group
   "group1"
   (test-assert (= 2 2))
   (test-assert (= (+ 1 2) 3))))




