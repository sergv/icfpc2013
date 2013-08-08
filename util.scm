;; util.scm ---

;; Author: Sergey Vinokurov <serg.foo@gmail.com>
;; Created: Thursday,  8 August 2013


(cond-expand
 (gambit
  (declare (r5rs-scheme)
           (inline)
           (inline-primitives)
           (standard-bindings)
           ;; (interrupts-enabled)
           ;; (debug)
           ;; (debug-location)
           ;; (debug-source)
           (debug-environments)
           (optimize-dead-local-variables)
           (proper-tail-calls))

  (define (assert . args)
    #f)

  ;; (define (pp x . args)
  ;;   (pretty-print x))
  )
 (chibi
  (import (srfi 16)))
 (else))

(define (format dest format-string . args)
  (define (interpret-format port fmt args)
    (cond ((null? fmt)
           #f)
          ((char=? (car fmt) #\~)
           (if (null? args)
             (error "number of format string arguments and actual argument list do not match" format-string args)
             (begin
               (display (car args) port)
               ;; (print port: port (car args))
               (interpret-format port (cddr fmt) (cdr args)))))
          (else
           (write-char (car fmt) port)
           (interpret-format port (cdr fmt) args))))
  (let ((fmt (string->list format-string)))
    (cond ((eq? dest #t)
           (interpret-format (current-output-port) fmt args))
          ((eq? dest #f)
           (let ((out (open-output-string)))
             (interpret-format out fmt args)
             (get-output-string out)))
          ((port? dest)
           (interpret-format dest fmt args))
          (else
           (error "format - dest must be #t, #f or port" dest)))))

(define (format-float n prec)
  (let* ((str (number->string n))
         (len (string-length str)))
    (let lp ((i (- len 1)))
         (cond
           ((negative? i)
            (string-append str "." (make-string prec #\0)))
           ((eqv? #\. (string-ref str i))
            (let ((diff (+ 1 (- prec (- len i)))))
              (cond
                ((positive? diff)
                 (string-append str (make-string diff #\0)))
                ((negative? diff)
                 (substring str 0 (+ i prec 1)))
                (else
                 str))))
           (else
            (lp (- i 1)))))))


(define (drop-while pred items)
  (cond ((null? items)
         '())
        ((pred items)
         (drop-while pred (cdr items)))
        (else
         items)))

(define (curry func . args)
  (lambda rest-args
    (apply func (append args rest-args))))

(define (remove-duplicates items-eq? items)
  (define (iter items result)
    (cond ((null? items)
           (reverse result))
          ((some? (lambda (x) (items-eq? (car items) x))
                  result)
           (iter (cdr items) result))
          (else
           (iter (cdr items) (cons (car items) result)))))
  (iter items '()))

(define (contains-duplicates? items-eq? items)
  (define (iter items)
    (cond ((null? items)
           #f)
          ((some? (lambda (x) (items-eq? (car items) x))
                  (cdr items))
           #t)
          (else
           (iter (cdr items)))))
  (iter items))

(define (join-list sep items)
    (cond ((null? items)
           "")
          ((null? (cdr items))
           (car items))
          (else
           (string-append (car items)
                          sep
                          (join-list sep (cdr items))))))


(define (all? pred items)
  (foldl (lambda (prev x)
           (and prev
                (pred x)))
         #t
         items))

(define (some? pred items)
  (foldl (lambda (prev x)
           (or prev
               (pred x)))
         #f
         items))

(define (foldr func init items)
  (if (null? items)
      init
      (func (car items)
            (foldr func init (cdr items)))))

(define (foldl func init items)
  (define (iter result items)
    (if (null? items)
        result
        (iter (func result (car items)) (cdr items))))
  (iter init items))

(define (foldl1 func items)
  (if (null? items)
      (error "foldl1 - invalid items sequence")
      (foldl func (car items) (cdr items))))



(define-syntax when
  (syntax-rules ()
    ((when cond body ...)
     (if cond
       (begin
         body ...)
       #f))))

(define-syntax when-let
  (syntax-rules ()
    ((when-let (var val) body ...)
     (let ((var val))
       (when var
         body ...)))))


;; (define-syntax aif
;;   (er-macro-transformer
;;    (lambda (expr rename compare)
;;      `(let ((it ,(cadr expr)))
;;         (if it
;;           ,(caddr expr)
;;           ,@(if (null? (cdddr expr))
;;               '()
;;               (list (cadddr expr))))))))

;; (define-syntax awhen
;;   (er-macro-transformer
;;    (lambda (expr rename compare)
;;      `(let ((it ,(cadr expr)))
;;         (if it
;;           ,(caddr expr)
;;           ,@(if (null? (cdddr expr))
;;               '()
;;               (list (cadddr expr))))))))




