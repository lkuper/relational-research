;; Computation type:
;;   Computations which may fail or throw exceptions
;; Binding strategy:

;; Failure records information about the cause/location of the
;; failure. Failure values bypass the bound function, other values are
;; used as inputs to the bound function.

;; Useful for: Building computations from sequences of functions that may
;; fail or using exception handling to structure error handling.

;; Zero and plus: Zero is represented by an empty error and the plus
;; operation executes its second argument if the first fails.

;; Example type: 	Either String

;; a Motivation

;; The Error monad (also called the Exception monad) embodies the
;; strategy of combining computations that can throw exceptions by
;; bypassing bound functions from the point an exception is thrown to the
;; point that it is handled.

;; The MonadError class is parameterized over the type of error
;; information and the monad type constructor. It is common to use Either
;; String as the monad type constructor for an error monad in which error
;; descriptions take the form of strings. In that case and many other
;; common cases the resulting monad is already defined as an instance of
;; the MonadError class. You can also define your own error type and/or
;; use a monad type constructor other than Either String or Either
;; IOError. In these cases you will have to explicitly define instances
;; of the Error and/or MonadError classes.

;; The definition of the MonadError class below uses multi-parameter type
;; classes and funDeps, which are language extensions not found in
;; standard Haskell 98. You don't need to understand them to take
;; advantage of the MonadError class.

;; class Error a where
;;     noMsg :: a
;;     strMsg :: String -> a

;; class (Monad m) => MonadError e m | m -> e where
;;     throwError :: e -> m a
;;     catchError :: m a -> (e -> m a) -> m a

;; throwError is used within a monadic computation to begin exception processing. catchError provides a handler function to handle previous errors and return to normal execution. A common idiom is:

;; do { action1; action2; action3 } `catchError` handler 

;; where the action functions can call throwError. Note that handler and
;; the do-block must have the same return type.

;; The definition of the Either e type constructor as an instance of the
;; MonadError class is straightforward. Following convention, Left is
;; used for error values and Right is used for non-error (right) values.

;; instance MonadError (Either e) where 
;;     throwError = Left 
;;     (Left e) `catchError` handler = handler e 
;;     a        `catchError` _       = a
    
;; Example

;; Here is an example that demonstrates the use of a custom Error data
;; type with the ErrorMonad's throwError and catchError exception
;; mechanism. The example attempts to parse hexadecimal numbers and
;; throws an exception if an invalid character is encountered. We use a
;; custom Error data type to record the location of the parse error. The
;; exception is caught by a calling function and handled by printing an
;; informative error message.

;; Code available in example12.hs

;; -- This is the type of our parse error representation.
;; data ParseError = Err {location::Int, reason::String}

;; -- We make it an instance of the Error class
;; instance Error ParseError where
;;   noMsg    = Err 0 "Parse Error"
;;   strMsg s = Err 0 s

;; -- For our monad type constructor, we use Either ParseError
;; -- which represents failure using Left ParseError or a
;; -- successful result of type a using Right a.
;; type ParseMonad = Either ParseError

;; -- parseHexDigit attempts to convert a single hex digit into
;; -- an Integer in the ParseMonad monad and throws an error on an
;; -- invalid character
;; parseHexDigit :: Char -> Int -> ParseMonad Integer
;; parseHexDigit c idx = if isHexDigit c then
;;                         return (toInteger (digitToInt c))
;;                       else
;;                         throwerror
;;                           (Err idx ("Invalid character '" ++ [c] ++ "'"))

;; -- parseHex parses a string containing a hexadecimal number into
;; -- an Integer in the ParseMonad monad.  A parse error from parseHexDigit
;; -- will cause an exceptional return from parseHex.
;; parseHex :: String -> ParseMonad Integer
;; parseHex s = parseHex' s 0 1
;;   where parseHex' []      val _   = return val
;;         parseHex' (c:cs)  val idx = do d <- parseHexDigit c idx
;;                                        parseHex' cs ((val * 16) + d) (idx + 1)

;; ------------------------------------------------------------------------

(define unit
  (lambda (a)
    `(right . ,a)))

(define bind
  (lambda (c f)
    (case (car c)
      ((left) c)
      ((right) (f (cdr c))))))

(define-syntax do*
  (syntax-rules ()
    ((_ ((x0 comp0)) comp-body) (bind comp0 (lambda (x0) comp-body)))
    ((_ ((x0 comp0) (x comp) ...) comp-body)
     (bind comp0 (lambda (x0) (do* ((x comp) ...) comp-body))))))

(define throw
  (lambda (exception)
    `(LEFT . ,exception)))

(define catch
  (lambda (c handler)
    (case (car c)
      ((left) (handler (cdr c)))
      ((right) c))))

(define parse-hex ;; string -> ...
  (let ((hex-char->int 
          (lambda (c pos)
            (case c
              ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (unit (- (char->integer c) 48)))
              ((#\a) (unit 10))
              ((#\b) (unit 11))
              ((#\c) (unit 12))
              ((#\d) (unit 13))
              ((#\e) (unit 14))
              ((#\f) (unit 15))
              (else (throw
                     `(,pos . ,(string-append "bad char " (string c)))))))))
    (lambda (s)
      (let loop ((s (string->list s)) (val 0) (pos 0))
        (cond
          ((null? s) (unit val))
          (else (do* ((d (hex-char->int (car s) pos)))
                  (loop (cdr s) (+ (* val 16) d) (add1 pos)))))))))

;;; There are basically two parse monads; one that has unit taking
;;; a string and one that has unit taking an integer.  Here's one where
;;; unit is taking a string.

;; -- convert takes a String containing a hexadecimal representation of
;; -- a number to a String containing a decimal representation of that
;; -- number.  A parse error on the input String will generate a
;; -- descriptive error message as the output String.
;; convert :: String -> String
;; convert s
;;   = let (right str) = do {n <- parseHex s
;;                           ;
;;                           return $ toString n}
;;                       `catchError`
;;                       printError
;;     in str
;;   where printError e
;;   = return $ "At index " ++ (show (location e)) ++ ":" ++ (reason e)

(define convert ;; String -> String
  (let ((print (lambda (e)
                 (let ((position (car e)) (reason (cdr e)))
                   (unit
                     (string-append (format "At index ~s : " position) reason))))))
    (lambda (shex)
      (let ((result (catch
                      (do* ((n (parse-hex shex)))
                        (unit (format "~s" n)))
                      print)))
        (case (car result)
          ((right) (cdr result)))))))

> (convert "a5x21b")
"At index 2 : bad char x"
> (convert "a5f21b")
"10875419"
