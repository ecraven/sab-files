(load-option 'sxml->xml)
(load-option 'string-replace-string)
(load-option 'parse-real)

(define *debug* #f)
(define *indent* 0)
(define *ignore-missing-includes* #t)
(define *inline-pictures* #t)
(define-structure myport data offset)
(define-structure mytable symbol-table)

(define *references* '())
(define *commands* '())
(define *pictures* '())
(define *environments* '())
(define *function-specs* '())
(define *example-record-markers* '())

(define *paragraph-marker-string* "**[[THISISAPARAGRAPH]]**")
(define *line-break-string* " ")

(define (port-seek port position)
  (set-myport-offset! port position))

(define (myport-peek port)
  (vector-8b-ref (myport-data port) (myport-offset port)))

(define (myport-eof? port)
  (= (myport-offset port) (vector-8b-length (myport-data port))))

(define (hex n)
  (string "#x" (number->string n 16)))

(define (vector-every fun vector)
  (let loop ((i 0))
    (if (= i (- (vector-length vector) 1))
        (fun (vector-ref vector i))
        (if (fun (vector-ref vector i))
            (loop (+ i 1))
            #f))))

(define (read-file-content filename)
  "Read the entire file into a string."
  (let* ((size (file-length filename))
         (str (make-string size)))
    (if (= size (read-string! str (open-input-file filename)))
        str
        (error "cannot read entire file" filename))))

(define (read-8-bit-number port)
  (let* ((o (myport-offset port))
         (d (vector-8b-ref (myport-data port) o)))
    (set-myport-offset! port (+ o 1))
    d))

(define (read-substring len stream)
  (let ((p (myport-offset stream)))
    (let ((res (substring (myport-data stream) p (+ p len))))
      (set-myport-offset! stream (+ p len))
      res)))

(define (read-16-bit-number stream)
  (let* ((low (read-8-bit-number stream))
         (high (read-8-bit-number stream)))
    (+ low (* (expt 2 8) high))))

(define (read-32-bit-number stream)
  (let* ((low (read-16-bit-number stream))
         (high (read-16-bit-number stream)))
    (+ low (* (expt 2 16) high))))

(define (collect-n n thunk)
  (let loop ((i 0)
             (res '()))
    (if (= i n)
        (reverse res)
        (loop (+ i 1)
              (cons (thunk) res)))))

;; based on nsage/sab-file.lisp


(define *sab-code-names* '(=sab-code-record=
                           =sab-code-type-symbol=
                           =sab-code-function-spec=
                           =sab-code-field-alist=
                           =sab-code-field-name=
                           =sab-code-envr=
                           =sab-code-envr-name=
                           =sab-code-envr-mods=
                           =sab-code-attribute-name=
                           =sab-code-contents-list=
                           =sab-code-fixnum=
                           =sab-code-string=
                           =sab-code-long-string=
                           =sab-code-list=
                           =sab-code-symbol-ref=
                           =sab-code-uninterned-symbol-def=
                           =sab-code-sage-pkg-symbol-def=
                           =sab-code-pkg-symbol-def=
                           =sab-code-doc-pkg-symbol-def=
                           =sab-code-read-from-string=
                           =sab-code-simple-command=
                           =sab-code-command=
                           =sab-code-simple-command-name=
                           =sab-code-command-name=
                           =sab-code-macro-call=
                           =sab-code-macro-name=
                           =sab-code-macro-arglist=
                           =sab-code-location-pair=
                           =sab-code-index=
                           =sab-code-callee-triple-list=
                           =sab-code-index-item=
                           =sab-code-file-attribute-alist=
                           =sab-code-keyword-pkg-symbol-def=
                           =sab-code-reference=
                           =sab-code-fat-string=
                           =sab-code-unique-id=
                           =sab-code-modification-history=
                           =sab-code-token-list=
                           =sab-code-file-attribute-string=
                           =sab-code-callee-4ple-list=
                           =sab-code-picture=
                           =sab-code-8-bit-array=
                           =sab-code-example-record-marker=
                           =sab-code-extensible-reference=
                           =sab-code-extensible-reference-take-two=
                           =sab-code-character=))

(define *sab-code-reader-dispatch* (make-vector (length *sab-code-names*) #f))

(define (read-sab-thing port table required-sab-type)
  (let ((code (read-8-bit-number port)))
    (when *debug*
      (format #t "~a#x~a read-sab-thing: ~s (~s)~%" (make-string *indent* #\space) (number->string (myport-offset port) 16) (list-ref *sab-code-names* code) (if required-sab-type (list-ref *sab-code-names* required-sab-type) "any"))
      (set! *indent* (+ *indent* 2)))
    (when required-sab-type
      (unless (= code required-sab-type)
        (error "sab code" code (list-ref *sab-code-names* code) "instead of" required-sab-type (list-ref *sab-code-names* required-sab-type))))
    (let ((function (vector-ref *sab-code-reader-dispatch* code)))
      (if function
          (let ((res (function port table)))
            (when *debug*
              (format #t "~a -> ~s~%" (make-string *indent* #\space) (if (procedure? res) (res list) (if (and (string? res) (> (string-length res) 128))  "......" res)))
              (set! *indent* (- *indent* 2)))
            res)
          (error "no sab reader for" code (list-ref *sab-code-names* code) "at" (string "#x" (number->string (myport-offset port) 16)))))))

(define-syntax define-sab-reader
  (syntax-rules ()
    ((define-sab-reader sym params body0 body ...)
     (begin
       (define sym (list-index (lambda (x) (eq? x 'sym)) *sab-code-names*))
       (vector-set! *sab-code-reader-dispatch* sym (lambda params body0 body ...))))))

(define (sage-record-callee-type record callee-id)
  (let ((c (hash-table/get (sage-record-callees record) callee-id #f)))
    (if c (second c) #f)))

(define-structure sage-record name type fields index callees)
(define-sab-reader =sab-code-record= (stream table)
  (let* ((name (read-sab-thing stream table #f))
         (type (read-sab-thing stream table =sab-code-type-symbol=))
         (field-alist (read-sab-thing stream table =sab-code-field-alist=)))
    ;; (fixup-old-doc-symbol-topic name field-alist)
    (let ((record (make-sage-record name type field-alist #f '())))
      (hash-table/put! *records-by-name* (if (sage-function-spec? name) (sage-function-spec-name name) name) record)
      record)))

(define-sab-reader =sab-code-field-alist= (stream table)
  (let ((n (read-16-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= n i)
          (reverse res)
          (receive (field-name sab-code)
              (read-sab-thing stream table =sab-code-field-name=)
            (loop (+ i 1)
                  (cons (list field-name (read-sab-thing stream table sab-code)) res)))))))

(define-sab-reader =sab-code-envr-mods= (stream table)
  (let ((n (read-16-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= i n)
          (reverse res)
          (let* ((name (read-sab-thing stream table =sab-code-attribute-name=))
                 (val (read-sab-thing stream table #f)))
            (loop (+ i 1)
                  (cons (list name val) res)))))))

(define-sab-reader =sab-code-file-attribute-alist= (stream table)
  (let ((alist (read-sab-thing stream table #f)))
    (unless (and (pair? alist)
                 (every (lambda (el) (and (pair? el) (symbol? (car el)))) alist))
      (error "not an alist with symbols in all CARs" alist))
    alist))

(define-sab-reader =sab-code-list= (stream table)
  (let ((n (read-16-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= i n)
          (reverse res)
          (loop (+ i 1)
                (cons (read-sab-thing stream table #f) res))))))

(define-sab-reader =sab-code-contents-list= (stream table)
  (let ((n (read-16-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= i n)
          (reverse res)
          (loop (+ i 1)
                (cons (read-sab-thing stream table #f) res))))))

(define (read-sab-symbol stream table prefix)
  (let ((sym (string->symbol (string-downcase (string-append prefix (read-sab-string stream table))))))
    (set-mytable-symbol-table! table (append (mytable-symbol-table table) (list sym)))
    sym))

(define-sab-reader =sab-code-keyword-pkg-symbol-def= (stream table)
  (read-sab-symbol stream table ":"))

(define-sab-reader =sab-code-uninterned-symbol-def= (stream table)
  (read-sab-symbol stream table "uninterned:"))

(define-sab-reader =sab-code-doc-pkg-symbol-def= (stream table)
  (read-sab-symbol stream table "doc:"))

(define-sab-reader =sab-code-sage-pkg-symbol-def= (stream table)
  (read-sab-symbol stream table ""))

(define-sab-reader =sab-code-pkg-symbol-def= (stream table)
  (let ((pkg (read-sab-string stream table)))
    (read-sab-symbol stream table (string-append pkg ":"))))

(define-sab-reader =sab-code-string= (stream table)
  (let* ((size (read-8-bit-number stream)))
    ;;(read-substring size stream)
    ;;(string-replace-string-all (string-replace-string-all (read-substring size stream) "\215\215" *paragraph-marker-string*) "\215" *line-break-string*)
    (recode-genera-characters (read-substring size stream))
    ))

(define-sab-reader =sab-code-long-string= (stream table)
  (let* ((size (read-32-bit-number stream)))
    ;;(read-substring size stream)
    (string-replace-string-all (string-replace-string-all (read-substring size stream) "\215\215" *paragraph-marker-string*) "\215" *line-break-string*)
    ))

(define (sab-validate-sage-param-command-name name)
  ;; TODO: implement
  #t)

(define-sab-reader =sab-code-command-name= (stream table)
  (let ((name (read-sab-thing stream table #f)))
    (sab-validate-sage-param-command-name name)
    name))

(define-structure sage-command name parameter)
(set-record-type-unparser-method!
 rtd:sage-command
 (standard-unparser-method 'sage-command
                           (lambda (envr port)
                             (format port ": ~a" (sage-command-name envr)))))
(define-sab-reader =sab-code-command= (stream table)
  (let* ((name (read-sab-thing stream table =sab-code-command-name=))
         (parameter (read-sab-thing stream table #f)))
    ;; TODO ...
    (let ((c (make-sage-command name (if (memq parameter '(lisp:nil common-lisp:nil)) '() parameter))))
      (set! *commands* (cons c *commands*))
      c)))

(define-sab-reader =sab-code-fixnum= (stream table)
  (read-32-bit-number stream))

(define-sab-reader =sab-code-index= (stream table)
  (let ((n (read-32-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= i n)
          (reverse res)
          (loop (+ i 1)
                (cons (read-sab-thing stream table =sab-code-index-item=) res))))))

(define (sab-validate-type-code-symbol thing)
  ;; TODO: implement
  #t)

(define-sab-reader =sab-code-type-symbol= (stream table)
  (let ((thing (read-sab-thing stream table #f)))
    (sab-validate-type-code-symbol thing)
    thing))

(define (sab-validate-field-name thing)
  (let ((element (assoc thing *field-name-to-sab-code-alist*)))
    (unless element
      (error "not a valid field name" thing))
    element))

(define-sab-reader =sab-code-field-name= (stream table)
  (let* ((field-name (read-sab-thing stream table #f))
         (sab-code (sab-validate-field-name field-name)))
    (values field-name (second sab-code))))

(define-sab-reader =sab-code-index-item= (stream table)
  (let* ((topic (read-sab-thing stream table #f))
         (type (read-sab-thing stream table =sab-code-type-symbol=))
         (fields (let ((n (read-16-bit-number stream)))
                   (let loop ((i 0)
                              (res '()))
                     (if (= i n)
                         (reverse res)
                         (loop (+ i 1)
                               (cons (receive (field-name sab-code)
                                         (read-sab-thing stream table =sab-code-field-name=)
                                       (list field-name (read-sab-thing stream table sab-code)))
                                     res)))))))
                                        ;(fixup-old-doc-symbol-topic topic fields)
    (list topic type fields)
    ))

(define (sab-validate-unique-id unique-id)
  ;; TODO: implement
  #t)
(define-sab-reader =sab-code-unique-id= (stream table)
  (let ((unique-id (read-sab-thing stream table #f)))
    (sab-validate-unique-id unique-id)
    unique-id))

(define (sab-validate-token-list thing)
  ;; TODO: implement
  #t)

(define-sab-reader =sab-code-token-list= (stream table)
  (let ((thing (read-sab-thing stream table #f)))
    (sab-validate-token-list thing)
    thing))

(define-sab-reader =sab-code-location-pair= (stream table)
  (let* ((from (read-sab-thing stream table =sab-code-fixnum=))
         (to (read-sab-thing stream table =sab-code-fixnum=)))
    (list from to)))

(define-sab-reader =sab-code-callee-4ple-list= (stream table)
  (let ((n (read-16-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= i n)
          (reverse res)
          (let* ((topic (read-sab-thing stream table #f))
                 (type (read-sab-thing stream table =sab-code-type-symbol=))
                 (called-how (read-sab-thing stream table #f))
                 (unique-id (read-sab-thing stream table #f)))
            ;; (fixup-old-doc-symbol-topic topic '())
            ;; (fixup-view called-how)
            (loop (+ i 1)
                  (cons (list topic type called-how unique-id) res)))))))

(define-sab-reader =sab-code-symbol-ref= (stream table)
  (let ((index (read-16-bit-number stream)))
    (list-ref (mytable-symbol-table table) index)))

(define-sab-reader =sab-code-file-attribute-string= (stream table)
  (let ((s (read-sab-string stream table)))
    (if (string-null? s)
        #f
        s)))

(define-sab-reader =sab-code-contents-list= (stream table)
  (let ((n (read-16-bit-number stream)))
    (let loop ((i 0)
               (res '()))
      (if (= i n)
          (reverse res)
          (loop (+ i 1)
                (cons (read-sab-thing stream table #f) res))))))

(define (sab-validate-modification-history thing)
  ;; TODO: implement
  #t)

(define-sab-reader =sab-code-modification-history= (stream table)
  (let ((thing (read-sab-thing stream table #f)))
    (sab-validate-modification-history thing)
    thing))

(define-sab-reader =sab-code-read-from-string= (stream table)
  (let ((str (read-sab-string stream table)))
    (with-input-from-string str
      read)))

(define-structure sage-envr name mods contents-list)
(set-record-type-unparser-method!
 rtd:sage-envr
 (standard-unparser-method 'sage-envr
                           (lambda (envr port)
                             (format port ": ~a" (sage-envr-name envr)))))
(define-sab-reader =sab-code-envr= (stream table)
  (let* ((envr-name (read-sab-thing stream table =sab-code-envr-name=))
         (envr-mods (read-sab-thing stream table =sab-code-envr-mods=))
         (contents-list (read-sab-thing stream table =sab-code-contents-list=)))
    (let ((e (make-sage-envr envr-name envr-mods contents-list)))
      (set! *environments* (cons e *environments*))
      e)))

(define (sab-validate-envr-name thing)
  ;; TODO: implement
  #t)

(define-sab-reader =sab-code-envr-name= (stream table)
  (let ((thing (read-sab-thing stream table #f)))
    (sab-validate-envr-name thing)
    thing))

(define (sab-validate-attribute-name thing)
  ;; TODO: implement
  #t)

(define-structure sage-example-record-marker type encoding)
(define-sab-reader =sab-code-example-record-marker= (stream table)
  (let* ((type (read-sab-thing stream table #f))
         (encoding (read-sab-thing stream table #f)))
    (let ((e (make-sage-example-record-marker type encoding)))
      (set! *example-record-markers* (cons e *example-record-markers*))
      e)))

(define-sab-reader =sab-code-attribute-name= (stream table)
  (let ((thing (read-sab-thing stream table #f)))
    (sab-validate-attribute-name thing)
    thing))

;; no idea what this is supposed to do, but it seems to extract the correct strings :-/
(define-sab-reader =sab-code-fat-string= (stream table)
  (let ((pos (myport-offset stream)))
    (let ((dimension-count (read-8-bit-number stream)))
      (let ((dims (collect-n dimension-count (lambda () (read-8-bit-number stream)))))
        ;; (format #t "fat stream at #x~a: ~s~%" (number->string pos 16) dims)
        (collect-n (second dims) (lambda () (read-8-bit-number stream))) ;; discard 06
        (unless (zero? (second dims))
          (let ((type (read-8-bit-number stream)))
            (case type
              ((#x0c)
               (let* ((fst-len (read-8-bit-number stream))
                      (fst (read-substring fst-len stream))
                      (snd-len (read-8-bit-number stream))
                      (snd (read-substring snd-len stream))
                      (ten (read-8-bit-number stream)))
                 (unless (= ten #x10)
                   (error "expected to read #x10"))))
              ((#x14)
               (let* ((len (read-8-bit-number stream))
                      (style (read-substring len stream)))
                 (let ((next (read-8-bit-number stream)))
                   (if (= next #x14)
                       (let* ((len (read-8-bit-number stream))
                              (style (read-substring len stream)))
                         'foo ;; ignore
                         )
                       (unless (= next #x10)
                         (error "expected to read #x10 or #x14" next (string "#x" (number->string (myport-offset stream) 16))))))))
              (else
               (error "unknown fat string type code" type))))
          (let* ((len (read-8-bit-number stream))
                 (font (read-substring len stream))
                 (zero (read-8-bit-number stream)))
            (unless (= zero 0)
              (error "expected to read #x0"))))
        (let loop ((res ""))
          (if (= (string-length res) (car dims))
              (let ((res (string-replace-string-all (string-replace-string-all res "\215\215" *paragraph-marker-string*) "\215" *line-break-string*)))
                ;; (format #t "fat string: ~a~%" res)
                res)
              (let* ((strlen (read-8-bit-number stream))
                     (unknown (read-8-bit-number stream)))
                (loop (string-append res (read-substring strlen stream))))))))))

(define-sab-reader =sab-code-character= (stream table)
  (let ((cs (read-sab-string stream table)))
    (if (= (string-length cs) 1)
        (string-ref cs 0)
        (error "cannot convert to character" cs))))

(define-structure sage-picture type file-name name contents decoded)
(define-sab-reader =sab-code-picture= (stream table)
  (let* ((type (read-sab-thing stream table #f))
         (file-name (read-sab-thing stream table #f))
         (name (read-sab-string stream table))
         (contents (read-sab-thing stream table #f)))
    (let ((p (make-sage-picture type file-name name contents #f)))
      (set! *pictures* (cons p *pictures*))
      p)))

(define-sab-reader =sab-code-8-bit-array= (stream table)
  (let ((n (read-32-bit-number stream)))
    (read-substring n stream)))

(define-structure sage-reference topic type unique-id view appearance booleans field)
;; booleans: (final-period initial-cap)
;; field: (topic contents operation)
;; view ("CrossRef" "crossref" "Expand")
(define-sab-reader =sab-code-extensible-reference-take-two= (stream table)
  (let* ((topic (read-sab-thing stream table #f))
         (type (read-sab-thing stream table =sab-code-type-symbol=))
         (unique-id (read-sab-thing stream table #f))
         (view (read-sab-thing stream table #f))
         (appearance (read-sab-thing stream table #f))
         (booleans (read-sab-thing stream table #f))
         (field (read-sab-thing stream table #f)))
    ;;(setq topic (fixup-old-doc-symbol-topic topic #f))
    ;;(setq view (fixup-view view))
    ;; (build-sage-reference (alist-nonnull 'topic topic
    ;;          'type type
    ;;          (if (integerp unique-id) 'unique-index 'unique-id)
    ;;             unique-id
    ;;          'view view
    ;;          'appearance appearance
    ;;          'booleans booleans
    ;;          'field field))
    (let ((r (make-sage-reference topic type unique-id view appearance
                                  (if (memq booleans '(lisp:nil common-lisp:nil)) '() booleans)
                                  (if (memq field  '(lisp:nil common-lisp:nil)) '() field))))
      ;; (format #t "reference ~s~%" r)
      ;; (pp r)
      (set! *references* (cons r *references*))
      r)))

(define-sab-reader =sab-code-reference= (stream table)
  (let* ((topic (read-sab-thing stream table #f))
         (type (read-sab-thing stream table =sab-code-type-symbol=))
         (unique-id (read-sab-thing stream table #f))
         (view (read-sab-thing stream table #f))
         (field (read-sab-thing stream table #f)))
    ;; TODO: handle booleans, appearance, etc.
    (let ((r (make-sage-reference topic type unique-id view '() '() (if (eq? 'lisp:nil field) '() field))))
      (set! *references* (cons r *references*))
      ;; (format #t "reference ~s~%" r)
      ;; (pp r)
      r)))

(define (read-sab-string stream table)
  (let ((c (myport-peek stream)))
    (cond ((= c =sab-code-string=)
           (read-sab-thing stream table =sab-code-string=))
          ((= c =sab-code-long-string=)
           (read-sab-thing stream table =sab-code-long-string=))
          (else
           (error "wanted to read a string, but got" c (list-ref *sab-code-names* c))))))

(define-structure sage-function-spec name)
(define-sab-reader =sab-code-function-spec= (stream table)
  (let ((name (read-sab-string stream table)))
    (let ((fs (make-sage-function-spec name)))
      (set! *function-specs* (cons fs *function-specs*))
      fs)))

(define *field-name-to-sab-code-alist*
  `((unique-id ,=sab-code-unique-id= write-sab-unique-id)
    (version-number ,=sab-code-fixnum= write-sab-fixnum)
    (flags ,=sab-code-fixnum= write-sab-fixnum)
    (location ,=sab-code-location-pair= write-sab-location-pair)
    (tokens ,=sab-code-token-list= write-sab-token-list)
    (keywords ,=sab-code-contents-list= write-sab-contents-list)
    (callee-list ,=sab-code-callee-4ple-list= write-sab-callee-4ple-list)
    ;;      ;; From old sab files
    ;;      (callees ,=sab-code-callee-triple-list= write-sab-callee-triple-list)
    (source-topic ,=sab-code-contents-list= write-sab-contents-list)
    (file-attribute-string ,=sab-code-file-attribute-string= write-sab-file-attribute-string)
    (contents ,=sab-code-contents-list= write-sab-contents-list)
    (arglist ,=sab-code-contents-list= write-sab-contents-list)
    (symbolics-common-lisp:arglist ,=sab-code-contents-list= write-sab-contents-list)
    (modification-history ,=sab-code-modification-history=
                          write-sab-modification-history)
    ;;      ;; From old sab files; same as contents
    ;;      (operation ,=sab-code-contents-list= write-sab-contents-list)
    ;;      ;; From old sab files; same as source-title
    ;;      (title ,=sab-code-contents-list= write-sab-contents-list)
    (source-title ,=sab-code-contents-list= write-sab-contents-list)
    (oneliner ,=sab-code-contents-list= write-sab-contents-list)
    (related ,=sab-code-contents-list= write-sab-contents-list)
    (releasenumber ,=sab-code-contents-list= write-sab-contents-list)
    (abbrev ,=sab-code-contents-list= write-sab-contents-list)
    (notes ,=sab-code-contents-list= write-sab-contents-list)
    (glossary ,=sab-code-contents-list= write-sab-contents-list)
    ;;      (topic nil write-sab-topic-spec)   ;seems bogus
    ;;      (type ,=sab-code-type-symbol= write-sab-type-spec) ;seems bogus
    (patched-from ,=sab-code-string= write-sab-string)
    (unique-index ,=sab-code-fixnum= write-sab-fixnum)
    ))
(define *sage-id-pattern* 0)
(define *compiled-data-format-versions* '(7))
(define (read-sab filename)
  (let ((stream (make-myport (read-file-content filename) 0)))
    (let ((id-pattern (read-32-bit-number stream)))
      (unless (= id-pattern *sage-id-pattern*)
        (error "Are you sure the file is a Sage compiled object file?" filename))
      (let ((version (read-8-bit-number stream)))
        (unless (member version *compiled-data-format-versions*)
          (error "incompatible version" version *compiled-data-format-versions*))
        (let ((file-attribute-alist (read-sab-thing stream (make-mytable '()) =sab-code-file-attribute-alist=)))
          (let* ((ps (read-32-bit-number stream))
                 (pos (read-32-bit-number stream)))
            ;;(format #t "throw away #x~a~%" (number->string ps 16)) ;; do not throw away the PS pointer
            (port-seek stream ps)
            (let loop ((res '()))
              (if (< (myport-offset stream) pos)
                  (loop (cons (read-sab-thing stream (make-mytable '()) #f) res))
                  (begin
                    ;;(format #t "go to position #x~a~%" (number->string pos 16))
                    (port-seek stream pos)
                    (let ((records (reverse res))
                          (index (read-sab-thing stream (make-mytable '()) =sab-code-index=)))
                      (list file-attribute-alist records index)))))))))))

(define (calculate-sage-record-callees! record index)
  (let ((clees (assq 'callee-list (third index))))
    (set-sage-record-callees!
     record
     (if clees
         (let ((table (make-hash-table)))
           (for-each (lambda (c)
                       (hash-table/put! table (fourth c) (list (second c) (third c) (first c))))
                     (cadr clees))
           table)
         #f))))

(define (register-sab filename)
  (let* ((el (read-sab filename))
         (records (second el))
         (index (third el)))
    (for-each (lambda (index record)
                (let ((id (second (assq 'unique-id (third index)))))
                  (set-sage-record-index! record index)
                  (calculate-sage-record-callees! record index)
                  (hash-table/put! *records-by-id* id record)))
              index
              records)
    el))

(define (read-sab-thing* filename offset)
  (let ((port (make-myport (read-file-content filename) offset)))
    (read-sab-thing port (make-mytable '()) #f)))

;;;; ******************** Binary Graphic parser ********************
;; based on dynamic-windows/binary-graphics.lisp

(define *binary-graphics-command-opcodes* (make-vector 256 #f))
(define *binary-graphics-operation-opcodes* (make-vector 256 #f))
(define *binary-graphics-commands* (make-hash-table))
(define *binary-graphics-operations* (make-hash-table))
(define *binary-graphics-keywords*
  (list->vector
   '(:bevel :butt :miter :none :round :square
            :draw :erase :flip
            :baseline :bottom :center :left :right :top
            :anti-cyclic :clamped :cyclic :relaxed
            :non-zero :odd-even
            :alu :attachment-x :attachment-y :character-style :clockwise :closed :copy-image
            :dash-pattern :scale-dashes :dashed :draw-end-point :draw-partial-dashes :end-angle
            :end-relaxation :end-slope-dx :end-slope-dy :filled :gray-level :handedness :image-bottom
            :image-left :image-right :image-top :initial-dash-phase :inner-x-radius :inner-y-radius
            :join-to-path :line-end-shape :line-joint-shape :mask :new-value :number-of-samples :opaque
            :pattern :points-are-convex-p :start-angle :start-relaxation :start-slope-dx :start-slope-dy
            :stretch-p :thickness :toward-x :toward-y :winding-rule
            :scale-thickness :character-size :string-width :scale-down-allowed :mask-x :mask-y
            :color :stipple :tile :shape :record-as-text :scan-conversion-mode
            :round-coordinates :center-circles :host-allowed :sketch :flatness
            :object :type :single-box :allow-sensitive-inferiors)))

(define (register-binary-graphics-command name opcode function)
  (hash-table/put! *binary-graphics-commands* name opcode)
  (hash-table/put! *binary-graphics-commands* opcode name)
  (vector-set! *binary-graphics-command-opcodes* opcode function))

(define (register-binary-graphics-operation name opcode function)
  (hash-table/put! *binary-graphics-operations* name opcode)
  (hash-table/put! *binary-graphics-operations* opcode name)
  (vector-set! *binary-graphics-operation-opcodes* opcode function))

(define-syntax define-binary-graphics-operation
  (syntax-rules ()
    ((define-binary-graphics-operation name opcode arglist
       body0 body ...)
     (begin
       (define name (lambda arglist
                      body0 body ...))
       (register-binary-graphics-operation 'name opcode name)))))

(define-syntax define-binary-graphics-command
  (syntax-rules ()
    ((define-binary-graphics-command name opcode arglist
       body0 body ...)
     (begin
       (define name (lambda arglist
                      body0 body ...))
       (register-binary-graphics-command 'name opcode name)))))

(define-syntax define-binary-graphics-command-for-value
  (syntax-rules ()
    ((define-binary-graphics-command-for-value name opcode arglist
       body0 body ...)
     (define-binary-graphics-command name opcode arglist
       (values (begin body0 body ...) #t)))))

(define-syntax define-binary-graphics-command-for-effect
  (syntax-rules ()
    ((define-binary-graphics-command-for-effect name opcode arglist
       body0 body ...)
     (define-binary-graphics-command name opcode arglist
       (begin body0 body ... (values #f #f))))))


(define (binary-graphics-next-value input-stream)
  (let loop ()
    (let ((byte (read-8-bit-number input-stream)))
      (let ((command (vector-ref *binary-graphics-command-opcodes* byte)))
        (if command
            (receive (result result?)
                (command input-stream)
              (if result?
                  result
                  (loop)))
            (error "Unknown binary graphics opcode at" byte (hex (- (myport-offset input-stream) 1))))))))

(define (binary-decode-graphics-into-forms input-stream)
  (let ((forms '()))
    (call-with-current-continuation
     (lambda (exit)
       (let loop ()
         ;;(format #t "loop: forms ~s~%" forms)
         (if (myport-eof? input-stream)
             (reverse forms)
             (let ((byte (read-8-bit-number input-stream)))
               (let ((command (vector-ref *binary-graphics-command-opcodes* byte)))
                 (if command
                     (receive (result result-type)
                         (command input-stream)
                       ;;(format #t " command: ~s ~s ~s~%" (hash-table/get *binary-graphics-commands* byte 'unknown) result result-type)
                       (case result-type
                         ((#t)
                          (if (eq? *end-value* result)
                              (exit (reverse forms))
                              (error "for-value command at top-level" result result-type)))
                         ((#f)
                          'ok)
                         ((:form)
                          (set! forms (cons result forms)))
                         (else
                          (error "unknown result type" byte result result-type)))
                       (loop))
                     (let ((operation (vector-ref *binary-graphics-operation-opcodes* byte)))
                       (if operation
                           (let ((result (operation input-stream)))
                             (set! forms (cons result forms))
                             ;;(format #t " operation: ~s ~s~%" (hash-table/get *binary-graphics-operations* byte 'unknown) result)
                             )
                           (error "garbage byte in input" byte (hex (- (myport-offset input-stream) 1))))
                       (loop)))))))))))

(define *format-version* 1)

(define *end-value* (list 'end))
(define (read-until-done input-stream)
  (let loop ((res '()))
    (let ((next (binary-graphics-next-value input-stream)))
      (if (eq? *end-value* next)
          (reverse res)
          (loop (cons next res))))))
(define (flip-byte n)
  (let loop ((i 0)
             (res 0))
    (if (= i 8)
        res
        (loop (+ i 1)
              (+ res (if (zero? (bitwise-and n (expt 2 i)))
                         0
                         (expt 2 (- 7 i))))))))
(define (vector-8b-map fun vector-8b)
  (let* ((len (vector-8b-length vector-8b))
         (new (make-vector-8b len)))
    (let loop ((i 0))
      (if (= i len)
          new
          (let ((b (fun (vector-8b-ref vector-8b i))))
            (vector-8b-set! new i b)
            (loop (+ i 1)))))))

(define-structure op-raster-image byte-size width height data)
(define-binary-graphics-command-for-value %com-raster-image 23 (input-stream)
  (let* ((byte-size (read-8-bit-number input-stream))
         (width (binary-graphics-next-value input-stream))
         (height (binary-graphics-next-value input-stream))
         (byte-length (* (/ (* width byte-size) 8) height))
         (data (read-substring byte-length input-stream)))
    ;; (with-output-to-file "/tmp/test.pbm"
    ;;   (lambda ()
    ;;     (format #t "P4 ~a ~a ~a" width height (vector-8b-map flip-byte data))))
    (make-op-raster-image byte-size width height data)
    ;;(list 'raster-image byte-size width height data)
    ))

(define-binary-graphics-command %com-end 50 (input-stream)
  (values *end-value* #t))

(define-binary-graphics-command-for-effect %com-format-version 51 (input-stream)
  (let ((version (read-8-bit-number input-stream)))
    (unless (= version *format-version*)
      (error "Incorrect version, instead of expected" version *format-version*))))

(define-binary-graphics-command-for-value %com-small-integer 52 (input-stream)
  (+ (read-8-bit-number input-stream) -128))

(define-binary-graphics-command-for-value %com-medium-integer 53 (input-stream)
  (let* ((low (read-8-bit-number input-stream))
         (high (read-8-bit-number input-stream)))
    (+ low (* high 256) -32768)))

(define-binary-graphics-command-for-value %op-large-integer 54 (input-stream)
  (let* ((lowlow (read-8-bit-number input-stream))
         (highlow (read-8-bit-number input-stream))
         (lowhigh (read-8-bit-number input-stream))
         (highhigh (read-8-bit-number input-stream)))
    (+ lowlow
       (* #x100 highlow)
       (* #x10000 lowhigh)
       (* #x1000000 highhigh))))

(define-binary-graphics-command-for-value %op-very-large-integer 55 (input-stream)
  (let* ((length0 (read-8-bit-number input-stream))
         (length1 (read-8-bit-number input-stream))
         (length (+ length0 (arithmetic-shift length1 8)))
         (n (ceiling-quotient length 8)))
    (let loop ((i 0)
               (number 0))
      (if (= i n)
          number
          (loop (+ i 1)
                (+ number (arithmetic-shift (read-8-bit-number input-stream) (* i 8))))))))

(define-binary-graphics-command-for-value %op-dash-pattern 72 (input-stream)
  (let* ((length (binary-graphics-next-value input-stream)))
    (collect-n length (lambda () (binary-graphics-next-value input-stream)))))

(define-structure op-point x y options)
(define-binary-graphics-operation %op-point 1 (input-stream)
  (let* ((x (binary-graphics-next-value input-stream))
         (y (binary-graphics-next-value input-stream)))
    (make-op-point x y (read-until-done input-stream))))

(define-structure op-line start-x start-y end-x end-y options)
(define-binary-graphics-operation %op-line 2 (input-stream)
  (let* ((start-x (binary-graphics-next-value input-stream))
         (start-y (binary-graphics-next-value input-stream))
         (end-x (binary-graphics-next-value input-stream))
         (end-y (binary-graphics-next-value input-stream)))
    (make-op-line start-x start-y end-x end-y (read-until-done input-stream))))

(define-structure op-lines points options)
(define-binary-graphics-operation %op-lines 3 (input-stream)
  (let ((points (binary-graphics-next-value input-stream)))
    (if (not (and (vector? points)
                  (even? (vector-length points))
                  (vector-every number? points)))
        (error "not a vector of points" points))
    (make-op-lines points (read-until-done input-stream))))

(define-structure op-rectangle left top right bottom options)
(define-binary-graphics-operation %op-rectangle 4 (input-stream)
  (let* ((left (binary-graphics-next-value input-stream))
         (top (binary-graphics-next-value input-stream))
         (right (binary-graphics-next-value input-stream))
         (bottom (binary-graphics-next-value input-stream)))
    (make-op-rectangle left top right bottom (read-until-done input-stream))))

(define-structure op-triangle x1 y1 x2 y2 x3 y3 options)
(define-binary-graphics-operation %op-triangle 5 (input-stream)
  (let* ((x1 (binary-graphics-next-value input-stream))
         (y1 (binary-graphics-next-value input-stream))
         (x2 (binary-graphics-next-value input-stream))
         (y2 (binary-graphics-next-value input-stream))
         (x3 (binary-graphics-next-value input-stream))
         (y3 (binary-graphics-next-value input-stream)))
    (make-op-triangle x1 y1 x2 y2 x3 y3 (read-until-done input-stream))))

(define-structure op-polygon points options)
(define-binary-graphics-operation %op-polygon 6 (input-stream)
  (let ((points (binary-graphics-next-value input-stream)))
    (if (not (and (vector? points)
                  (even? (vector-length points))
                  (vector-every number? points)))
        (error "not a vector of points" points))
    (make-op-polygon points (read-until-done input-stream))))

(define-structure op-ellipse center-x center-y radius-x radius-y options)
(define-binary-graphics-operation %op-ellipse 8 (input-stream)
  (let* ((center-x (binary-graphics-next-value input-stream))
         (center-y (binary-graphics-next-value input-stream))
         (x-radius (binary-graphics-next-value input-stream))
         (y-radius (binary-graphics-next-value input-stream)))
    (make-op-ellipse center-x center-y x-radius y-radius (read-until-done input-stream))))

(define-structure op-bezier-curve start-x start-y end-x end-y control-1-x control-1-y control-2-x control-2-y options)
(define-binary-graphics-operation %op-bezier-curve 9 (input-stream)
  (let* ((start-x (binary-graphics-next-value input-stream))
         (start-y (binary-graphics-next-value input-stream))
         (end-x (binary-graphics-next-value input-stream))
         (end-y (binary-graphics-next-value input-stream))
         (control-1-x (binary-graphics-next-value input-stream))
         (control-1-y (binary-graphics-next-value input-stream))
         (control-2-x (binary-graphics-next-value input-stream))
         (control-2-y (binary-graphics-next-value input-stream)))
    (make-op-bezier-curve start-x start-y end-x end-y control-1-x control-1-y control-2-x control-2-y (read-until-done input-stream))))

(define-structure op-cubic-spline points options)
(define-binary-graphics-operation %op-cubic-spline 10 (input-stream)
  (let ((points (binary-graphics-next-value input-stream)))
    (if (not (and (vector? points)
                  (even? (vector-length points))
                  (vector-every number? points)))
        (error "not a vector of points" points))
    (make-op-cubic-spline points (read-until-done input-stream))))

(define-structure op-path path-function options)
(define-binary-graphics-operation %op-path 11 (input-stream)
  ;;(format #t "called %op-path at ~a~%" (hex (myport-offset input-stream)))
  (let* ((path-function (binary-graphics-next-value input-stream)))
    (make-op-path path-function (read-until-done input-stream))))

(define-structure op-string string x y options)
(define-binary-graphics-operation %op-string 12 (input-stream)
  (let* ((string (binary-graphics-next-value input-stream))
         (x (binary-graphics-next-value input-stream))
         (y (binary-graphics-next-value input-stream)))
    (make-op-string string x y (read-until-done input-stream))))

(define-structure op-circular-arc-to to-x to-y tangent-intersection-x tangent-intersection-y radius options)
(define-binary-graphics-operation %op-circular-arc-to 14 (input-stream)
  ;;  (format #t "circular arc to at ~a~%" (hex (myport-offset input-stream)))
  (let* ((to-x (binary-graphics-next-value input-stream))
         (to-y (binary-graphics-next-value input-stream))
         (tangent-intersection-x (binary-graphics-next-value input-stream))
         (tangent-intersection-y (binary-graphics-next-value input-stream))
         (radius (binary-graphics-next-value input-stream)))
    (make-op-circular-arc-to to-x to-y tangent-intersection-x tangent-intersection-y radius (read-until-done input-stream))))

(define-structure op-image image left top options)
(define-binary-graphics-operation %op-image 16 (input-stream)
  (let* ((image (binary-graphics-next-value input-stream))
         (left (binary-graphics-next-value input-stream))
         (top (binary-graphics-next-value input-stream)))
    (make-op-image image left top (read-until-done input-stream))))

(define-structure op-string-image string x y options)
(define-binary-graphics-operation %op-string-image 17 (input-stream)
  (let* ((string (binary-graphics-next-value input-stream))
         (x (binary-graphics-next-value input-stream))
         (y (binary-graphics-next-value input-stream)))
    (make-op-string-image string x y (read-until-done input-stream))))

(define-structure op-line-to end-x end-y options)
(define-binary-graphics-operation %op-line-to 18 (input-stream)
  (let* ((end-x (binary-graphics-next-value input-stream))
         (end-y (binary-graphics-next-value input-stream)))
    (make-op-line-to end-x end-y (read-until-done input-stream))))

(define-structure op-close-path options)
(define-binary-graphics-operation %op-close-path 19 (input-stream)
  (make-op-close-path (read-until-done input-stream)))

(define-binary-graphics-command-for-value %com-thin-string 20 (input-stream)
  (let ((len (read-8-bit-number input-stream)))
    (read-substring len input-stream)))

(define-binary-graphics-command-for-value %com-path 22 (input-stream)
  ;;(format #t "called %com-path at ~a ~s~%" (hex (myport-offset input-stream)) input-stream)
  (let ((function (binary-decode-graphics-into-forms input-stream)))
    ;;(format #t "read path function ~s~%" function)
    function))

(define-binary-graphics-command-for-value %com-character-style 24 (input-stream)
  (let ((len (read-8-bit-number input-stream)))
    (string->symbol (read-substring len input-stream))))

(define-binary-graphics-command-for-value %com-ratio 56 (input-stream)
  (let* ((num (binary-graphics-next-value input-stream))
         (denom (binary-graphics-next-value input-stream)))
    (/ num denom)))

(define-binary-graphics-command-for-value %com-single-float 57 (input-stream)
  (let ((bytes (read-substring 4 input-stream)))
    (parse-float bytes)))

(define-binary-graphics-command-for-value %com-double-float 58 (input-stream)
  (let ((bytes (read-substring 8 input-stream)))
    (parse-double bytes)))

(define-binary-graphics-command-for-value %com-point-sequence 59 (input-stream)
  (let* ((length (binary-graphics-next-value input-stream))
         (points (make-vector (* length 2))))
    (let loop ((i 0))
      (if (= i (* length 2))
          points
          (let ((p (binary-graphics-next-value input-stream)))
            (vector-set! points i p)
            (if (not (number? p))
                (error "element not a point in point sequence")
                (loop (+ i 1))))))))

(define-binary-graphics-command-for-value %com-angle 60 (input-stream)
  (let ((two_pi (* 2 4 (atan 1))))
    (/ (* (binary-graphics-next-value input-stream) two_pi) 3600.0)))

(define-binary-graphics-command-for-value %com-true 62 (ignore) #t)
(define-binary-graphics-command-for-value %com-false 63 (ignore) #f)
(define-binary-graphics-command-for-value %com-keyword 64 (input-stream)
  (vector-ref *binary-graphics-keywords* (read-8-bit-number input-stream)))

(define-structure op-set-current-position x y options)
(define-binary-graphics-command %com-set-position 67 (input-stream)
  (values (make-op-set-current-position
           (binary-graphics-next-value input-stream)
           (binary-graphics-next-value input-stream)
           '())
          ':form))

(define-structure op-graphics-transform r11 r12 r21 r22 tx ty)
(define-binary-graphics-command %com-transform-matrix 68 (input-stream)
  (let* ((r11 (binary-graphics-next-value input-stream))
         (r12 (binary-graphics-next-value input-stream))
         (r21 (binary-graphics-next-value input-stream))
         (r22 (binary-graphics-next-value input-stream))
         (tx (binary-graphics-next-value input-stream))
         (ty (binary-graphics-next-value input-stream)))
    (values (make-op-graphics-transform r11 r12 r21 r22 tx ty) ':form)))

(define-structure op-scan-conversion-mode output-forms options)
(define-binary-graphics-command %op-scan-conversion-mode 74 (input-stream)
  ;;  (format #t "called %op-scan-conversion-mode~%")
  (let ((output-forms (binary-decode-graphics-into-forms input-stream)))
    ;;    (format #t "  output forms ~s~%" output-forms)
    (values (make-op-scan-conversion-mode output-forms (read-until-done input-stream)) ':form)))
;;;; ******************** HTML renderer ********************
(define (format-sage-reference-topic sage-reference)
  (let ((topic (sage-reference-topic sage-reference)))
    (cond ((string? topic)
           topic)
          ((sage-function-spec? topic)
           (sage-function-spec-name topic))
          (else
           (error "unknown sage reference topic" topic)))))

(define *records-by-name* (make-hash-table))
(define *records-by-id* (make-hash-table))

(define *currently-including* (make-parameter '()))
(define *current-record* (make-parameter #f))
(define (include-sage-reference sage)
  (if (memq sage (*currently-including*))
      (format #t "already including ~s, ignoring it. ~s~%" sage (*currently-including*))
      (parameterize ((*currently-including* (cons sage (*currently-including*))))
        (let* ((ref (sage-reference-unique-id sage))
               (topic (sage-reference-topic sage))
               (name (if (sage-function-spec? topic) (sage-function-spec-name topic) topic))
               (record (hash-table/get *records-by-id* ref #f))) ;; try by id
          ;;(format #t "including ~s ~s~%" (sage-reference-type sage) ref)
          ;; (flush-output)
          (if record
              (record->sxml record)
              (let ((by-name (hash-table/get *records-by-name* name #f))) ;; try by name
                (format #t "could not resolve reference by id: ~s~%" sage)
                (if by-name
                    (record->sxml by-name)
                    (let ((by-name (find (lambda (el) (string-ci=? name (if (sage-function-spec? el) (sage-function-spec-name el) el))) (hash-table-keys *records-by-name*)))) ;; try case insensitive
                      (if by-name
                          (hash-table/get *records-by-name* by-name #f)
                          (if *ignore-missing-includes*
                              (begin
                                (format #t "ignoring missing include ~a ~s~%" name sage)
                                "")
                              (error "cannot find referenced record" ref sage)))))))))))

(define (my-split-string string split-at marker)
  (let ((len (string-length string))
        (split-at-len (string-length split-at)))
    (let loop ((pos 0)
               (res '()))
      (let ((p (substring-search-forward split-at string pos len)))
        (if p
            (loop (+ p split-at-len)
                  (let ((s (substring string pos p)))
                    ;; (if (string-null? s)
                    ;;     res
                    ;;     (cons s (if marker (if (null? res) res (cons marker res)) res)))
                    (cons s (if marker (if (null? res) res (cons marker res)) res))
                    ))
            (let ((s (substring string pos len)))
              (reverse (cons s (if marker (if (null? res) res (cons marker res)) res)))
              ;; (if (string-null? s)
              ;;     (reverse res)
              ;;     (reverse (cons s (if marker (if (null? res) res (cons marker res)) res))))
              ))))))

(define (ensure-list x)
  (if (pair? x) x (list x)))

(define *raster-png-count* 0)

(define (next-raster-png-filename)
  (begin0
   (string "/tmp/raster-png-" *raster-png-count* ".png")
   (set! *raster-png-count* (+ *raster-png-count* 1))))

(define *raster-images* (make-hash-table))
(define (->base64 str)
  (apply string-append
         (map (lambda (char)
                (define (nibble x)
                  (list-ref (string->list "0123456789ABCDEF") x))
                (let* ((value (char->ascii char))
                       (high (nibble (quotient value 16)))
                       (low (nibble (remainder value 16))))
                  (string high low)))
              (string->list str))))
(define (raster->png image)
  (define (->png filename)
    (with-output-to-file "/tmp/foo.pbm"
      (lambda ()
        (format #t "P4 ~a ~a ~a" (op-raster-image-width image) (op-raster-image-height image) (vector-8b-map flip-byte (op-raster-image-data image)))))
    (run-shell-command "convert /tmp/foo.pbm /tmp/foo.png"))
  (let ((cached (hash-table/get *raster-images* image #f)))
    (if cached
        cached
        (begin
          (->png "/tmp/foo.png")
          (if *inline-pictures*
              (begin
                (run-shell-command "base64 /tmp/foo.png > /tmp/foo.base64")
                (let ((data (string-append "data:image/png;base64," (string-replace-string-all (read-file-content "/tmp/foo.base64") (string #\newline) ""))))
                  data))
              (let ((path (next-raster-png-filename)))
                (rename-file "/tmp/foo.png" path)
                (hash-table/put! *raster-images* image path)
                path))))))

(define (partition-tuples lst tuple-size #!optional error-if-not-exact)
  (let loop ((lst lst)
             (res '()))
    (if (< (length lst) tuple-size)
        (if (and (not (default-object? error-if-not-exact))
                 error-if-not-exact)
            (error "cannot partition exactly" lst tuple-size)
            (reverse (if (not (null? lst))
                         (cons lst res)
                         res)))
        (loop (drop lst tuple-size)
              (cons (take lst tuple-size)
                    res)))))

(define (points->string points-vector #!optional invert)
  (let ((pts (partition-tuples (vector->list points-vector) 2)))
    (decorated-string-append "" " " "" (map (lambda (el)
                                              (let ((y (cadr el))
                                                    (x (car el)))
                                                (string (my-inexact x) "," (my-inexact (if (eq? invert 'invert-y) (- y) y))))) pts))))

(define (points->cubic points-vector #!optional invert)
  (let ((pts (partition-tuples (vector->list points-vector) 2)))
    (decorated-string-append "" " " "" (let ((pts (map (lambda (el)
                                                         (let ((x (car el))
                                                               (y (cadr el)))
                                                           (string (my-inexact x) "," (my-inexact (if (eq? invert 'invert-y) (- y) y))))) pts)))
                                         `("M" ,(car pts)
                                           ,(if (= (length (cdr pts)) 3)
                                                " C"
                                                " Q")
                                           ,@(cdr pts))))))

(define (my-inexact n)
  (let ((f (inexact n)))
    (let ((s (format #f "~a" (/ (round->exact (* 1000 f)) 1000.0))))
      (if (char=? #\. (string-ref s (- (string-length s) 1)))
          (string-append s "0")
          (if (char=? #\. (string-ref s 0))
              (string-append "0" s)
              s)))))

(define (point-left-up x1 y1 x2 y2)
  "Return the x1/x2 and y1/y2, whichever is more upper-left"
  (values (min x1 x2)
          (min y1 y2)))

(define (point-right-down x1 y1 x2 y2)
  "Return the x1/x2 and y1/y2, whichever is more lower-right"
  (values (max x1 x2)
          (max y1 y2)))

(define-structure bounding-box x1 y1 x2 y2)
(define (new-bounding-box/bb bb other-bb)
  (new-bounding-box/xy (new-bounding-box/xy bb
                                            (bounding-box-x1 other-bb)
                                            (bounding-box-y1 other-bb))
                       (bounding-box-x2 other-bb)
                       (bounding-box-y2 other-bb)))

(define (new-bounding-box/xy bb x0 y0)
  (let ((x1 (bounding-box-x1 bb))
        (y1 (bounding-box-y1 bb))
        (x2 (bounding-box-x2 bb))
        (y2 (bounding-box-y2 bb)))
    (receive (nx1 ny1)
        (point-left-up x1 y1 x0 y0)
      (receive (nx2 ny2)
          (point-right-down x2 y2 x0 y0)
        (make-bounding-box nx1 ny1 nx2 ny2)))))

(define (path->sxml path)
  (let loop ((path path)
             (res '()))
    (if (null? path)
        (decorated-string-append "" " " "" (reverse res))
        (let ((el (car path)))
          (loop (cdr path)
                (cons (cond ((op-close-path? el)
                             (string "Z"))
                            ((op-line-to? el)
                             (string "l" (my-inexact (op-line-to-end-x el)) "," (my-inexact (- (op-line-to-end-y el))) " "))
                            ((op-set-current-position? el)
                             (string "M" (my-inexact (op-set-current-position-x el)) "," (my-inexact (- (op-set-current-position-y el)))))
                            ((op-circular-arc-to? el)
                             (string "L" (my-inexact (op-circular-arc-to-to-x el)) " " (my-inexact (- (op-circular-arc-to-to-y el)))))
                            ((op-lines? el)
                             (string "L" (points->string (op-lines-points el))))
                            (else
                             (error "unknown path element" el)))
                      res))
          ))))

(define (plist-get plist key default)
  (let loop ((l plist))
    (if (null? l)
        default
        (if (eq? (car l) key)
            (cadr l)
            (loop (cddr l))))))

(define (escape-svg str)
  (string-replace-string-all
   (string-replace-string-all
    (string-replace-string-all str ">" "&gt;")
    "<" "&lt;")
   "&" "&amp;"))

(define (picture-ops->sxml ops transform)
  (let loop ((ops ops)
             (res '())
             (current-transform transform)
             (bb (make-bounding-box 0 0 0 0)))
    (if (null? ops)
        (let ((r (values
                  `(g
                    ,@(reverse res))
                  bb)))
          ;;(format #t "picture->sxml -> ~s~%" r)
          r)
        (let ((op (car ops))
              (transform (lambda (before after)
                           `(transform ,(format #f "~amatrix(~a ~a ~a ~a ~a ~a)~a"
                                                before
                                                (my-inexact (op-graphics-transform-r11 current-transform))
                                                (my-inexact (op-graphics-transform-r12 current-transform))
                                                (my-inexact (op-graphics-transform-r21 current-transform))
                                                (my-inexact (op-graphics-transform-r22 current-transform))
                                                (my-inexact (op-graphics-transform-tx current-transform))
                                                (my-inexact (- (op-graphics-transform-ty current-transform)))
                                                after)))))
          (define (continue obj bb)
            (loop (cdr ops)
                  (cons obj res)
                  current-transform
                  bb))
          (define (tx+ x)
            (+ x (op-graphics-transform-tx current-transform)))
          (define (ty+ y)
            (- y (op-graphics-transform-ty current-transform)))
          (cond ((op-graphics-transform? op)
                 (loop (cdr ops)
                       res
                       op
                       bb))
                ((op-line? op)
                 (let* ((x1 (tx+ (op-line-start-x op)))
                        (y1 (ty+ (- (op-line-start-y op))))
                        (x2 (tx+ (op-line-end-x op)))
                        (y2 (ty+ (- (op-line-end-y op))))
                        (bb (new-bounding-box/xy (new-bounding-box/xy bb x1 y1) x2 y2)))
                   (continue
                    `(line (@ (x1 ,(my-inexact x1))
                              (y1 ,(my-inexact y1))
                              (x2 ,(my-inexact x2))
                              (y2 ,(my-inexact y2))
                              (stroke "#000000")
                              (fill "none")))
                    bb)))
                ((op-scan-conversion-mode? op)
                 ;; not sure whether this is correct?
                 (picture-ops->sxml (op-scan-conversion-mode-output-forms op) current-transform))
                ((op-rectangle? op)
                 (let ((filled? (plist-get (op-rectangle-options op) ':filled #t))
                       (thickness (plist-get (op-rectangle-options op) ':thickness 1))
                       (gray-level (plist-get (op-rectangle-options op) ':gray-level #f))
                       (x (tx+ (min (op-rectangle-left op) (op-rectangle-right op))))
                       (y (ty+ (- (max (op-rectangle-top op) (op-rectangle-bottom op)))))
                       (width (abs (- (op-rectangle-right op) (op-rectangle-left op))))
                       (height (abs (- (op-rectangle-bottom op) (op-rectangle-top op)))))
                   (continue `(rect (@ (x ,(my-inexact x))
                                       (y ,(my-inexact y))
                                       (width ,(my-inexact width))
                                       (height ,(my-inexact height))
                                       ,@(if filled?
                                             `((fill ,(if gray-level
                                                          (string "rgb(" (round->exact (* 255 (- 1 gray-level))) "," (round->exact (* 255 (- 1 gray-level))) "," (round->exact (* 255 (- 1 gray-level))) ")")
                                                          "#000000")))
                                             `((stroke "#000000")
                                               (stroke-width ,thickness)
                                               (fill "none")))))
                             (new-bounding-box/bb bb (make-bounding-box x y (+ x width) (+ y height))))))
                ((op-image? op)
                 (let ((img (op-image-image op)))
                   (let* ((x (tx+ (op-image-left op)))
                          (y (ty+ (op-image-top op)))
                          (options (op-image-options op))
                          (image-right (plist-get options ':image-right #f))
                          (image-bottom (plist-get options ':image-bottom #f))
                          (width (or image-right (op-raster-image-width img)))
                          (height (or image-bottom (op-raster-image-height img))))
                     (continue `(image (@ (x ,(my-inexact x))
                                          (y ,(my-inexact y))
                                          (width ,(string (my-inexact width) "px"))
                                          (height ,(string (my-inexact height) "px"))
                                          (xlink:href ,(raster->png (op-image-image op)))))
                               (new-bounding-box/bb bb (make-bounding-box x y (+ x width) (+ y height)))))))
                ((op-string? op)
                 (let ((x (tx+ (op-string-x op)))
                       (y (ty+ (- (op-string-y op))))
                       (width (* (string-length (op-string-string op)) 10)) ;; completely unbased guess
                       (height -16) ;; completely unbased guess
                       )
                   (continue `(text (@ (x ,(my-inexact x))
                                       (y ,(my-inexact y)))
                                    ,(escape-svg (op-string-string op)))
                             (new-bounding-box/bb bb (make-bounding-box x y (+ x width) (+ y height))))))
                ((op-string-image? op)
                 (let ((x (tx+ (op-string-image-x op)))
                       (y (ty+ (- (op-string-image-y op))))
                       (width (* (string-length (op-string-image-string op)) 10)) ;; completely unbased guess
                       (height -16) ;; completely unbased guess
                       )
                   (continue `(text (@ (x ,(my-inexact x))
                                       (y ,(my-inexact y)))
                                    ,(escape-svg (op-string-image-string op)))
                             (new-bounding-box/bb bb (make-bounding-box x y (+ x width) (+ y height))))))
                ((op-path? op)
                 (let ((filled? (plist-get (op-path-options op) ':filled #t))
                       (thickness (plist-get (op-path-options op) ':thickness 1)))
                   (let ((path (path->sxml (op-path-path-function op))))
                     (continue `(path (@ (d ,path)
                                         ,@(if filled?
                                               '((fill "#x000000"))
                                               '((fill "none")))
                                         ,@(if (not filled?)
                                               `((stroke "#000000")
                                                 (stroke-width ,thickness))
                                               '())
                                         ,(transform "" "")))
                               bb))))
                ((op-cubic-spline? op)
                 (let ((thickness (plist-get (op-cubic-spline-options op) ':thickness 1)))
                   (let* ((path (string (points->cubic (op-cubic-spline-points op) 'invert-y))))
                     (continue `(path (@ (d ,path)
                                         (stroke "#000000")
                                         (fill "none")
                                         (stroke-width ,thickness)
                                         ,(transform "" "")))
                               bb))))
                ((op-lines? op)
                 (let* ((thickness (plist-get (op-lines-options op) ':thickness 1))
                        (path (points->string (op-lines-points op) 'invert-y)))
                   (continue `(polyline (@ (points ,path)
                                           (stroke "#000000")
                                           (fill "none")
                                           (stroke-width ,thickness)
                                           ,(transform "" "")))
                             bb)))
                ((op-triangle? op)
                 (let* ((filled? (plist-get (op-triangle-options op) ':filled #t))
                        (thickness (plist-get (op-triangle-options op) ':thickness 1))
                        (gray-level (plist-get (op-triangle-options op) ':gray-level #f))
                        (path (points->string (vector (tx+ (op-triangle-x1 op)) (ty+ (- (op-triangle-y1 op)))
                                                      (tx+ (op-triangle-x2 op)) (ty+ (- (op-triangle-y2 op)))
                                                      (tx+ (op-triangle-x3 op)) (ty+ (- (op-triangle-y3 op)))))))
                   (continue `(polygon (@ (points ,path)
                                          ,@(if filled?
                                                `((fill ,(if gray-level
                                                             (string "rgb(" (round->exact (* 255 (- 1 gray-level))) "," (round->exact (* 255 (- 1 gray-level))) "," (round->exact (* 255 (- 1 gray-level))) ")")
                                                             "#000000")))
                                                `((stroke "#000000")
                                                  (stroke-width ,thickness)
                                                  (fill "none")))))
                             bb)))
                ((op-polygon? op)
                 (let* ((path (points->string (op-polygon-points op))))
                   (continue `(polygon (@ (points ,path)
                                          (stroke "#000000")
                                          ,(transform "" "")))
                             bb )))
                ((op-ellipse? op)
                 (let ((filled? (plist-get (op-ellipse-options op) ':filled #t))
                       (thickness (plist-get (op-ellipse-options op) ':thickness 1))
                       (gray-level (plist-get (op-ellipse-options op) ':gray-level #f)))
                   (continue `(ellipse (@ (cx ,(my-inexact (tx+ (op-ellipse-center-x op))))
                                          (cy ,(my-inexact (ty+ (op-ellipse-center-y op))))
                                          (rx ,(my-inexact (op-ellipse-radius-x op)))
                                          (ry ,(my-inexact (op-ellipse-radius-y op)))
                                          ,@(if filled?
                                                `((fill ,(if gray-level
                                                             (string "rgb(" (round->exact (* 255 (- 1 gray-level))) "," (round->exact (* 255 (- 1 gray-level))) "," (round->exact (* 255 (- 1 gray-level))) ")")
                                                             "#000000")))
                                                `((stroke "#000000")
                                                  (stroke-width ,thickness)
                                                  (fill "none")))))
                             bb)))
                ((op-point? op)
                 (let ((x (tx+ (op-point-x op)))
                       (y (ty+ (op-point-y op)))
                       (r 1))
                   (continue `(circle (@ (cx ,(my-inexact x))
                                         (cy ,(my-inexact y))
                                         (r ,(my-inexact r))))
                             (new-bounding-box/xy bb x y))))
                ((op-bezier-curve? op)
                 (let ((thickness (plist-get (op-bezier-curve-options op) ':thickness 1)))
                   (let* ((path (string (points->cubic (list (op-bezier-curve-start-x op)
                                                             (op-bezier-curve-start-y op)
                                                             (op-bezier-curve-control-1-x op)
                                                             (op-bezier-curve-control-1-y op)
                                                             (op-bezier-curve-control-2-x op)
                                                             (op-bezier-curve-control-2-y op)
                                                             (op-bezier-curve-end-x op)
                                                             (op-bezier-curve-end-y op))
                                                       'invert-y))))
                     (continue `(path (@ (d ,path)
                                         (stroke "#000000")
                                         (fill "none")
                                         (stroke-width ,thickness)
                                         ,(transform "" "")))))))
                (else
                 (error "don't know how to convert to svg" op)))))))

(define (picture->sxml sage)
  (let ((ops (decode-picture sage))
        (transform (make-op-graphics-transform 1 0 0 1 0 0)))
    (receive (pic bb)
        (picture-ops->sxml ops transform)
      (let ((x (my-inexact (bounding-box-x1 bb)))
            (y (my-inexact (bounding-box-y1 bb)))
            (width (my-inexact (- (bounding-box-x2 bb) (bounding-box-x1 bb))))
            (height (my-inexact (- (bounding-box-y2 bb) (bounding-box-y1 bb)))))
        `(svg (@ (width ,width) (height ,height) (|viewBox| ,(format #f "~a ~a ~a ~a" x y width height)))
              ;; (rect (@ (x ,x)
              ;;          (y ,y)
              ;;          (width ,width)
              ;;          (height ,height)
              ;;          (stroke "red")
              ;;          (fill "none")
              ;;          (stroke-width "3")))
              ,pic)))))

(define *marker-tab-to-tab-stop* (list 'tab-to-tab-stop-marker))
(define (sage->sxml sage)
  (define (unimplemented-sage-command sage)
    `(div (@ (class "unknown-sage-command"))
          "Unknown sage command: "
          ,(sage-command-name sage)
          " "
          ,(format #f "~s~%" (sage-command-parameter sage))))
  (define (unimplemented-sage-environment sage content)
    `(div (@ (class "unknown-sage-environment"))

          ,(format #f "Unknown sage environment: ~s, mods: ~s~%" (sage-envr-name sage) (sage-envr-mods sage))
          ,@content))
  (cond ((string? sage)
         (string-replace-string-all (string-replace-string-all (string-replace-string-all sage "&" "&amp;") "<" "&lt;") ">" "&gt;"))
        ((null? sage)
         "")
        ((sage-envr? sage)
         ;; see Concordia: "Dictionary of Symbolics Concordia Markup Environments and Commands"
         ;; Sage Environments
         (let ((content (map sage->sxml (fix-up-special-markup (sage-envr-contents-list sage)))))
           (case (sage-envr-name sage)
             ((b) ;; bold
              `(b (@ (class "b"))
                  ,@content))
             ((bi) ;; bold italic
              `(b (@ (class "bi"))
                  (i ,@content)))
             ((i) ;; italic
              `(i (@ (class "i"))
                  ,@content))
             ((p) ;; bold italic
              `(span (@ (class "p"))
                     ,@content))
             ((r) ;; roman
              `(span (@ (class "r"))
                     ,@content))
             ((g) ;; greek
              `(span (@ (class "g"))
                     ,@content))
             ((w) ;; no idea??
              `(span (@ (class "w"))
                     ,@content))
             ((k) ;; keyboard
              `(code (@ (class "k"))
                     ,@content))
             ((m) ;; mathematical
              `(code (@ (class "m"))
                     ,@content))
             ((ls) ;; lisp object
              `(code (@ (class "ls"))
                     ,@content))
             ((c) ;; smallcaps
              `(span (@ (class "c"))
                     ,@content))
             ((s) ;; symbol
              `(span (@ (class "s"))
                     ,@content))
             ((t) ;; typewriter
              `(code (@ (class "t"))
                     ,@content))
             ((u) ;; underline non-space
              `(span (@ (class "u"))
                     ,@content))
             ((f) ;; specialfont (??)
              `(span (@ (class "f"))
                     ,@content))
             ((un) ;; underline alphanumeric
              `(span (@ (class "un"))
                     ,@content))
             ((ux) ;; underline everything
              `(span (@ (class "ux"))
                     ,@content))
             ((multiple)
              `(div (@ (class "multiple"))
                    ,@content))
             ((plus)
              (unimplemented-sage-environment sage content))
             ((display)
              `(div (@ (class "display"))
                    ,@content))
             ((crossref)
              (unimplemented-sage-environment sage content))
             ((enumerate)
              `(ol (@ (class "enumerate"))
                   ,@(map (lambda (el)
                            ;; rather ugly hack to replace (div (@ (class "nex-paragraph))  by (li
                            (if (and (pair? el)
                                     (eq? (car el) 'div)
                                     (> (length el) 1)
                                     (eq? (car (second el)) '@)
                                     (eq? 'class (first (second (second el))))
                                     (string=? "nex-paragraph" (second (second (second el)))))
                                (cons 'li (cddr el))
                                el))
                          (fix-up-special-markup content))))
             ((description)
              `(div (@ (class "description"))
                    ,@content))
             ((quotation)
              (unimplemented-sage-environment sage content))
             ((figure)
              `(div (@ (class "figure"))
                    ,@content))
             ((advancednote)
              (unimplemented-sage-environment sage content))
             ((nex-tab-to-tab-stop)
              `(div (@ (class "nex-tab"))
                    ,@content))
             ((nex-paragraph)
              `(div (@ (class "nex-paragraph"))
                    ,@content))
             ((lisp:float)
              (unimplemented-sage-environment sage content))
             ((fullpagefigure)
              (unimplemented-sage-environment sage content))
             ((fullpagetable)
              (unimplemented-sage-environment sage content))
             ((layerederrorenv)
              (unimplemented-sage-environment sage content))
             ((center)
              `(div (@ (class "center"))
                    ,@content))
             ((minus)
              (unimplemented-sage-environment sage content))
             ((itemize)
              `(ul (@ (class "itemize"))
                   ,@(map (lambda (el)
                            (if (and (pair? el)
                                     (eq? (car el) 'div)
                                     (> (length el) 1)
                                     (eq? (car (second el)) '@)
                                     (eq? 'class (first (second (second el))))
                                     (string=? "nex-paragraph" (second (second (second el)))))
                                (cons 'li (cddr el))
                                el))
                          (fix-up-special-markup content))))
             ((table)
              (unimplemented-sage-environment sage content))
             ((simpletable)
              (unimplemented-sage-environment sage content))
             ((simpletable)
              `(table ,@content))
             ((common-lisp:- lisp:-)
              `(sub ,@content))
             ((common-lisp:+ lisp:+)
              `(sup ,@content))
             ((checklist)
              (unimplemented-sage-environment sage content))
             ((equation)
              (unimplemented-sage-environment sage content))
             ((example)
              `(div (@ (class "example"))
                    ,@content))
             ((verse)
              (unimplemented-sage-environment sage content))
             ((text)
              (unimplemented-sage-environment sage content))
             ((level)
              (unimplemented-sage-environment sage content))
             ((flushright)
              (unimplemented-sage-environment sage content))
             ((flushleft)
              (unimplemented-sage-environment sage content))
             ((verbatim)
              `(pre (@ (class "verbatim"))
                    ,@content))
             ((inputexample)
              (unimplemented-sage-environment sage content))
             ((fileexample)
              (unimplemented-sage-environment sage content))
             ((programexample)
              (unimplemented-sage-environment sage content))
             ((outputexample)
              (unimplemented-sage-environment sage content))
             ((activeexample)
              (unimplemented-sage-environment sage content))
             ((box)
              (unimplemented-sage-environment sage content))
             ((subheading)
              (unimplemented-sage-environment sage content))
             ((subsubheading)
              (unimplemented-sage-environment sage content))
             ((lisp:t common-lisp:t)
              `(span (@ (class "lisp:t"))
                     ,@content))
             ((commentary)
              `(div (@ (class "commentary"))
                    ,@content))
             ((header)
              `(h2 (@ (class "header"))
                   ,@content))
             ((heading)
              `(h3 (@ (class "heading"))
                   ,@content))
             ((majorheading)
              `(h2 (@ (class "majorheading"))
                   ,@content))
             ((captionenv)
              (unimplemented-sage-environment sage content))
             ((common-lisp:block lisp:block)
              (unimplemented-sage-environment sage content))
             ((c-description)
              (unimplemented-sage-environment sage content))
             ((bar old-bar-environment)
              (unimplemented-sage-environment sage content))
             ((largestyle)
              (unimplemented-sage-environment sage content))
             ((titlestyle)
              (unimplemented-sage-environment sage content))
             ((transparent)
              (unimplemented-sage-environment sage content))
             ((group)
              `(div (@ (class "group"))
                    ,@content))
             ((lisp:format common-lisp:format global:format)
              (if (null? (sage-envr-mods sage))
                  `(div (@ (class "format"))
                        ,@content)
                  (unimplemented-sage-environment sage content)))
             (else
              (error "unknown sage envr name" (sage-envr-name sage) sage)))))
        ;; Sage Commands
        ((sage-command? sage)
         (case (sage-command-name sage)
           ((em)
            "—")
           ((tabdivide)
            (unimplemented-sage-command sage))
           ((permit-word-break)
            "") ;; unicode break permitted here
           ((caption)
            `(div (@ (class "caption"))
                  ,(caar (sage-command-parameter sage))))
           ((layerederror)
            (unimplemented-sage-command sage))
           ((tag)
            `(a (@ (class "tag") (id ,(car (sage-command-parameter sage))) (name ,(car (sage-command-parameter sage))))
                "tag: " ,(car (sage-command-parameter sage))))
           ((label)
            `(a (@ (class "label") (id ,(car (sage-command-parameter sage))) (name ,(car (sage-command-parameter sage))))
                "label: " ,(car (sage-command-parameter sage))))
           ((hinge)
            (unimplemented-sage-command sage))
           ((ref)
            `(a (@ (href ,(string-append "#" (car (sage-command-parameter sage)))))
                ,(car (sage-command-parameter sage))))
           ((collect-centering)
            (unimplemented-sage-command sage))
           ((indexsecondary)
            (unimplemented-sage-command sage))
           ((dynamic-left-margin)
            (unimplemented-sage-command sage))
           ((permanentstring)
            (unimplemented-sage-command sage))
           ((note)
            (unimplemented-sage-command sage))
           ((bar)
            (unimplemented-sage-command sage))
           ((replicate-pattern)
            (unimplemented-sage-command sage))
           ((simpletablespecs)
            (unimplemented-sage-command sage))
           ((dictionarytabs)
            (unimplemented-sage-command sage))
           ((endexamplecompiledprologue)
            (unimplemented-sage-command sage))
           ((collect-right-flushing)
            (unimplemented-sage-command sage))
           ((plainheadingsnow)
            (unimplemented-sage-command sage))
           ((pagefooting)
            (unimplemented-sage-command sage))
           ((pageref)
            (unimplemented-sage-command sage))
           ((force-line-break)
            `(br))
           ((plainheadings)
            (unimplemented-sage-command sage))
           ((blocklabel)
            (unimplemented-sage-command sage))
           ((pageheading)
            (unimplemented-sage-command sage))
           ((subsection)
            `(h3 ,(caar (sage-command-parameter sage))))
           ((make)
            (unimplemented-sage-command sage))
           ((newpage)
            (unimplemented-sage-command sage))
           ((ignore-white-space)
            ;; TODO
            `(span))
           ((literal-space)
            " ")
           ((value)
            (let ((p (car (sage-command-parameter sage))))
              (string-append "value " p)))
           ((common-lisp:string lisp:string)
            (unimplemented-sage-command sage)) ;; (parameter  ((doctitle ("Symbolics Version Control Design and Implementation"))))
           ((l) ;; string for lisp reading
            `(code ,(caar (sage-command-parameter sage))))
           ((abbreviation-period)
            (unimplemented-sage-command sage))
           ((include)
            (unimplemented-sage-command sage)) ;; (parameter ("/dess/doc/bp/frontm.mss"))
           ((blankspace) ;; vertical blank space
            ;;(format #t "blank space ~s~%" sage)
            (let* ((el (car (sage-command-parameter sage)))
                   (count (if (= (length el) 3) (second el) (first el)))
                   (unit (if (= (length el) 3) (third el) (second el)))
                   (height (case unit
                             ((lines)
                              (string count "em"))
                             ((inches)
                              (string count "in"))
                             ((cm)
                              (string count "cm"))
                             (else
                              (error "unknown blank space unit" unit sage)))))
              `(div (@ (class "blankspace"))
                    (@ (style ,(string-append "height: " height ";"))))))
           ((index)
            ;; TODO: not sure how to handle these properly
            `(span))
           ((lisp:case)
            (unimplemented-sage-command sage))
           ((missing-special-character)
            (unimplemented-sage-command sage))
           ((tabclear)
            (unimplemented-sage-command sage))
           ((tabset)
            (unimplemented-sage-command sage))
           ((tab-to-tab-stop)
            *marker-tab-to-tab-stop*)
           (else
            (error "unknown sage command" (sage-command-name sage) sage))))
        ((sage-reference? sage)
         (let ((appearance (sage-reference-appearance sage))
               (topic (sage-reference-topic sage))
               (type (sage-reference-type sage))
               (booleans (sage-reference-booleans sage)))
           ;; (format #t "booleans for ~a: ~s~%" topic booleans)
           (case appearance
             ((common-lisp:nil lisp:nil ())
              (let ((callee-type (sage-record-callee-type (*current-record*) (sage-reference-unique-id sage))))
                (case callee-type
                  ((#f)
                   (error "cannot find callee for reference" sage))
                  ((topic)
                   `(span "\"" (a (@ (href "")) ,(format-sage-reference-topic sage)) "\""))
                  ((expand)
                   (include-sage-reference sage))
                  ((precis)
                   ;; TODO
                   `(span "\"" (a (@ (href "")) ,(format-sage-reference-topic sage)) "\"")
                   ;; `(span "Sage Reference: Precis of " ,(format-sage-reference-topic sage))
                   )
                  ((crossreference)
                   ;; TODO
                   `(span "Sage Reference: Crossreference of " ,(format-sage-reference-topic sage)))
                  ((contents)
                   ;; TODO
                   `(span "Sage Reference: Contents of " ,(format-sage-reference-topic sage))
                   (include-sage-reference sage))
                  ((operation)
                   ;; TODO
                   `(span "Sage Reference: Operation of " ,(format-sage-reference-topic sage)))
                  (else
                   (if (string? callee-type)
                       (cond ((string=? callee-type "CrossRef")
                              ;; TODO
                              `(span "Sage Reference: CrossRef of " ,(format-sage-reference-topic sage)))
                             ((string=? callee-type "crossref")
                              ;; TODO
                              `(span "Sage Reference: crossref of " ,(format-sage-reference-topic sage)))
                             ((string=? callee-type "Expand")
                              ;; TODO
                              `(span "Sage Reference: Expand of " ,(format-sage-reference-topic sage))
                              (include-sage-reference sage))
                             (else
                              (error "unknown sage reference callee type" callee-type sage)))
                       (error "unknown sage reference callee type" callee-type sage))))))
             ((invisible)
              "" ;; how do we handle this?
              )
             ((topic)
              `(span "\"" (a (@ (href "")) ,(format-sage-reference-topic sage)) "\""))
             ((see)
              `(span ,(if (memq 'initial-cap booleans) "S" "s") "ee the " ,(symbol->string type) " " (a (@ (href "")) ,(format-sage-reference-topic sage)) ,(if (memq 'final-period booleans) "." ""))))))
        ((sage-picture? sage)
         (let ((sxml (picture->sxml sage)))
           `(div (@ (class "picture"))
                 ;; (p ,(format #f "~s" sxml))
                 ,sxml
                 (p "picture name: " ,(sage-picture-name sage)))))
        ((sage-example-record-marker? sage)
         `(div (@ (class "example-record-marker"))
               "Sage example record marker"))
        ((eq? sage *paragraph-marker*)
         `(br))
        (else
         (error "unknown sage thing" sage))))

(define (format-sage-record-title record)
  (let ((name (sage-record-name record))
        (source-title (assq 'source-title (sage-record-fields record))))
    ;; (if (and (pair? source-title) (pair? (cdr source-title)) (pair? (cadr source-title)) (string? (caadr source-title)))
    ;;     (caadr source-title)
    ;;     name)
    (if (and (pair? source-title)
             (> (length source-title) 0))
        (cons 'span (map sage->sxml (fix-up-special-markup (if (and (= (length source-title) 1)
                                                                    (list? (cadr source-title)))
                                                               (caadr source-title)
                                                               (cadr source-title)))))
        name)))

(define (record->sxml record)
  (parameterize ((*current-record* record))
    (let ((contents (second (assq 'contents (sage-record-fields record)))))
      `(section (h1 ,(format-sage-record-title record))
                ,@(map sage->sxml (fix-up-special-markup contents))))))

;; .figure, .picture { background: #dfd; }
(define css "
.commentary { color: #aaa; }
.center { margin: auto; text-align: center; }
.display { margin: 1em 2em; }
.unknown-sage-command { background-color: red; }
.unknown-sage-environment { background-color: red; }
.example { margin: 1em 2em; }
.nex-tab { margin-left: 3em; display: inline-block; }
.nex-paragraph { margin-top: 0.5em; margin-bottom: 1em; }
@font-face {
font-family: 'cptfont';
  src: url('cptfont.woff') format('woff');
}
@font-face {
  font-family: 'cptfont';
  src: url('cptfonti.woff') format('woff');
  font-style: italic;
}
@font-face {
  font-family: 'cptfont';
  src: url('cptfontb.woff') format('woff');
  font-weight: bold;
}
body {
  font-family: 'cptfont';
  font-size: 18pt;
  line-height: 12pt;
}
code { font-family: 'cptfont'; }
")

(define (record->file record filename)
  (let ((sxml `(html (head (meta (@ (charset "utf-8"))))
                     (body (style ,css)
                           ,(record->sxml record)))))
    (with-output-to-file filename (lambda () (sxml->html sxml)))))

(define (find-picture name)
  (filter (lambda (p) (string=? name (sage-picture-name p))) *pictures*))

(define (decode-picture name-or-picture)
  (let ((p (if (sage-picture? name-or-picture) name-or-picture (car (find-picture name-or-picture)))))
    (if p
        (let ((d (sage-picture-decoded p)))
          (if d
              d
              (let ((decoded (binary-decode-graphics-into-forms (make-myport (sage-picture-contents p) 0))))
                (set-sage-picture-decoded! p decoded)
                decoded)))
        (error "picture not found" name-or-picture))))

(define (records->file records filename)
  (let ((sxml `(html (head (meta (@ (charset "utf-8"))))
                     (body (style ,css)
                           ,@(map (lambda (x) (record->sxml x)) (filter (lambda (r) (eq? (sage-record-type r) 'section)) records))))))
    (with-output-to-file filename (lambda () (sxml->html sxml)))))

(define (reset-decoded-pictures)
  (for-each (lambda (p) (set-sage-picture-decoded! p #f)) *pictures*))

(define (sage-record-unique-id record)
  (cadr (assq 'unique-id (third (sage-record-index record)))))

(define (recode-genera-characters str)
  (define (ensure-string x)
    (if (string? x)
        x
        (char->string x)))
  (define chars `(("\215\215" ,*paragraph-marker-string*)
                  (#\U+8D ,*line-break-string*)
                  (#\U+00 "·")
                  (#\U+01 "↓")
                  (#\U+02 "α")
                  (#\U+03 "β")
                  (#\U+04 "∧")
                  (#\U+05 "¬")
                  (#\U+06 "ε")
                  (#\U+07 "π")
                  (#\U+08 "λ")
                  (#\U+09 "γ")
                  (#\U+0a "δ")
                  (#\U+0b "↑")
                  (#\U+0c "±")
                  (#\U+0d "⊕")
                  (#\U+0e "∞")
                  (#\U+0f "∂")
                  (#\U+10 "⊂")
                  (#\U+11 "⊃")
                  (#\U+12 "∪")
                  (#\U+13 "∩")
                  (#\U+14 "∀")
                  (#\U+15 "∃")
                  (#\U+16 "⊗")
                  (#\U+17 "⇆")
                  (#\U+18 "←")
                  (#\U+19 "→")
                  (#\U+1A "≠")
                  (#\U+1B "⋄")
                  (#\U+1C "≤")
                  (#\U+1D "≥")
                  (#\U+1E "≡")
                  (#\U+1F "∨")
                  ))
  (fold (lambda (el res)
          ;;          (format #t "res: ~s~%" res)
          (let ((r (string-replace-string-all res (ensure-string (car el)) (cadr el))))
            ;;            (format #t "-> ~s~%" r)
            r))
        str
        chars))

(define *records-by-index* #f)
(define (make-global-record-index)
  (define indices (map recode-genera-characters (car (read-file "/home/nex/scheme/compressed-record-groups.scm"))))
  (set! *records-by-index* (make-vector (length indices) #f))
  (for-each (lambda (topic i)
              (when (sage-function-spec? topic)
                (set! topic (sage-function-spec-name topic)))
              (let ((r (hash-table/get *records-by-name* topic #f)))
                (vector-set! *records-by-index* i r)
                (hash-table/put! *records-by-id* i r)))
            indices
            (iota (length indices))))

(define (sage-record-contents record)
  (cadr (assq 'contents (sage-record-fields record))))

(define *paragraph-marker* (list 'marker))
(define (split-out-paragraph-markers lst)
  (define (split-individually item)
    (if (string? item)
        (my-split-string item *paragraph-marker-string* *paragraph-marker*)
        (list item)))
  (apply append (map split-individually lst)))

;; TODO: section "Getting Help in the Command Processor" has an instance of line breaks influencing tabbing.
;; It is not rendered correctly with the following.. not sure if it can be :-/
(define (fix-up-tabs lst)
  (let loop ((lst lst)
             (this-tab #f)
             (result '()))
    (if (null? lst)
        (reverse (if this-tab
                     (cons (make-sage-envr 'nex-tab-to-tab-stop '() (reverse this-tab)) result)
                     result))
        (let ((el (car lst)))
          (cond ((and (sage-command? el)
                      (eq? 'tab-to-tab-stop (sage-command-name el)))
                 (loop (cdr lst)
                       (or this-tab '())
                       result))
                ((eq? *paragraph-marker* el)
                 (loop (cdr lst)
                       #f
                       (cons el (cons (if this-tab (make-sage-envr 'nex-tab-to-tab-stop '() (reverse this-tab)) el) result))))
                (else
                 (loop (cdr lst)
                       (if this-tab (cons el this-tab) this-tab)
                       (if this-tab result (cons el result)))))))))

(define (fix-up-paragraphs lst)
  (if (memq *paragraph-marker* lst)
      (let loop ((lst lst)
                 (this-p #f)
                 (result '()))
        (if (null? lst)
            (let ((p (if this-p (filter (lambda (x) (or (not (string? x)) (not (string-null? x)))) this-p) this-p)))
              (if (or (not p) (null? p))
                  (reverse result)
                  (reverse (cons (make-sage-envr 'nex-paragraph '() (reverse p)) result))))
            (let ((el (car lst)))
              (if (eq? *paragraph-marker* el)
                  (loop (cdr lst)
                        #f
                        (let ((p (if this-p (filter (lambda (x) (or (not (string? x)) (not (string-null? x)))) this-p) this-p)))
                          (if (or (not p) (null? p))
                              (reverse result)
                              (reverse (cons (make-sage-envr 'nex-paragraph '() (reverse p)) result)))))
                  (loop (cdr lst)
                        (cons el (or this-p '()))
                        result)))))
      lst))

(define (fix-up-special-markup lst)
  ;;(fix-up-tabs (split-out-paragraph-markers lst))
  (fix-up-paragraphs (fix-up-tabs (split-out-paragraph-markers lst))))
