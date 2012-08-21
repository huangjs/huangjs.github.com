---
layout: post
title: "Implemeting TCO 'defun' and 'labels' in Common Lisp"
date: 2011-06-20 14:49
comments: true
categories: [lisp, programming]
---
(This is an old blog, I didn't blog much, maybe only when I'm drunk, which is rare...Now I need to do more, so hope this a good begining :)

Two weeks ago, a post from the Lisp-cn mailing list asked whether
Emacs's elisp implementation supports tail-call optimization. Though
the answer turned out to be "nope", I broke into the conversation and
said he could implement his own version of abstraction easily in Lisp.

Then I followed up a new post of a small quiz for implementing
tail-call optimized (but crippled) "defun" (or "define" for Schemes).
Maybe because it's not a very interesting quiz, only one person showed
up with his solution, and eventually it became my own amusement.
However, the result that shows the optimization done by several Common
Lisp implementations is not boring at least. And it can be of help
when using implementations that doesn't do tail-call optimization such
as ABCL or ECL.

### Task 1 Self-recursion Optimization

> Write a macro called "defun-tc" that does similar things (define a toplevel function) as "defun" but also does forced tail-call optimization when calling itself recursively.

This is a very simple one. Tail-calls are in fact gotos, but in a structured way. The point is to shadow the function definition with a local macro (nlet-tc as follows) that expands to goto.

``` common-lisp
(defmacro nlet-tc (name bindings &body body)
  (alexandria:with-unique-names (entry return)
    (let* ((bindings (mapcar #'alexandria:ensure-list bindings))
           (vars (mapcar #'first bindings)))
      `(macrolet ((,name (&rest args)
                    `(progn
                       (psetf ,@(mapcan #'list ',vars args))
                       (go ,',entry))))
         (let ,bindings
           (block ,return
             (tagbody
                ,entry
                (return-from ,return
                  (locally ,@body)))))))))

(defmacro defun-tc (name args &body body)
  `(defun ,name ,args
     (nlet-tc ,name ,(mapcar (lambda (a) `(,a ,a)) args)
       ,@body)))
To make it more explicit, here's an example.

(defun-tc sum (n acc)
  (declare (fixnum n acc)
           (optimize speed (safety 0)))
  (if (< = n 0)
      acc
      (sum (- n 1) (+ acc n))))
```

when expanded, will be:

```common-lisp
(DEFUN SUM (N ACC)
  (MACROLET ((SUM (&REST ARGS)
               `(PROGN
                 (PSETF ,@(MAPCAN #'LIST '(N ACC) ARGS))
                 (GO #:ENTRY967))))
    (LET ((N N) (ACC ACC))
      (BLOCK #:RETURN968
        (TAGBODY
         #:ENTRY967
          (RETURN-FROM #:RETURN968
            (LOCALLY
             (DECLARE (FIXNUM N ACC)
                      (OPTIMIZE SPEED (SAFETY 0)))
             (IF (< = N 0)
                 ACC
                 (SUM (- N 1) (+ ACC N))))))))))
```

The following benchmark

```common-lisp
(defun-tc test (n acc)
  (declare (fixnum n acc)
           (optimize speed (safety 0)))
  (if (< = n 0)
       acc
       (test (1- n) (1+ acc))))
(time (test (expt 2 32)))
=> 4294967296
```

showed there's a little bit more overhead than SBCL's native implementation. After examination the assembly code, it turned out that in my version SBCL wil treat (1- n) and (1+ acc) as machine integer rather than fixnum as declared, and the 4 redundant shifts are the only overhead. After adding (the fixnum ...) to both form, the difference disappeared.

A natural improvement is to automatically add the type declaration in the "psetf" form, the following trick does that, though it turned out to be less useful in the next task.

```common-lisp
(defun variable-type (var &optional env)
  nil
  #+sbcl (cdr (assoc 'cl:type (nth-value 2 (sb-cltl2:variable-information var env)))))

(defmacro my-psetf (&environment env &rest args)
  (assert (and (> (length args) 0)
               (evenp (length args))))
  (multiple-value-bind (places vals newvars)
      (loop with e = args
            while e
            collect (pop e) into places
            collect (pop e) into vals
            collect (gensym "NEW") into newvars
            finally (return (values places vals newvars)))
    `(let* ,(mapcar (lambda (p v n)
                     (if (and (symbolp p)
                              (variable-type p env))
                         `(,n (the ,(variable-type p env) ,v))
                         `(,n ,v)))
                   places vals newvars)
       (setf ,@(mapcan #'list places newvars)))))
```

Change "psetf" to "my-psetf" and the type information will be propagated in compile-time.

### Task 2 Mutual-recursion Optimization

> Write a macro called "labels-tc" that does similar things as "label" but also does forced tail-call optimization when recursively calling functions defined in the same scope.

This task is much more fun. You need to

- Establish tagbody scope that covers all local functions
- Still allow local functions being used in "funcall" and "apply"
- Handle all variables in one scope

My idea is to define an anonymous local function that includes all the definitions, and use a dispatch to jump to the right entry point. All other functions will call the anonymous one. As for variable handling, I currently don't have a good solution without a full renaming. So it's ignored and I simply combined all the variables (maybe an error checking is necessary).

Here's the code:

```common-lisp
(defmacro labels-tc (definitions &body body)
  (multiple-value-bind (names argss bodies jump-tags)
      (loop for d in definitions
            for n = (first d)
            for a = (second d)
            for b = (rest (rest d))
            for j = (gensym (symbol-name n))
            collect n into ns
            collect a into as
            collect b into bs
            collect j into js
            finally (return (values ns as bs js)))
    (alexandria:with-unique-names (entry exit name dispatch)
      `(labels ((,entry (,name &key ,@(remove-duplicates (apply #'append argss)))
                  (macrolet (,@(mapcar (lambda (name args jump-tag)
                                         `(,name (&rest arrrgs)
                                                 `(progn
                                                    (my-psetf ,@(mapcan #'list ',args arrrgs))
                                                    (go ,',jump-tag))))
                                 names argss jump-tags))
                    (block ,exit
                      (tagbody
                         ,dispatch
                         (case ,name
                           ,@(mapcar (lambda (name jump-tag)
                                       `(,name (go ,jump-tag)))
                              names jump-tags))
                         ,@(mapcan (lambda (jump-tag body)
                                     `(,jump-tag
                                       (return-from ,exit
                                         (locally ,@body))))
                                   jump-tags bodies)))))
                ,@(mapcar (lambda (name args)
                            `(,name ,args
                                    (,entry
                                     ',name
                                     ,@(mapcan (lambda (a)
                                                 `(,(alexandria:make-keyword a) ,a))
                                               args))))
                    names argss))
         (locally ,@body)))))
```

So again, example:

```common-lisp
(labels-tc ((oddp (n)
           (declare (fixnum n))
           (if (= n 0)
               nil
               (evenp (1- n))))
         (evenp (m)
           (declare (fixnum m))
           (if (= m 0)
               t
               (oddp (1- m)))))
  (print (oddp 21)))
```

will be expanded to:

```common-lisp
(labels ((#:entry (#:name &key n m)
           (block #:exit
             (tagbody
                #:dispatch
                (case #:name
                  (oddp (go #:oddp))
                  (evenp (go #:evenp)))
                #:oddp
                (return-from #:exit
                  (locally
                      (declare (fixnum n))
                    (if (= n 0)
                        nil
                        (progn
                          (psetf m (1- n))
                          (go #:evenp)))))
                #:evenp
                (return-from #:exit
                  (locally
                      (declare (fixnum m))
                    (if (= m 0)
                        t
                        (progn
                          (psetf n (1- m))
                          (go #:oddp))))))))
         (oddp (n)
           (#:entry 'oddp :n n))
         (evenp (m)
           (#:entry 'evenp :m m)))
  (print (oddp 21)))
```

Note again that this version doesn't handle variables properly except the simplest form. And as mentioned above, my-psetf has no effect here since type declarations are not visible in the scope of labels-tc.

### Benchmark and Verification

Ok, here's the fun part, benchmark and verifying the implementation in different implementations. Here's the benchmark code:

```common-lisp
(defun test (n)
  (declare (fixnum n)
           (optimize speed (safety 0)))
  (labels-tc ((my-oddp (n)
                       (declare (fixnum n))
                       (if (= n 0)
                           nil
                           (my-evenp (the fixnum (1- n)))))
              (my-evenp (m)
                        (declare (fixnum m))
                        (if (= m 0)
                            t
                            (my-oddp (the fixnum (1- m))))))
    (my-evenp n)))

(time (test (expt 2 30)))
=> T
```

And here's the result:

<table border="2" rules="groups" cellspacing="0" cellpadding="6"><colgroup> <col align="left" /> <col align="right" /> <col align="right" /> </colgroup>
<thead>
<tr>
<th scope="col">Common Lisp</th>
<th scope="col">labels version (sec)</th>
<th scope="col">labels-tc version (sec)</th>
</tr>
</thead>
<tbody>
<tr>
<td>SBCL 1.0.48 (64bit)</td>
<td>0.599</td>
<td>0.594</td>
</tr>
<tr>
<td>ABCL 0.25 (OpenJDK 1.6.0<sub>22</sub>)</td>
<td>(java.lang.StackOverflowError)</td>
<td>13.171</td>
</tr>
<tr>
<td>AllegroCL 8.2 64bit</td>
<td>10.17</td>
<td>2.32</td>
</tr>
<tr>
<td>ClozureCL 1.7 64bit</td>
<td>1.664</td>
<td>0.767</td>
</tr>
<tr>
<td>Lispworks 6.0.1 64bit</td>
<td>3.657</td>
<td>2.468</td>
</tr>
<tr>
<td>Clisp 2.48</td>
<td>(Lisp stack overflow. RESET)</td>
<td>27.002</td>
</tr>
<tr>
<td>CMUCL 20B (32bit)</td>
<td>0.57</td>
<td>0.42</td>
</tr>
<tr>
<td>ECL 11.1.1</td>
<td>(Segmentation fault)</td>
<td>16.218</td>
</tr>
</tbody>
</table>

+ OS: Ubuntu natty 11.04 x86_64 (CPU: Core2 3.0GHz)
+ AllegroCL needs compiler flag to turn on the optimization on.
+ Since CMUCL is 32bit, to avoid fixnum overflow, I changed the benchmark to (test (expt 2 28)) and looped 4 times.

What amazed me is that my implementation is among the best with SBCL/CMUCL's, so if your algorithm depends heavily on mutual tail-recursion, you can use this customized labels-tc without changing a single line of your code (but be aware of the variable handling!). And I think the reason other implementations don't optimize enough is because many tail-recursion programs can be intuitively translated into ones using loop, however, in some situations, it is not case.

TODO: Here's the file for download.

