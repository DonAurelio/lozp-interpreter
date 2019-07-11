# lozp-interpreter

This repository holds an interpreter in Mozart/Oz of a simple lisp based laguage. This an assigment of the subject *Introduction to programing paradigms* dictated by Nicolás Cardoso, Universidad de los Andes, Bogotá, Colombia.

```oz
(
  (defvar X)
  (defun Fac N
    (if 
    (= N 0)
    (* N (Fact (- N 1)))))
    (unify X (Fact 5))
)
```

```oz
[
  [ defvar X ]
  [ defun fac [ N ]
  [[ conditional [ eq N 0]
  [ multiply N [ fac [ subtract N 1]]]]]]
  [ unify X [ fac 5]]
]
```

## Todo

-[] the *parser.oz* only has the tokenizer step, the parser step is missing.

## Contributors

* Aurelio Vivas
* Paula Siauchò
