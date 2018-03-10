
# Stacky

Stacky was a postscript inspired stack language. 


The project had a simple purpose: try to make a programming language and fail fast to learn from it. 

Some relative success came along the way. The implementation is not optimized at all. I also changed directions numerous times. I stalled when I attempted to introduce types.

# code samples

## Comments 
```stacky
% comments start with a percent signe 
```

Multiline comments are buggy in the last implementation.
```stacky
%( Multiple 
   line
   comments )%
```

## Literals

- Booleans
```stacky
true
false
```

- Strings:
```stacky
"hello world!\n"
```

- Raw Strings:
```stacky
r"\n is not escaped here"
```

- Integers:
```stacky
1 2 
```

- Floats:
```stacky
1.2 3.14
```

- Arrays: sequence delimited by parentheses
```stacky
( 1 2 3 )
```

- Dictionaries: sequence of pairs delimeted by squared brackets
```
stacky> [ 1 "hello" 2 "world" ]
[2i: "world", 1i: "hello"]
```

- Functions: sequence of literals within curly braces
```stacky
{ 5 + }
```

Anything else refers to a symbol defined in a global or local dictionary.

Symbols can be escaped so as to not be interpreted by prefixing them by a `/`. This can be used in conjonction with `def` to define variables.
```
/hello "hello" def
```
## Function examples

- A sum

```stacky
/sum {
    0 swap { + } for-all
} def
```

- A range function 

```stacky
/range { 
    () 3 swapn { 
        swap push 
    } for 
} def

1 1 10 range sum print-ln
```

- Test a predicate holds for all the values within an array. 

```stacky
/all { 
    /proc   swap def 
    /array  swap def
    /status true def
    
    array { 
        proc true = not { 
            /status false def 
        } if 
    } for-all
    
    status
} def 

( 1 2 3 ) { 5 < } all
```

- Test that one element of an array satisfies a given predicate.

```stacky
/any { 
    /proc   swap def 
    /array  swap def
    
    array { 
        proc true = { 
            true 
            return
        } if 
    } for-all
} def 

( 1 2 3 ) { 5 < } any
```

- The `map` function

```stacky
/map {
    /proc   swap  def
    /source swap  def
    /target  ()   def 

    source { proc target push } for-all

    target
} def
```

- The `filter` function

```stacky
/filter {
    /proc   swap def
    /source swap def 
    /target  ()  def

    source {
        dup proc true =
        { target push } { drop } if-else
    } for-all
    
    target
} def
```
