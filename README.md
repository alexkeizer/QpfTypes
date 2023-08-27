
# A (co)datatype package for Lean 4, based on Quotients of Polynomial Functors

This library implements a `codata` command, which can be used to define *coinductive* types in [Lean 4](https://leanprover-community.github.io/)
using a syntax similar to `inductive`. For example, the following specifies a type of (potentially)
infinite lists.

```lean4
/-- Infinite lists -/
codata Stream α 
  | cons : α → CoList α → CoList α
```
```lean4
/-- Potentially infinite Lists -/
codata CoList α
  | nil : CoList α
  | cons : α → CoList α → CoList α
```

The framework is *compositional*, so we can use `CoList` in subsequent specifications.

```lean4
/-- Potentially infinite trees -/
codata CoTree α 
  | node : α → CoList (CoTree α) → CoTree α 
```

We can even mix induction and coinduction. However, the framework used by `codata` does not play
nice with `inductive`. So, the library also provides a `data` command for inductive types, using
that same framework.

```lean4
/-- Infinitely branching, finite depth trees
    That is, one node may have infinitely many children, 
    but the depth of the tree is limited.
-/
data CoTree α 
  | node : α → CoList (CoTree α) → CoTree α 
```


# Live and Dead variables

Binders without any type ascription, such as in the examples so far, are called *live* parameters and assumed to live in `Type _`, where the universe level is inferred.
Note that this universe level is the same for all live parameters.

Conversely, binders that do specify a type, even if that type is `Type _` are *dead* parameters.

This distinction becomes important for subsequent definition: it is only allowed to nest (co)induction behind live parameters. It is thus best to leave out type ascription where possible. That said, live variables have a few more restrictions in where they may appear.

```lean4
codata CoList' (α : Type _) -- In this definition, `α` is a dead parameter
  | nil : CoList' α 
  | cons : α → CoList' α → CoList' α

/-- The following is not accepted: 
    It not allowed to nest a corecursive occurrence of the type to be defined 
    behind `CoList'`, when its parameter is defined as dead.
-/
codata CoTree (α : Type _)
  | node : α → CoList' (CoTree α) → CoTree α 
  --           ^^^^^^^^^^^^^^^^^^ <-- this is where it goes wrong
```

Reusing the type ascription to distinguish live/dead variable is not ideal; in future we'll either introduce dedicated syntax, or automatically determine which variables can be live and which have to be dead.



# Limitations

The implementation is intended as a proof-of-concept. It is still very rough, and not at all ready for serious use.

Fundamentally, (co)recursive families of types or even mutually (co)inductive types are not supported yet, and the only way to define (total) (co)recursive functions is through the low-level `MvQPF.Fix.drec` and `MvQPF.Cofix.corec` (co)recursion principles.

Beyond this, the implementation is far from perfect and might throw errors for specifications that should be supported. Feel free to open issues for any such specifications.


# Try it Out

You can clone https://github.com/alexkeizer/qpf4-example for an example project that imports this package. There is also https://gitpod.io/#https://github.com/alexkeizer/qpf4-example, allowing you to play with codatatypes directly in your browser, no setup needed.



# Organization

TODO





# References

For a thorough discussion about the foundations and implementation of this library, see the accompanying MSc. Thesis by Alex C. Keizer: [Implementing a definitional (co)datatype package in Lean 4, based
on quotients of polynomial functors](https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf)


The foundations of this library come from [avigad/qpf](https://github.com/avigad/qpf).
There it was described as
>  This repository contains a formalization of data type constructions in Lean, by Jeremy Avigad, Mario Carneiro, and Simon Hudon. A       preliminary version of the work is described in this talk: [http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf](http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf).

