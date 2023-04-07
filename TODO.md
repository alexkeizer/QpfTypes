
# Short term

* Use `fin_cases` instead of `fin_destr`
* Polynomial specialization (i.e., don't use QPFs if pfunctors suffice)
* Change `PFunctor::B` to be the following sum
    ```lean
    inductive Card
      | fin      : Nat → Card
      | infinite : Type u → Card
    ```
    So that the most common case (finitely many datapoints for each parameter) can be encoded as a vector (and thus be amenable to pattern matching)

* Emit `Foo.rec` / `Foo.corec` (co)recursion principles, as specialization of `MvQPF.Fix.rec` / `MvQPF.Cofix.corec`

* Emit `recOn` / `cases` / `casesOn` as wrappers around `Foo.rec` for inductive types


# Long Term

* Primitive corecursion equation compiler
    * Primitive corecursion means emitting exactly one constructor and then corecursing (in the same function)
    * This corresponds to the corecursion principle, but we want to enable writing corecursive equations in an equational style, rather than the state machine approach 

* (Co)Inductive families, mutual induction, and mutual coinduction 
    * Without allowing induction/coinduction mixed in the same mutual block

* More complex corecursion with friends / companions