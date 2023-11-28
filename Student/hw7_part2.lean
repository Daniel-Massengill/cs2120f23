/-!
# Exam 1


## HOMEWORK PART 1:

Write three functions
- sat : Expr → Bool
- unsat: Expr → Bool
- valid: Expr → Bool

Given any expression, *e*, in propositional logic, the first returns true
if *e* is sastisfiable, otherwise false. The second returns true if *e* is
unsatisfiable, otherwise false. The third returns true if *e* is valid, and
otherwise returns false. You can write helper functions if/as needed. Write
short comments to explain what each of your functions does. Write a few test
cases to demonstrate your results.
-/

-- Here
def is_sat (e : Expr) : Bool :=
  -- If there exists an interpretation where the expression is true, it's satisfiable
  (truth_table_outputs e).any id

def is_unsat (e : Expr) : Bool :=
  -- If there are no interpretations where the expression is true, it's unsatisfiable
  ¬(truth_table_outputs e).any id

def is_valid (e : Expr) : Bool :=
  -- If the expression is true for all interpretations, it's valid
  (truth_table_outputs e).all id


-- A few tests
#eval is_valid (X)                      -- expect false
#eval is_sat (X)                        -- exect true
#eval is_sat (X ∧ ¬X)                   -- expect false
#eval is_unsat (X ∧ ¬X)                 -- expect true
#eval is_valid (X ∨ ¬X)                 -- expect true
#eval is_valid ((¬(X ∧ Y) ⇒ (¬X ∨ ¬Y))) -- expect true
#eval is_valid (¬(X ∨ Y) ⇒ (¬X ∧ ¬Y))   -- expect true
#eval is_valid ((X ∨ Y) ⇒ (X → ¬Y))     -- expect false

-- Test cases
#eval is_sat (X ∧ Y)                  -- expect true 
#eval is_sat (X ∧ (Y ∨ ¬Z))            -- expect true
#eval is_unsat ((X ∨ Y) ∧ (¬X ∨ ¬Y))   -- expect true
#eval is_valid ((X ∧ Y) → (X → Y))     -- expect true

--Test Case for #4 on Part 2
#eval is_valid ((O ∨ (A ∧ B)) ∨ (A ∧ C)) ⟺ ((A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C)) -- expect true




/-
## Part 2

DO NOT CHEAT.
-/

/-! 
## #1 Easy Functions [15 points]

Define a function, *pythag*, that takes three natural 
numbers, call them *a, b,* and *c*, and that returns
*true* if *a^2 + b^2 = c^2* and that returns *false*
otherwise.
-/

-- Define your function here
def pythag (a b c : Nat) : Prop :=
| a * a + b * b = c * c


-- The following test cases should then pass
#eval pythag 3 4 5  -- expect true
#eval pythag 6 7 8  -- expect false

/-! 
## #2 Recursive Functions

Define a function, sum_cubes, that takes any natural
number, *n*, as an argument, and that retrns the sum
of the cubes of the natural numbers from *1* up to *n*
inclusive.
-/

-- Define your function here
def sum_cubes : Nat → Nat
| 0 := 0
| (n + 1) := (n + 1) ^ 3 + sum_cubes n


-- test case: sum_cubes 4 = 1 + 8 + 27 + 64 = 100
#eval sum_cubes 4   -- expect 100

/-!
## #3 Product and Sum Types

Define two functions, called *prod_ors_to_or_prods*, 
and *or_prods_to_prod_ors* that shows that a product 
of sums be converted into a sum of products in a way
that the result can then be converted back into the
original product of sums. 

As a concrete example, you might want to show that if 
you have an apple or an orange and you have a cup or
a bowl, then you have an apple and a cup or an apple
and a bowl or an orange and a cup or an orange and a
bowl. 

Hints: 1. Be sure you understand the reasoning before
you try to define your functions. 2. Use four cases. 3. 
Use type-guided, top-down programming, assisted by the
Lean prover to work out a solution for each case.  
-/

def prod_ors_to_or_prods {α β γ δ: Type} :
  (α ⊕ β) × (γ ⊕ δ) → α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ 
| (sum.inl a, sum.inl c) := sum.inl (a, c) 
| (sum.inl a, sum.inr d) := sum.inr (sum.inl (a, d)) 
| (sum.inr b, sum.inl c) := sum.inr (sum.inr (sum.inl (b, c))) 
| (sum.inr b, sum.inr d) := sum.inr (sum.inr (sum.inr (b, d))) 


-- Write the second function here from scratch
def or_prods_to_prod_ors {α β γ δ : Type} :
  α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ → (α ⊕ β) × (γ ⊕ δ)
| (sum.inl (a, c)) := (sum.inl a, sum.inl c) 
| (sum.inr (sum.inl (a, d))) := (sum.inl a, sum.inr d)
| (sum.inr (sum.inr (sum.inl (b, c)))) := (sum.inr b, sum.inl c)
| (sum.inr (sum.inr (sum.inr (b, d)))) := (sum.inr b, sum.inr d)


/-!
## #4 Propositional Logic Syntax and Semantics

Extend your Homework #7 solution to implement the
propositional logic *iff/equivalence* (↔) operator.
Note that Lean does not natively define the *iff*
Boolean operator. 
-/
def iff (a b : Bool) : Bool :=
  (a && b) || (!a && !b)

-- Function to check if two expressions are equivalent using custom ↔ operator
def is_equiv (e1 e2 : Expr) : Bool :=
  -- Evaluate the expressions and check if they are equivalent
  iff (truth_table_outputs e1).all id (truth_table_outputs e2).all id

/-!
Using our syntax for propositional logic, and the
variable names *A, O, C,* and *B*, respectively for
the propositions *I have an apple, I have an orange,
I have a cup,* and *I have a bowl* write a proposition
that having an orange or an apple and a bowl or a cup
is equivalent to having an apple and a bowl or an
apple and a cup or an orange and a bowl or an orange
and a cup.

Note: There's no need here to use our implementation
of propositional logic. Just write the expression 
here using the notation we've defined.
-/

((O ∨ (A ∧ B)) ∨ (A ∧ C)) ⟺ ((A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C))

/-!
## #5 Propositional Logic Validity
At the end of your updated Homework #7 file, use our
validity checking function to check your expression
for validity, in the expectation that the checker will
determine that the expression is in fact valid. 
-/