import data.set
--np3wj; https://github.com/pniroj/cs2120f21.git
/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 
/-
 (1) What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
If there's a function that maps/takes every α value that
there exists, a function that if α implies β for all
α, a predicate a implies q to function f a, then all
p a implies q b. 
-/
 --(2)  Give your formal proof here
begin
assume firstImp,
assume secImp,
cases firstImp with f qb,
admit,
end
/-
(3) Write an informal proof of the proposition.
There exists a function that if α implies β for all
α, a predicate a implies q to function f a, then all
p a implies q b.
-/