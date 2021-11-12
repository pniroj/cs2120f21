Introduction rule - rule that creates a proof
intro rule - uses the reflexive rule
- Introductionrule for ANd takes in a proof of P and a proof of Q separetely
and constructs a proof of (P and Q)
Ex:

axiom eq_refl  : 
  ∀ (T : Type)  -- if T is any type (of thing)
    (t : T),    -- and t is thing of that type, T
  t = t         -- the result type: proof of t = t

/- For all proposition- assume you're given an arbitrary type and use an arbitrary value to conduct proof


Elimination rule - uses a proof (creates a proof of equality)
Elimination rule for and: if you have a proof of P and Q, you can use
Elimination rule left to break it down and get a proof of P
Conjecture- proposition you believe is true but don't have proof

Definition- 

proposition- any claim about the world
that can be true or false or unknown

predicate- proposition with parameters

axiom- proposition that you just accept
as true (symmetry and transitivity)

theorem- proposition for which you have
a proof (reflexivity and subsitutability)

axiom wrong: 1 = 0

example : 1 = 0 := wrong

conjuction- proof that uses and (^ operator)

~P = not P (If ~P is true, then P is false)

First, if ~P is true, there should be a proof of it. Second,
what that proof should show is that there can be no proof of P.

e.i. ~0 = 1 is true

Saying that P has a proof that equals true when it is actually false is a contradiction

If P → False is true then there is no proof of P

THERE IS NO PROOF FOR FALSE!
-/
example: false → false :=
begin
  assume f,
  exact f,
end


example: false → true :=
begin
  assume f,
  exact true.intro,
end

example: true → false :=
begin
  assume t,
end

--** if your goal is ~P, remember P → F, assume P is true, show false **

example: true → true :=
begin
  assume t,
  cases t,
end

--Elimination rule for proof of false:
example: ¬(0 = 1) :=
begin
  assume h,
  cases h,
end

example: false → false :=
begin
  assume f,
  exact false.elim f,
end

theorem false_elim (P: Prop) (f: false) :P :=
begin
  cases f,
exact false.elim f,
end

theorem no_contradiction : ∀(P : Prop), ¬(P ∧ ¬P) :=
begin
assume P,
assume h,
have p :=h.left,
have np :=h.right,
have f := np p,
exact f,
end

axiom excluded_middle: ∀(P : Prop), (P ∨ ¬P) :=

example : ∀ (P : Prop), P ∨ P ↔ P :=
begin
assume P,
apply iff.intro,
--forward
assume pork,
cases pork,
exact pork,
--backward

end

example : 0 ≠ 1 :=
begin
  -- ¬(0 = 1)
  --(0 = 1) → false
  assume p,
  cases p,
end

example : 0 ≠ 0 → 2 = 3 :=
begin
assume p,
have f : false := p (eq.refl 0),
exact false.elim(p(eq.refl 0)),
-- have f : false := p
-- ¬(0 = 0)
-- (0 = 0) → false
end

example : ∀(P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  apply false.elim f,
end

theorem neg_elim : ∀(P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  -- case analysis
  -- excluded middle (em)
  have pornp := classical.em P,
  cases pornp with p np,
  assumption,
  contradiction,
end

-- pythagoren triple: takes in 3 arguments
def pt (a b c: ℕ): Prop :=
a*a + b*b = c*c
example: pt 3 4 5 :=
begin
unfold  pt,
apply eq.refl,
end

∃(N : ℕ): prime m ∧ ev n → Prop :=
-- YOU NEED A WITNESS AND A PROOF FOR ∃ 
-- give an arbitrary variable (w)
-- use w to prove

memorize all the formulas i n lecture 18

have foo : k = 1 := sorry,

well order - total order with the condition that for any set of
defined values (non-empty) there is a element in s, smaller
than every other element in s