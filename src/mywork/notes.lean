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
Elimination rule for and: if you have a proof of P annd Q, you can use
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