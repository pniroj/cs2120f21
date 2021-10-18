/- 
--np3wj; https://github.com/pniroj/cs2120f21.git

   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

In English: Given propositions, P and Q,
you can use elimination rule left/right
to break down P → Q to get a proof of P. 

(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- → elim
             p2q : p
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume PimpQ,
  exact PimpQ,
end

-- Extra credit [2 points]. Who invented this principle?

-- Theophrastus (student of Aristotle)

-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

-- true.intro 
---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- The introduction rule for true is
unconditonally true and can be proven
using true.intro (in lean). 

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true :=
begin
exact true.intro,
end


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Assuming P and Q are propositions, applying
the introduction rule for ∧ we can have proofs
of P, Q, respectively. 

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.
-/
/-
(P Q : Prop) (pq : P ∧ Q)
------------------------- ∧ elim (left)
        p : P

Assuming P and Q are propositions, we can apply
left AND elimination rule to P ∧ Q to get a proof of p:P

(P Q : Prop) (pq : P ∧ Q)
------------------------- ∧ elim (right)
          q : Q

Assuming P and Q are propositions, we can apply
left AND elimination rule to P ∧ Q to get a proof of q:Q

-/
/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/
/-
Assume arbitrary but specific propostions
P and Q. Again, assume QandP because we have
an implication. Since we have a proof of Q ∧ P
and the goal is P,we can apply AND elimination 
right to QandP. 
-/
example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
assume P Q,
assume QandP,
exact and.elim_right QandP,
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- For the introduction rule for ∀, you assume an arbitrary object
x of Type T and then show Q must be true for any x

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                pf : Q t

-- We have a proof (pf) of ∀ (t : T), Q t.
We know that every t has property Q. We use
the elimination rule for ∀ by applying pf to t, which
then yields a proof that t satisfies the predicate Q.

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- We can use the proof, pf of the ∀ proposition,
to show that any specific value, such as t here, 
has the property Q. We do this by applying the proof
pf to t. This is the elimination rule for ∀. 
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  (Lynn : Person)
  (Person Lynn : KnowsLogic Lynn)
/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀(Lynn: 
begin

end
-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := namespace(P→false) -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- First, if ~P is true, there should be a proof of it. Second,
-- what that proof should show is that there can be no proof of P.

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume _¬P___ and show that __contradiction
___occurs_____.
From this derivation you can conclude __P→false____.
Then you apply the rule of negation __elimination___
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is ___logically___ valid, and that accepting the axiom
of the __excluded middle___ suffices to establish negation
__elimination_____ (better called double
 _____negation _________) as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/
/-
First we assume that we have a proposition P and Q. Then we break down the
bi-implication with if and only if. We are left with two implications
(forward and backward). For the forward direction we assume another proposition
PandQ and apply the AND introduction and elimination left ∧ right rule. For the 
backward direction we assume a proposition Qand P and apply the AND introduction
and elimination left ∧ right rule (same as forward). 
-/
example : ∀ (P Q : Prop), (P ∧ Q) ↔ (Q ∧ P) :=
begin
assume P Q,
apply iff.intro _ _,
--forward
assume PandQ,
apply and.intro,
apply and.elim_right PandQ,
apply and.elim_left PandQ,
--backward
assume QandP,
apply and.intro,
apply and.elim_right QandP,
apply and.elim_left QandP,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/
/-
elantp, ∴, John Lennon is a nice and talented
person and everyone likes John Lennon.   
-/
def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    

example : ELJL :=
begin
  intros,
  unfold ELJL,
  intros,
  have JLN := and.elim_right JLNT,
  have JLT := and.elim_left JLNT,
  apply elantp,
  exact JLT,
  exact JLN,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? _5_
-- list the cases (informaly)
    /- Case #1 and #2- Heavy ∨ Light- Cases where heavy
    can be considered true or light can be considered true

    Case #3 and #4- Red ∨ Blue- Cases where red can be
    considered true or blue can be considered true
    
    Case #5- Proof by cases that every car is rad
    -\

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/
-/
def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T),
  x = y → 
  y = x 

def eq_is_transitive : Prop :=
  ∀ (T: Type) (x y z : T),
  x = y →
  y = z →
  x = z 

/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
∀(P Q: Prop), (¬¬P → P) ↔ (P→(P ∨ ¬P))
example : ∀(P : Prop), (¬¬P → P) ↔ P→(P ∨ ¬P) :=
begin
assume P,
apply iff.intro _ _,
--foward
assume PimpP,
assume p,
exact or.intro_left (¬P) p,
--backward
assume PimpPornotP,
assume nnp,
have PornotP := classical.em P,
cases PornotP with p pn,
assumption,
contradiction,
end

/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h,
  assume e,
  cases h with p pf,
  apply exists.intro p,
  exact (pf e),
end
