/-
np3wj; https://github.com/pniroj/cs2120f21.git

Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro --This proof is done using the introduction rule of true QED

example : false :=     -- trick question? why? There is no proof for false QED
/-
First we assume that we have a proposition P. Then we break down the
bi-implication with if and only if. We are left with two implications
(forward and backword). For the forward direction we assume another proposition
and apply the OR elimination. We get another implication so we assume
a proposition. For the backward direction we assume a proposition
and apply OR left introduction rule.
-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
end
/- We assume P and apply the iff intro rule to seperate
forward and backward. For the forward direction, we assume a
propostion and apply AND elimination left to this proposition.
For the backward direction, we start with an assumption of P and
apply the introduction rule of AND.
-/
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
assume P,
apply iff.intro,
--forward
assume porp,
exact and.elim_left porp,
--backward
assume P,
apply and.intro P,
exact P,
end
/-
We assume that we have a proposition P and Q, and apply the
iff intro rule to break down the bi-implication. For forward 
we assume a proposition and do case analysis. After the case analysis we have
Q ∨ P so we aply the OR introduction rule left and right. For backward
we repeat the same process.
-/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
  assume pork,
  cases pork,
  apply or.intro_right,
  exact pork,
  apply or.intro_left,
  exact pork,
--backward
assume porke,
cases porke,
apply or.intro_right,
exact porke,
apply or.intro_left,
exact porke,
end
/-
We assume we speciic propositions P and Q and apply iff intro rule.
For the forward direction, we use the AND elimination to pq and
the AND introduction rule q p. For the backward direction, we use
AND elimination as well as AND introduction rule to form a proof
of P ∧ Q.
-/
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
assume P Q,
apply iff.intro,
--forward
assume pork,
have p : P := and.elim_left pork,
have q : Q := and.elim_right pork,
exact and.intro q p,
--backward
assume porke,
have p : P := and.elim_right porke,
have q : Q := and.elim_left porke,
exact and.intro p q,
end
/-
We assume specific propositions P Q R and apply iff intro. For the
forward direction, we apply AND left elimination and AND right
elimination. Then we do case analysis
-/
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forward
  assume pork,
  have p : P := and.elim_left pork,
  have q : Q ∨ R := and.elim_right pork,
  cases q with a b,
  have porke : P ∧ Q := and.intro p a,
  



end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forward
  assume pork,
  have p : P := or.intro_left pork,
  have q : Q ∨ R := 
  
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
assume P Q,
apply iff.intro,
--forward
assume pork,
apply and.elim_left pork,
--backward
assume porke,

end
/-
We assume specific propositions P Q and apply iff intro rule.
For the forward direction, we assume a propostion pork and do
case analysis with porke for P ∨ P ∧ Q. We apply the left AND
elimination. For the backward direction, we assume another prop
porko and apply OR left introduction to (P ∧ Q)
-/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
  assume pork,
  cases pork with porke,
  exact porke,
  exact and.elim_left pork,
  --backward
  assume porko,
  exact or.intro_left (P ∧ Q),

end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  --forward
  assume pork,
  cases pork with a b,
  
  --backward

end
/-
We assume a specific proposition P and apply iff intro rule. 
For forward, we do case analysis and use false elimination rule. 
For backward, we apply OR introduction left after assuming a
proposition.
-/
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  --forward
  assume pork,
  cases pork with a b,
  exact a,
  exact false.elim b,
  --backward
  assume porke,
  apply or.intro_left,
  
end
/-
We assume a specific proposition P and apply iff intro rule.
For the forward direction, we apply AND elimination left to get
P ∧ true. For the backward direction, we apply AND introduction and 
true introduction to P ∧ true.
-/
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  --forward
  assume pork,
  apply and.elim_left pork,
  --backward
  assume porke,
  apply and.intro porke true.intro,
end
/-
We assume a specific proposition P and apply iff introduction.
For the forward direction, we use the and elimination right to deduce
P ∧ false = false. For the backward direction, we begin with false
and apply the false elimination rule to get P ∧ false. Then we aply
the AND introduction rule to P.
-/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  --forward
  assume pork,
  exact and.elim_right pork,
  --backward
  assume porko,
  have p : P := false.elim porko,
  apply and.intro p porko,
end


