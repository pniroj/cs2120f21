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
First we assume that we have a proposition P and a proof of P ∨ P. P ∨ P
results in true
-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end
/- We assume P and apply the iff intro rule to seperate
forward and backward. For the forward direction, we assume porp

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

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
apply iff.intro,
--forward
assume pork,
cases pork,
apply and.elim_left pork,
--backward


end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  assume pork,
  
  
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forward
  
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,

  



end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  --forward
  assume pork,
  exact and.elim_right pork,
  --backward
  assume porko,
  exact and.elim_left porko,
end


