-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption, --test exact on every variable
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  --forward
  assume notPandQ,
  have PornotP := classical.em P,
  have QornotQ := classical.em Q,
  cases PornotP,
  cases QornotQ,
  have PandQ := and.intro PornotP QornotQ,
  contradiction,
  apply or.intro_right,
  exact QornotQ,
  cases QornotQ,
  apply or.intro_left,
  exact PornotP,
  apply or.intro_left,
  exact PornotP,
  --backward
  assume notPornotQ,
  assume PandQ,
  cases notPornotQ,
  cases PandQ,
  contradiction,
  cases PandQ,
  contradiction,
  
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume notPornotQ,
  apply and.intro,
  have PornotP := classical.em P,
  assume p,
  cases PornotP,
  have PorQ := or.intro_left Q p,
  contradiction,
  contradiction,
  have QornotQ := classical.em Q,
  cases QornotQ,
  have PorQ : P ∨ Q := begin
    apply or.intro_right,
    exact QornotQ,
  end,
  contradiction,
  exact QornotQ,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  --forward
  assume PornotP,
  cases PornotP,
  apply or.intro_left,
  exact PornotP,
  cases PornotP,
  apply or.intro_right,
  exact PornotP_right,
  --backward
  assume PorQ,
  apply or.intro_left,
  have PorQ := classical.em P,
  cases PorQ,
  exact PorQ_1,
  have PorQ_1 := classical.em P,
  contradiction,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  --foward
  assume PorQ,
  have andElim := and.elim_left PorQ,
  have andElim2 := and.elim_right PorQ,
  cases PorQ,
  apply or.intro_left (Q∧R),
  
  --backward
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  assume p,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃(n : ℕ), n ≠ 0 :=
begin
  apply exists.intro _ _,
  exact 1010,
  assume p,
  cases p,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume PimpQ,
  have PorNP := classical.em P,
  cases PorNP with p np,
  have QorNQ := (PimpQ p),
  exact or.intro_right (¬P) QorNQ,
  exact or.intro_left Q np,
  assume NPimpQ,
  assume p,
  cases NPimpQ with np q,
  exact false.elim (np p),
  exact q,
  
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume p,
  assume q,
  assume notP,
  have f := p notP,
  exact q f, 
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume Imp,
  assume notImp,
  --forward
  have PorQ := classical.em P,
  cases PorQ,
  exact PorQ,
  contradiction,
end

