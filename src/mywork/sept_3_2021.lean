/-
Theorem: Equality is symmetric
Equality is reflexive and you can 

-/
theorem eq_sym :
∀(T: Type) (x y: T), x = y → y = x :=
begin
  assume(T:Type),
  assume(x y: T),
  assume (e : x = y),
  rw e, 
  /-
  Theorem: Equality is symmetric

  Proof: What we really need to show is that

  ∀(T: Type) (x y: T), x = y → y = x :=

  First we'll assume that T is any type
  and we have objects x and y of this type.
  What remains to shown is that x = y → y =  x.
  To prove this, we'll assume the premise, that
  x = y, and in this context to prove y = x. 
  But by thhe axiom of substitutability of equals,
  and using the fact x = y, we can rewrite x in
  the goal as y, yielding y = y as our new proof
  goal. BUt this is true by the axiomn of 
  reflexivity of equality. OBD.

  For all arbitrary objects of type x and y if x = y then
  y = x because equality is symmetric
  -/

end


/-
Prove that equality is transitive
-/

theorem eq_trans:
 ∀(T: Type) (x y z: T), x = y → y = z → x = z:=
begin
  assume(T:Type),
  assume(x y z: T),
  assume(e1 : x = y),
  assume(e2 : y = z),
  rw e1, 
  rw e2,
end

example: ∀(T : Type), ∀ (x y z : T), x = y → y = z → z = x :=
begin
  /-
  assume T,
  assume (x : T),
  assume (y : T),
  assume (z : T),
  -/
  assume T x y z,
  assume h1 h2,
  apply eq_sym 

end
