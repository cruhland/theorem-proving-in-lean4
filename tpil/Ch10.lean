/-= Chapter 10: Type classes =-/

namespace without_typeclasses

structure Add (α : Type) where
  add : α → α → α

#check @Add.add

def double (s : Add α) (x : α) : α :=
  s.add x x

#eval double { add := Nat.add } 10
#eval double { add := Nat.mul } 10
#eval double { add := Int.add } 10

end without_typeclasses

namespace with_typeclasses

class Add (α : Type) where
  add : α → α → α

#check @Add.add

instance : Add Nat where
  add := Nat.add

instance [Add α] : Add (Array α) where
  add x y := Array.zipWith x y Add.add

#eval Add.add #[1, 2] #[3, 4]

end with_typeclasses

namespace inhabited

class Inhabited (α : Type u) where
  default : α

#check @Inhabited.default

instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
#eval (Inhabited.default : Bool)

export Inhabited (default)

#eval (default : Nat)
#eval (default : Bool)

theorem defNatEq0 : (default : Nat) = 0 := rfl

constant arbitrary [Inhabited α] : α := default

-- Fails to type check
-- theorem arbitraryNatEq0 : (arbitrary : Nat) = 0 := rfl

end inhabited

/- Chaining instances -/
namespace chaining_instances

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (arbitrary, arbitrary)

#eval (arbitrary : Nat × Bool)

instance [Inhabited b] : Inhabited (a → b) where
  default := λ _ => arbitrary

-- Exercise
instance : Inhabited (List a) where
  default := []

instance [Inhabited a] : Inhabited (a ∨ b) where
  default := Or.inl arbitrary

instance [Inhabited b] : Inhabited (a ∨ b) where
  default := Or.inr arbitrary

#check (inferInstance : Inhabited Nat)

def foo : Inhabited (Nat × Nat) := inferInstance

theorem ex : foo.default = (arbitrary, arbitrary) := rfl

#print inferInstance

end chaining_instances

/- ToString -/
namespace to_string

structure Person where
  name : String
  age : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 54 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person}, "hello")

end to_string

/- Numerals -/
namespace numerals

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)

#check (2 : Rational)
#check (2 : Nat)

#check nat_lit 2

class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α := 1

end numerals

/- Output parameters -/
namespace output_parameters

#check_failure (inferInstance : Inhabited (Nat × _))

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (λ b => hMul a b)

#eval hMul 4 3
#eval hMul 4 #[2, 3, 4]
#eval hMul (-2) #[3, -1, 4]
#eval hMul 2 #[#[2, 3], #[0, 4]]

end output_parameters

/- Default instances -/
namespace default_instances_failure

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check_failure λ y => xs.map (λ x => hMul x y)

end default_instances_failure

namespace default_instances_success

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[defaultInstance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check λ y => xs.map (λ x => hMul x y)

end default_instances_success

namespace default_instance_override

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[defaultInstance]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2

end default_instance_override

/- Local instances -/
namespace local_instances



end local_instances
