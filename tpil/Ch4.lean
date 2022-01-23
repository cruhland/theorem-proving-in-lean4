/-= Chapter 4: Quantifiers and equality =-/

/- The universal quantifier -/
namespace universal

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  λ h : ∀ x : α, p x ∧ q x =>
  λ y : α =>
  show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

namespace implicit_trans

  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r hab
  #check trans_r hab hbc

end implicit_trans

namespace equivalence_relation

  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r hab (trans_r (symm_r hcb) hcd)

end equivalence_relation

end universal

/- Equality -/
namespace equality

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α β : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans hab (Eq.trans (Eq.symm hcb) hcd)

example : a = d := hab.trans (hcb.symm.trans hcd)

example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl _
example (a b : α) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl
example (a b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

namespace subst_helpers

  variable (α : Type)
  variable (a b : α)
  variable (f g : α → Nat)
  variable (h₁ : a = b)
  variable (h₂ : f = g)

  example : f a = f b := congrArg f h₁
  example : f a = g a := congrFun h₂ a
  example : f a = g b := congr h₂ h₁

end subst_helpers

namespace nat_identities

  variable (a b c d : Nat)

  example : a + 0 = a := Nat.add_zero a
  example : 0 + a = a := Nat.zero_add a
  example : a * 1 = a := Nat.mul_one a
  example : 1 * a = a := Nat.one_mul a
  example : a + b = b + a := Nat.add_comm a b
  example : (a + b) + c = a + (b + c) := Nat.add_assoc a b c
  example : a * b = b * a := Nat.mul_comm a b
  example : (a * b) * c = a * (b * c) := Nat.mul_assoc a b c
  example : a * (b + c) = (a * b) + (a * c) := Nat.mul_add a b c
  example : a * (b + c) = (a * b) + (a * c) := Nat.left_distrib a b c
  example : (a + b) * c = (a * c) + (b * c) := Nat.add_mul a b c
  example : (a + b) * c = (a * c) + (b * c) := Nat.right_distrib a b c

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      Nat.mul_add (x + y) x y
    have h₂ : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
      (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h₁
    h₂.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

end nat_identities

end equality

/- Calculational proofs -/
namespace calculational_proofs

variable (a b c d e : Nat)
variable (h₁ : a = b)
variable (h₂ : b = c + 1)
variable (h₃ : c = d)
variable (h₄ : e = 1 + d)

theorem T : a = e :=
  calc
    a = b     := h₁
    _ = c + 1 := h₂
    _ = d + 1 := congrArg Nat.succ h₃
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h₄

theorem T₂ : a = e :=
  calc
    a = b     := by rw [h₁]
    _ = c + 1 := by rw [h₂]
    _ = d + 1 := by rw [h₃]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h₄]

theorem T₃ : a = e :=
  calc
    a = d + 1 := by rw [h₁, h₂, h₃]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h₄]
  
theorem T₄ : a = e :=
  by rw [h₁, h₂, h₃, Nat.add_comm, h₄]

theorem T₅ : a = e :=
  by simp [h₁, h₂, h₃, Nat.add_comm, h₄]
  
example (h₁ : a = b) (h₂ : b ≤ c) (h₃ : c + 1 < d) : a < d :=
  calc
    a = b     := h₁
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h₂
    _ < d     := h₃

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    _ = (x + y) * (x + y)               := by rfl
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]

end calculational_proofs

/- The existential quantifier -/
namespace existential_quantifier

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

section infer_predicate

  variable (g : Nat → Nat → Nat)
  variable (hg : g 0 0 = 0)

  theorem gex₁ : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex₂ : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex₃ : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex₄ : ∃ x, g x x = 0 := ⟨0, hg⟩

  -- display implicit arguments
  set_option pp.explicit true
  #print gex₁
  #print gex₂
  #print gex₃
  #print gex₄

end infer_predicate

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (λ w => 
     λ hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  λ ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
  Exists.elim h₁ (fun w₁ (hw₁ : a = 2 * w₁) =>
  Exists.elim h₂ (fun w₂ (hw₂ : b = 2 * w₂) =>
    Exists.intro (w₁ + w₂)
      (calc
        _ = a + b           := by rfl
        _ = 2 * w₁ + 2 * w₂ := by rw [hw₁, hw₂]
        _ = 2 * (w₁ + w₂)   := by rw [Nat.mul_add])))

theorem even_plus_even_short
    (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
  match h₁, h₂ with
  | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ => ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

theorem even_plus_even_readable
    (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
  let ⟨w₁, (hw₁ : a = 2 * w₁)⟩ := h₁
  let ⟨w₂, (hw₂ : b = 2 * w₂)⟩ := h₂
  let even_sum := calc
    _ = a + b           := by rfl
    _ = 2 * w₁ + 2 * w₂ := by rw [hw₁, hw₂]
    _ = 2 * (w₁ + w₂)   := by rw [Nat.left_distrib]
  show is_even (a + b) from ⟨w₁ + w₂, even_sum⟩

section classical_exists
  open Classical
  variable (p : α → Prop)

  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction
      (fun h₁ : ¬ ∃ x, p x =>
        have h₂ : ∀ x, ¬ p x :=
          fun x =>
          fun h₃ : p x =>
          have h₄ : ∃ x, p x := ⟨x, h₃⟩
          show False from h₁ h₄
        show False from h h₂)

  example (hnaxnpx : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction λ hnexpx : ¬ ∃ x, p x =>
      suffices caxnpx : ∀ x, ¬ p x from show False from hnaxnpx caxnpx
      show ∀ x, ¬ p x from λ x (hpx : p x) =>
        have cexpx : ∃ x, p x := ⟨x, hpx⟩
        show False from hnexpx cexpx

end classical_exists

end existential_quantifier

/- More on the proof language -/
namespace proof_language

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

example (_ : f 0 ≥ f 1) (_ : f 1 ≥ f 2) : f 0 = f 2 :=
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

example (n : Nat) : Nat := ‹Nat›

end proof_language

/- Exercises -/
namespace ex_1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have fwd : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := λ axpxqx =>
    have axpx : ∀ x, p x := λ x => (axpxqx x).left
    have axqx : ∀ x, q x := λ x => (axpxqx x).right
    show (∀ x, p x) ∧ (∀ x, q x) from ⟨axpx, axqx⟩
  have rev : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) := λ axpxaxqx =>
    have axpx : ∀ x, p x := axpxaxqx.left
    have axqx : ∀ x, q x := axpxaxqx.right
    show ∀ x, p x ∧ q x from λ x => ⟨axpx x, axqx x⟩
  show (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) from ⟨fwd, rev⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := λ _ _ x =>
  have : p x → q x := ‹∀ x, p x → q x› x
  have : p x := ‹∀ x, p x› x
  show q x from ‹p x → q x› ‹p x›

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := λ axpxaxqx x =>
  match axpxaxqx with
  | Or.inl axpx => Or.inl (axpx x)
  | Or.inr axqx => Or.inr (axqx x)

-- The converse of the last example is not derivable because even if
-- (p x ∨ q x) is true for every x, it could be that p x is true for some x's
-- and q x is true for others. We can't commit to either
-- (∀ x, p x) or (∀ x, q x).

end ex_1

namespace ex_2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := λ a =>
  have fwd : (∀ x : α, r) → r := λ f => f a
  have rev : r → (∀ x : α, r) := λ hr x => hr
  show (∀ x : α, r) ↔ r from ⟨fwd, rev⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  have fwd : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r := λ axpxr =>
    match (Classical.em r) with
    | Or.inl (hr : r) =>
      Or.inr hr
    | Or.inr (hnr : ¬ r) =>
      show (∀ x, p x) ∨ r from Or.inl λ x =>
        show p x from match (axpxr x : p x ∨ r) with
        | Or.inl px => px
        | Or.inr hr => absurd hr hnr
  have rev : (∀ x, p x) ∨ r → (∀ x, p x ∨ r) := λ axpxr x =>
    match axpxr with
    | Or.inl axpx => Or.inl (axpx x)
    | Or.inr r => Or.inr r
  show (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r from ⟨fwd, rev⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  have fwd : (∀ x, r → p x) → (r → ∀ x, p x) := λ haxrpx hr x =>
    show p x from haxrpx x hr
  have rev : (r → ∀ x, p x) → (∀ x, r → p x) := λ hraxpx x hr =>
    show p x from hraxpx hr x
  show (∀ x, r → p x) ↔ (r → ∀ x, p x) from ⟨fwd, rev⟩

end ex_2

namespace ex_3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

-- Copied from Chapter 3's exercises
theorem p_iff_np_false : ¬(p ↔ ¬p) := λ p_iff_np =>
  have hpnp : p → ¬p := p_iff_np.mp
  have hnpp : ¬p → p := p_iff_np.mpr
  have hnp : ¬p := λ hp => hpnp hp hp
  have hnnp : ¬¬p := λ hnp => hnp (hnpp hnp)
  show False from hnnp hnp

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h_barber : shaves barber barber ↔ ¬ shaves barber barber := h barber
  show False from p_iff_np_false h_barber

end ex_3

namespace ex_4

def even (n : Nat) : Prop := ∃ m, n = 2 * m

def prime (n : Nat) : Prop := n > 1 ∧ ¬ ∃ m₁ m₂, m₁ < n ∧ m₂ < n ∧ m₁ * m₂ = n 

def infinitely_many (P : Nat → Prop) : Prop := ∀ n : Nat, ∃ m, m > n ∧ P m

def infinitely_many_primes : Prop := infinitely_many prime

def Fermat_number (n : Nat) : Prop := ∃ m : Nat, n = 2 ^ (2 ^ m) + 1

def Fermat_prime (n : Nat) : Prop := Fermat_number n ∧ prime n

def infinitely_many_Fermat_primes : Prop := infinitely_many Fermat_prime

def goldbach_conjecture : Prop :=
  ∀ n, n > 2 → even n → ∃ p₁ p₂, prime p₁ ∧ prime p₂ ∧ n = p₁ + p₂

def Goldbach's_weak_conjecture : Prop :=
  ∀ n, n > 5 → ¬ even n →
  ∃ p₁ p₂ p₃, prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ n = p₁ + p₂ + p₃

def Fermat's_last_theorem : Prop :=
  ∀ n, n > 2 → ¬ ∃ a b c : Nat, a ^ n + b ^ n = c ^ n

end ex_4

namespace ex_5

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := λ ⟨x, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) := λ hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  have fwd : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r := λ ⟨x, px, hr⟩ =>
    show (∃ x, p x) ∧ r from ⟨⟨x, px⟩, hr⟩
  have rev : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) := λ ⟨⟨x, px⟩, hr⟩ =>
    show ∃ x, p x ∧ r from ⟨x, px, hr⟩
  show (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r from ⟨fwd, rev⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  have fwd : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) := λ ⟨x, pxqx⟩ =>
    match pxqx with
    | Or.inl px => Or.inl ⟨x, px⟩
    | Or.inr qx => Or.inr ⟨x, qx⟩
  have rev : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) := λ _ =>
    match ‹(∃ x, p x) ∨ (∃ x, q x)› with
    | Or.inl ⟨x, px⟩ => ⟨x, Or.inl px⟩
    | Or.inr ⟨x, qx⟩ => ⟨x, Or.inr qx⟩
  show (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) from ⟨fwd, rev⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  have fwd : (∀ x, p x) → ¬ (∃ x, ¬ p x) := λ axpx ⟨x, npx⟩ =>
    show False from npx (axpx x)
  have rev : ¬ (∃ x, ¬ p x) → (∀ x, p x) := λ (_ : ¬ ∃ x, ¬ p x) x =>
    Classical.byContradiction λ (_ : ¬ p x) =>
      have : ∃ x, ¬ p x := ⟨x, ‹¬ p x›⟩
      show False from ‹¬ (∃ x, ¬ p x)› ‹∃ x, ¬ p x›
  show (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) from ⟨fwd, rev⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  have fwd : (∃ x, p x) → ¬ (∀ x, ¬ p x) := λ ⟨x, px⟩ axnpx =>
    show False from axnpx x px
  have rev : ¬ (∀ x, ¬ p x) → (∃ x, p x) := λ _ : ¬ ∀ x, ¬ p x =>
    Classical.byContradiction λ _ : ¬ ∃ x, p x =>
      have : ∀ x, ¬ p x := λ x px =>
        have : ∃ x, p x := ⟨x, px⟩
        show False from ‹¬ ∃ x, p x› ‹∃ x, p x›
      show False from ‹¬ ∀ x, ¬ p x› ‹∀ x, ¬ p x›
  show (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) from ⟨fwd, rev⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  have fwd : (¬ ∃ x, p x) → (∀ x, ¬ p x) := λ (_ : ¬ ∃ x, p x) x px =>
    have : ∃ x, p x := ⟨x, px⟩
    show False from ‹¬ ∃ x, p x› ‹∃ x, p x›
  have rev : (∀ x, ¬ p x) → (¬ ∃ x, p x) := λ (_ : ∀ x, ¬ p x) ⟨x, px⟩ =>
    have : ¬ p x := ‹∀ x, ¬ p x› x
    show False from ‹¬ p x› ‹p x›
  show (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) from ⟨fwd, rev⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  have fwd : (¬ ∀ x, p x) → (∃ x, ¬ p x) := λ (_ : ¬ ∀ x, p x) =>
    Classical.byContradiction λ (_ : ¬ ∃ x, ¬ p x) =>
      have : ∀ x, p x := λ x =>
        Classical.byContradiction λ (_ : ¬ p x) =>
          have : ∃ x, ¬ p x := ⟨x, ‹¬ p x›⟩
          show False from ‹¬ (∃ x, ¬ p x)› ‹∃ x, ¬ p x›
      show False from ‹¬ ∀ x, p x› ‹∀ x, p x›
  have rev : (∃ x, ¬ p x) → (¬ ∀ x, p x) := λ ⟨x, npx⟩ (_ : ∀ x, p x) =>
    have : p x := ‹∀ x, p x› x
    show False from ‹¬ p x› ‹p x›
  show (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) from ⟨fwd, rev⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  have fwd : (∀ x, p x → r) → (∃ x, p x) → r := λ (_ : ∀ x, p x → r) ⟨x, px⟩ =>
    show r from ‹∀ x, p x → r› x px
  have rev : ((∃ x, p x) → r) → (∀ x, p x → r) := λ (_ : (∃ x, p x) → r) x px =>
    show r from ‹(∃ x, p x) → r› ⟨x, px⟩
  show (∀ x, p x → r) ↔ (∃ x, p x) → r from ⟨fwd, rev⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  have fwd : (∃ x, p x → r) → (∀ x, p x) → r :=
    λ ⟨x, (_ : p x → r)⟩ (_ : ∀ x, p x) =>
      have : p x := ‹∀ x, p x› x
      show r from ‹p x → r› ‹p x›
  have rev : ((∀ x, p x) → r) → (∃ x, p x → r) :=
    λ (_ : (∀ x, p x) → r) =>
      show ∃ x, p x → r from Classical.byContradiction λ (_ : ¬∃ x, p x → r) =>
        have : ∀ x, p x := Classical.byContradiction λ (_ : ¬∀ x, p x) =>
          have : ∀ x, p x := λ x =>
            show p x from Classical.byContradiction λ (_ : ¬(p x)) =>
              have : ∃ x, p x → r := ⟨x, λ _ => absurd ‹p x› ‹¬(p x)›⟩
              show False from ‹¬∃ x, p x → r› ‹∃ x, p x → r›
          show False from ‹¬∀ x, p x› ‹∀ x, p x›
        have : r := ‹(∀ x, p x) → r› ‹∀ x, p x›
        have : ∃ x, p x → r := ⟨a, λ _ => ‹r›⟩
        show False from ‹¬∃ x, p x → r› ‹∃ x, p x → r›
  show (∃ x, p x → r) ↔ (∀ x, p x) → r from ⟨fwd, rev⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  have fwd : (∃ x, r → p x) → (r → ∃ x, p x) :=
    λ ⟨x, (_ : r → p x)⟩ (_ : r) =>
      have : p x := ‹r → p x› ‹r›
      show ∃ x, p x from ⟨x, ‹p x›⟩
  have rev : (r → ∃ x, p x) → (∃ x, r → p x) :=
    λ (_ : r → ∃ x, p x) =>
      show ∃ x, r → p x from Classical.byContradiction λ (_ : ¬∃ x, r → p x) =>
        have : r := Classical.byContradiction λ (_ : ¬r) =>
          have : ∃ x, r → p x := ⟨a, λ _ => absurd ‹r› ‹¬r›⟩
          show False from ‹¬∃ x, r → p x› ‹∃ x, r → p x›
        let ⟨x, (_ : p x)⟩ := ‹r → ∃ x, p x› ‹r›
        have : ∃ x, r → p x := ⟨x, λ _ => ‹p x›⟩
        show False from ‹¬∃ x, r → p x› ‹∃ x, r → p x›
  show (∃ x, r → p x) ↔ (r → ∃ x, p x) from ⟨fwd, rev⟩

end ex_5
