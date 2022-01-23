/-= Chapter 5: Tactics =-/

/- Entering tactic mode -/
namespace enter_tactic_mode

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

#print test₂

theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

theorem test₄ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left =>
    exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

theorem test₅ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left =>
    exact hp

theorem test₆ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp

end enter_tactic_mode

/- Basic tactics -/
namespace basic_tactics

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    apply h.right.elim
    · intro hq
      apply Or.inl
      apply And.intro
      · exact h.left
      · exact hq
    · intro hr
      apply Or.inr
      apply And.intro
      · exact h.left
      · exact hr
  · intro h
    apply h.elim
    · intro hpq
      apply And.intro
      · exact hpq.left
      · apply Or.inl
        exact hpq.right
    · intro hpr
      apply And.intro
      · exact hpr.left
      · apply Or.inr
        exact hpr.right

example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
    | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
    | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption
  apply Eq.trans
  assumption
  assumption

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h₁ _ h₂
  apply Eq.trans 
  apply Eq.symm
  exact h₂
  exact h₁

example (y : Nat) : (λ x : Nat => 0) y = 0 := by rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example (x : Nat) : x = x := by
  revert x
  -- goal is ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl

/-
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit
-/

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]

end basic_tactics

/- More tactics -/
namespace more_tactics

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  · apply Or.inr
    assumption

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      · apply Or.inl; constructor <;> assumption
      · apply Or.inr; constructor <;> assumption
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr

example (p q : Nat → Prop) : (∃ x, p x) → (∃ x, p x ∨ q x) := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x) → (∃ x, p x ∨ q x) := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
      constructor <;> assumption

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  · apply Sum.inr; assumption
  . apply Sum.inl; assumption

example
    (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (Nat.succ n)) (m : Nat) : P m := by
  cases m with
  | zero => exact h₀
  | succ m' => exact h₁ m'

example (p q : Prop) : p ∧ ¬p → q := by
  intro h
  cases h
  contradiction

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  · intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  · intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption

end more_tactics

/- Structuring tactic proofs -/
namespace structuring_tactic_proofs

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

-- My own attempt at making this look nice
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro
    | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
    | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩
  · intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

-- Updating my clean version above with show
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · show p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
    intro
    | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
    | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩
  · show (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)
    intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this

example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
  rfl

-- My own version, more explicitly showing the evaluation
example : ∃ x, x + 2 = 8 := by
  let a := 3 * 2
  exists a
  show 3 * 2 + 2 = 8
  show 8 = 8
  rfl

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }

end structuring_tactic_proofs

/- Tactic combinators -/
namespace tactic_combinators

example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

example
    (p q r : Prop) (hp : p) (hq : q) (hr : r)
    : p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example
    (p q r : Prop) (hp : p) (hq : q) (hr : r)
    : p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

end tactic_combinators

/- Rewriting -/
namespace rewriting

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0

example
    (x y : Nat) (p : Nat → Prop) (q : Prop)
    (h : q → x = y) (h' : p y) (hq : q)
    : p x := by
  rw [h hq]; assumption

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ←Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

end rewriting

/- Using the simplifier -/
namespace using_the_simplifier

example
    (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
    : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example
    (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
    : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

open List

example
    (xs : List Nat) : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example
    (xs ys : List α) : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]

example
    (x y z : Nat) (p : Nat → Prop) (h : p ((x + 0) * (0 + y * 1 + z * 0)))
    : p (x * y) := by
  simp at h; assumption

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example
    (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x))
    : p (x * w * z + y * x) := by
  simp at *; assumption

example
    (x y z : Nat) (p : Nat → Prop) (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
    : p (y + 0 + x) ∧ p (z * x) := by
  simp at *; constructor <;> assumption

example
    (w x y z : Nat) (p : Nat → Prop)
    : x * y + z * w * x = x * w * z + y * x := by
  simp

example
    (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x))
    : p (x * w * z + y * x) := by
  simp; simp at h; assumption

def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [←h', f]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

example
    (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x) : w = z + y + u := by
  simp [*]

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

example
    (u w x x' y y' z : Nat) (p : Nat → Prop) (h₁ : x + 0 = x') (h₂ : y + 0 = y')
    : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

def mk_symm (xs : List α) :=
  xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α) : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example
    (xs ys : List Nat)
    : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example
    (xs ys : List Nat) (p : List Nat → Prop) (h : p (xs ++ mk_symm ys).reverse)
    : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

namespace simp_annotation

@[simp]
theorem reverse_mk_symm (xs : List α) : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

-- Alternatively:
-- attribute [simp] reverse_mk_symm

example
    (xs ys : List Nat)
    : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

-- Alternatively:
-- attribute [simp] reverse_mk_symm

example
    (xs ys : List Nat) (p : List Nat → Prop) (h : p (xs ++ mk_symm ys).reverse)
    : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example
    (xs ys : List Nat) (p : List Nat → Prop) (h : p (xs ++ mk_symm ys).reverse)
    : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example
    (xs ys : List Nat) (p : List Nat → Prop) (h : p (xs ++ mk_symm ys).reverse)
    : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption

end simp_annotation

namespace local_simp_annotation

theorem reverse_mk_symm (xs : List α) : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section local_simp
attribute [local simp] reverse_mk_symm

example
    (xs ys : List Nat)
    : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp
end local_simp

example
    (xs ys : List Nat) (p : List Nat → Prop) (h : p (xs ++ mk_symm ys).reverse)
    : p (mk_symm ys ++ xs.reverse) := by
  -- This simp shouldn't work but I think the other defs in the file apply
  simp at h; assumption

end local_simp_annotation

end using_the_simplifier

/- Extensible tactics -/
namespace extensible_tactics

-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter tries all
-- possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv

end extensible_tactics

/- Exercises -/
namespace ex_1

namespace ch3_exs

variable (p q r s : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · show p ∧ q → q ∧ p
    intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · show q ∧ p → p ∧ q
    intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

example : p ∧ q ↔ q ∧ p := by
  constructor <;> intros <;> simp [*]

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  · show p ∨ q → q ∨ p
    intro
    | Or.inl hp => exact Or.inr hp
    | Or.inr hq => exact Or.inl hq
  · show q ∨ p → p ∨ q
    intro
    | Or.inl hq => exact Or.inr hq
    | Or.inr hp => exact Or.inl hp

example : p ∨ q ↔ q ∨ p := by
  constructor <;> intros h <;> cases h <;> simp [*]

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  · show (p ∧ q) ∧ r → p ∧ (q ∧ r)
    intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, ⟨hq, hr⟩⟩
  · show p ∧ (q ∧ r) → (p ∧ q) ∧ r
    intro ⟨hp, ⟨hq, hr⟩⟩
    exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor <;> intros <;> simp [*]

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  · show (p ∨ q) ∨ r → p ∨ (q ∨ r)
    intro
    | Or.inl (Or.inl hp) => exact Or.inl hp
    | Or.inl (Or.inr hq) => exact Or.inr (Or.inl hq)
    | Or.inr hr => exact Or.inr (Or.inr hr)
  · show p ∨ (q ∨ r) → (p ∨ q) ∨ r
    intro
    | Or.inl hp => exact Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => exact Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => exact Or.inr hr
  
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor <;> intro
  repeat (first | rename_i h; cases h | simp [*])

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · show p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
    intro
    | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
    | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩
  · show (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)
    intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor <;> intro h; simp [*]; cases h <;> simp [*]

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · show p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    intro
    | Or.inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  · show (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    intro
    | ⟨Or.inl hp, _⟩ => exact Or.inl hp
    | ⟨_, Or.inl hp⟩ => exact Or.inl hp
    | ⟨Or.inr hq, Or.inr hr⟩ => exact Or.inr ⟨hq, hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor <;> intro h <;> cases h <;> simp [*]
  rename_i hpq hpr; cases hpq <;> simp [*]

-- other properties
example : (p → q → r) ↔ (p ∧ q → r) := by
  apply Iff.intro
  · show (p → q → r) → (p ∧ q → r)
    intro f
    intro ⟨hp, hq⟩
    show r
    exact f hp hq
  · show (p ∧ q → r) → (p → q → r)
    intros f hp hq
    show r
    exact f ⟨hp, hq⟩

example : (p → q → r) ↔ (p ∧ q → r) := by
  constructor <;> intros <;> simp [*]

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  · show ((p ∨ q) → r) → (p → r) ∧ (q → r)
    intro (_ : p ∨ q → r)
    apply And.intro
    · show p → r
      intro (_ : p)
      exact ‹p ∨ q → r› (Or.inl ‹p›)
    · show q → r
      intro (_ : q)
      exact ‹p ∨ q → r› (Or.inr ‹q›)
  · show (p → r) ∧ (q → r) → ((p ∨ q) → r)
    intro ⟨(_ : p → r), (_ : q → r)⟩
    intro
    | Or.inl (_ : p) => exact ‹p → r› ‹p›
    | Or.inr (_ : q) => exact ‹q → r› ‹q›

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor <;> intros
  · constructor <;> intros <;> simp [*]
  · rename_i h; cases h <;> simp [*]

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · show ¬(p ∨ q) → ¬p ∧ ¬q
    intro (_ : ¬(p ∨ q))
    apply And.intro
    · show ¬p
      intro (_ : p)
      show False
      exact ‹¬(p ∨ q)› (Or.inl ‹p›)
    · show ¬q
      intro (_ : q)
      show False
      exact ‹¬(p ∨ q)› (Or.inr ‹q›)
  · show ¬p ∧ ¬q → ¬(p ∨ q)
    intro ⟨(_ : ¬p), (_ : ¬q)⟩
    intro
    | Or.inl (_ : p) => exact ‹¬p› ‹p›
    | Or.inr (_ : q) => exact ‹¬q› ‹q›

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor <;> intros h
  · constructor <;> intro <;> simp [*] at *
  · intro hpq; cases hpq <;> simp [*] at *

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl (_ : ¬p) =>
    intro ⟨(_ : p), _⟩; contradiction
  | Or.inr (_ : ¬q) =>
    intro ⟨_, (_ : q)⟩; contradiction

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h; cases h <;> simp [*]

example : ¬(p ∧ ¬p) := by
  intro ⟨(_ : p), (_ : ¬p)⟩
  show False
  exact ‹¬ p› ‹p›

example : ¬(p ∧ ¬p) := by
  intro ⟨_, _⟩; contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨(_ : p), (_ : ¬q)⟩
  intro (_ : p → q)
  show False
  exact ‹¬q› (‹p → q› ‹p›)

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨_, _⟩; intro; simp [*] at *

example : ¬p → p → q := by
  intro (_ : ¬p) (_ : p)
  show q
  exact False.elim (‹¬p› ‹p›)

example : ¬p → p → q := by
  intros; contradiction

example : (¬p ∨ q) → (p → q) := by
  intro (_ : ¬p ∨ q) (_ : p)
  show q
  match ‹¬p ∨ q› with
  | Or.inl (_ : ¬p) => exact False.elim (‹¬p› ‹p›)
  | Or.inr (_ : q) => exact ‹q›

example : (¬p ∨ q) → (p → q) := by
  intros; simp [*] at *; assumption

example : p ∨ False ↔ p := by
  apply Iff.intro
  · show p ∨ False → p
    intro
    | Or.inl (_ : p) => exact ‹p›
  · show p → p ∨ False
    intro (_ : p)
    exact Or.inl ‹p›

example : p ∨ False ↔ p := by
  simp [*] at *

example : p ∧ False ↔ False := by
  apply Iff.intro
  · show p ∧ False → False
    intro ⟨_, (_ : False)⟩
    exact ‹False›
  · show False → p ∧ False
    intro (_ : False)
    exact False.elim ‹False›

example : p ∧ False ↔ False := by
  apply Iff.intro
  · show p ∧ False → False
    intro ⟨_, (_ : False)⟩
    cases ‹False›
  · show False → p ∧ False
    intro (_ : False)
    cases ‹False›

example : p ∧ False ↔ False := by
  simp

example : (p → q) → (¬q → ¬p) := by
  intro (_ : p → q) (_ : ¬q) (_ : p)
  show False
  exact ‹¬q› (‹p → q› ‹p›)

example : (p → q) → (¬q → ¬p) := by
  repeat intro; simp [*] at *

namespace using_classical
open Classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro (_ : p → r ∨ s)
  show (p → r) ∨ (p → s)
  match em r with
  | Or.inl (_ : r) =>
    apply Or.inl
    show p → r
    exact λ _ => ‹r›
  | Or.inr (_ : ¬r) =>
    apply Or.inr
    show p → s
    intro (_ : p)
    match ‹p → r ∨ s› ‹p› with
    | Or.inl (_ : r) =>
      show s
      exact False.elim (‹¬r› ‹r›)
    | Or.inr (_ : s) =>
      show s
      exact ‹s›

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro; cases em r
  · simp [*]
  · apply Or.inr; intro; cases ‹p → r ∨ s› ‹p›
    · contradiction
    · assumption

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro (_ : ¬(p ∧ q))
  show ¬p ∨ ¬q
  match em p with
  | Or.inr (_ : ¬p) =>
    apply Or.inl
    show ¬p
    exact ‹¬p›
  | Or.inl (_ : p) =>
    apply Or.inr
    show ¬q
    intro (_ : q)
    exact ‹¬(p ∧ q)› ⟨‹p›, ‹q›⟩

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro; cases em p
  · apply Or.inr; intro; simp [*] at *
  · simp [*]

example : ¬(p → q) → p ∧ ¬q := by
  intro (_ : ¬(p → q))
  apply And.intro
  · show p
    apply byContradiction
    intro (_ : ¬p)
    show False
    have : p → q := by
      intro (_ : p)
      exact False.elim (‹¬p› ‹p›)
    exact ‹¬(p → q)› ‹p → q›
  · show ¬q
    intro (_ : q)
    show False
    have : p → q := λ _ => ‹q›
    exact ‹¬(p → q)› ‹p → q›

example : ¬(p → q) → p ∧ ¬q := by
  intro; constructor
  · apply byContradiction; intro; simp [*] at *
  · intro; simp [*] at *

example : (p → q) → ¬p ∨ q := by
  intro (_ : p → q)
  show ¬p ∨ q
  match em p with
  | Or.inl (_ : p) => exact Or.inr (‹p → q› ‹p›)
  | Or.inr (_ : ¬p) => exact Or.inl ‹¬p›

example : (p → q) → ¬p ∨ q := by
  intro (_ : p → q)
  show ¬p ∨ q
  match em p with
  | Or.inl (_ : p) =>
    apply Or.inr
    show q
    exact ‹p → q› ‹p›
  | Or.inr (_ : ¬p) =>
    apply Or.inl
    show ¬p
    exact ‹¬p›

example : (p → q) → ¬p ∨ q := by
  intro; cases em p <;> simp [*]

example : (¬q → ¬p) → (p → q) := by
  intro (_: ¬q → ¬p) (_ : p)
  show q
  apply byContradiction
  intro (_ : ¬q)
  show False
  exact ‹¬q → ¬p› ‹¬q› ‹p›

example : (¬q → ¬p) → (p → q) := by
  intros; apply byContradiction; intro; simp [*] at *

example : p ∨ ¬p := by
  exact em p

example : ((p → q) → p) → p := by
  intro (_ : (p → q) → p)
  show p
  apply byContradiction
  intro (_ : ¬p)
  show False
  apply ‹¬p›
  apply ‹(p → q) → p›
  show p → q
  intro (_ : p)
  exact False.elim (‹¬p› ‹p›)

example : ((p → q) → p) → p := by
  intro; apply byContradiction; intro; simp [*] at *

end using_classical

example : ¬(p ↔ ¬p) := by
  intro ⟨(_ : p → ¬p), (_ : ¬p → p)⟩
  have : ¬p := λ (_ : p) => ‹p → ¬p› ‹p› ‹p›
  show False
  exact ‹¬p› (‹¬p → p› ‹¬p›)

example : ¬(p ↔ ¬p) := by
  intro ⟨_, _⟩
  have : ¬p := by intro; simp [*] at *
  simp [*] at *

end ch3_exs

namespace ch4_ex1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  · show (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x)
    intro (_ : ∀ x, p x ∧ q x)
    apply And.intro
    · show ∀ x, p x
      intro x
      exact (‹∀ x, p x ∧ q x› x).left
    · show ∀ x, q x
      intro x
      exact (‹∀ x, p x ∧ q x› x).right
  · show (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x)
    intro ⟨(_ : ∀ x, p x), (_ : ∀ x, q x)⟩ x
    apply And.intro
    · show p x
      exact ‹∀ x, p x› x
    · show q x
      exact ‹∀ x, q x› x

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor <;> intros <;> simp [*]

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro (_ : ∀ x, p x → q x) (_ : ∀ x, p x) x
  show q x
  have : p x := ‹∀ x, p x› x
  have : q x := ‹∀ x, p x → q x› x ‹p x›
  exact this

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intros; simp [*]

example : (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x) := by
  intro (_ : (∀ x, p x) ∨ (∀ x, q x)) x
  show p x ∨ q x
  match ‹(∀ x, p x) ∨ (∀ x, q x)› with
  | Or.inl (_ : ∀ x, p x) =>
    apply Or.inl
    show p x
    exact ‹∀ x, p x› x
  | Or.inr (_ : ∀ x, q x) =>
    apply Or.inr
    show q x
    exact ‹∀ x, q x› x

example : (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x) := by
  intro h x; cases h <;> simp [*] at *

end ch4_ex1

namespace ch4_ex2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro (a : α)
  apply Iff.intro
  · show (∀ x : α, r) → r
    intro (_ : ∀ x : α, r)
    exact ‹∀ x : α, r› a
  · show r → (∀ x : α, r)
    intro (_ : r) x
    exact ‹r›

example : α → ((∀ x : α, r) ↔ r) := by
  intro a; constructor
  · intro h; exact h a
  · intros; simp [*]

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  · intro (_ : ∀ x, p x ∨ r)
    show (∀ x, p x) ∨ r
    match Classical.em r with
    | Or.inl (_ : r) =>
      apply Or.inr
      show r
      exact ‹r›
    | Or.inr (_ : ¬r) =>
      apply Or.inl
      intro x
      show p x
      match ‹∀ x, p x ∨ r› x with
      | Or.inl (_ : p x) => exact ‹p x›
      | Or.inr (_ : r) => exact False.elim (‹¬r› ‹r›)
  · intro (_ : (∀ x, p x) ∨ r) x
    show p x ∨ r
    match ‹(∀ x, p x) ∨ r› with
    | Or.inl (_ : ∀ x, p x) =>
      apply Or.inl
      show p x
      exact ‹∀ x, p x› x
    | Or.inr (_ : r) =>
      apply Or.inr
      show r
      exact ‹r›

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor <;> intro h
  · cases Classical.em r <;> intros
    · simp [*]
    · apply Or.inl; intro x; cases h x <;> simp [*] at *
  · intros; cases h <;> simp [*]

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  · intro (_ : ∀ x, r → p x) (_ : r) x
    show p x
    exact ‹∀ x, r → p x› x ‹r›
  · intro (_ : r → ∀ x, p x) x (_ : r)
    show p x
    exact ‹r → ∀ x, p x› ‹r› x

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor <;> intros <;> simp [*]

end ch4_ex2

namespace ch4_ex3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  let bsh : Prop := shaves barber barber -- "barber shaves himself"
  have ⟨(_ : bsh → ¬bsh), (_ : ¬bsh → bsh)⟩ := h barber
  have : ¬bsh := λ (_ : bsh) => ‹bsh → ¬bsh› ‹bsh› ‹bsh›
  show False
  exact ‹¬bsh› (‹¬bsh → bsh› ‹¬bsh›)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  let bsh : Prop := shaves barber barber -- "barber shaves himself"
  have ⟨(_ : bsh → ¬bsh), (_ : ¬bsh → bsh)⟩ := h barber
  show False
  have : ¬bsh := by
    intro (_ : bsh)
    show False
    have : ¬bsh := ‹bsh → ¬bsh› ‹bsh›
    contradiction
  have : bsh := ‹¬bsh → bsh› ‹¬bsh›
  contradiction

end ch4_ex3

namespace ch4_ex5

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro ⟨x, (_ : r)⟩
  exact ‹r›

example : (∃ x : α, r) → r := by
  intro h; cases h; assumption

example (a : α) : r → (∃ x : α, r) := by
  intro (_ : r)
  exists a
  exact ‹r›

example (a : α) : r → (∃ x : α, r) := by
  intro; constructor <;> assumption

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  · intro ⟨x, ⟨(_ : p x), (_ : r)⟩⟩
    show (∃ x, p x) ∧ r
    exact ⟨⟨x, ‹p x›⟩, ‹r›⟩
  · intro ⟨⟨x, (_ : p x)⟩, (_ : r)⟩
    show ∃ x, p x ∧ r
    exact ⟨x, ⟨‹p x›, ‹r›⟩⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  · intro ⟨_, ⟨_, _⟩⟩; (constructor <;> try constructor); repeat assumption
  · intro ⟨⟨_, _⟩, _⟩; repeat constructor; repeat assumption

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  · intro ⟨x, (_ : p x ∨ q x)⟩
    show (∃ x, p x) ∨ (∃ x, q x)
    match ‹p x ∨ q x› with
    | Or.inl (_ : p x) => exact Or.inl ⟨x, ‹p x›⟩
    | Or.inr (_ : q x) => exact Or.inr ⟨x, ‹q x›⟩
  · intro (_ : (∃ x, p x) ∨ (∃ x, q x))
    show ∃ x, p x ∨ q x
    match ‹(∃ x, p x) ∨ (∃ x, q x)› with
    | Or.inl ⟨x, (_ : p x)⟩ => exact ⟨x, Or.inl ‹p x›⟩
    | Or.inr ⟨x, (_ : q x)⟩ => exact ⟨x, Or.inr ‹q x›⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  · intro ⟨x, (_ : p x ∨ q x)⟩
    show (∃ x, p x) ∨ (∃ x, q x)
    match ‹p x ∨ q x› with
    | Or.inl (_ : p x) => apply Or.inl; exists x; exact ‹p x›
    | Or.inr (_ : q x) => apply Or.inr; exists x; exact ‹q x›
  · intro (_ : (∃ x, p x) ∨ (∃ x, q x))
    show ∃ x, p x ∨ q x
    match ‹(∃ x, p x) ∨ (∃ x, q x)› with
    | Or.inl ⟨x, (_ : p x)⟩ => exists x; apply Or.inl; exact ‹p x›
    | Or.inr ⟨x, (_ : q x)⟩ => exists x; apply Or.inr; exact ‹q x›

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro h ; cases h; rename_i h; cases h
    · apply Or.inl; constructor; assumption
    · apply Or.inr; constructor; assumption
  · intro h; cases h <;> rename_i h <;> cases h
    · constructor; apply Or.inl; assumption
    · constructor; apply Or.inr; assumption

-- Not bothering with short proofs after this point
-- They aren't so easy to do with existentials

example : (∀ x, p x) ↔ ¬∃ x, ¬ p x := by
  apply Iff.intro
  · intro (_ : ∀ x, p x) ⟨x, (_ : ¬ p x)⟩
    show False
    exact ‹¬ p x› (‹∀ x, p x› x)
  · intro (_ : ¬∃ x, ¬ p x) x
    show p x
    apply Classical.byContradiction
    intro (_ : ¬ p x)
    show False
    exact ‹¬∃ x, ¬ p x› ⟨x, ‹¬ p x›⟩

example : (∃ x, p x) ↔ ¬∀ x, ¬ p x := by
  apply Iff.intro
  · intro ⟨x, (_ : p x)⟩ (_ : ∀ x, ¬ p x)
    show False
    exact ‹∀ x, ¬ p x› x ‹p x›
  · intro (_ : ¬∀ x, ¬ p x)
    show ∃ x, p x
    apply Classical.byContradiction
    intro (_ : ¬∃ x, p x)
    show False
    apply ‹¬∀ x, ¬ p x›
    intro x (_ : p x)
    show False
    apply ‹¬∃ x, p x›
    exact ⟨x, ‹p x›⟩

example : (∃ x, p x) ↔ ¬∀ x, ¬ p x := by
  apply Iff.intro
  · intro ⟨x, (_ : p x)⟩ (_ : ∀ x, ¬ p x)
    show False
    exact ‹∀ x, ¬ p x› x ‹p x›
  · intro (_ : ¬∀ x, ¬ p x)
    show ∃ x, p x
    apply Classical.byContradiction
    intro (_ : ¬∃ x, p x)
    show False
    have : ∀ x, ¬ p x := by
      intro x (_ : p x) 
      show False
      exact ‹¬∃ x, p x› ⟨x, ‹p x›⟩
    exact ‹¬∀ x, ¬ p x› ‹∀ x, ¬ p x›

example : (¬∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro (_ : ¬∃ x, p x) x (_ : p x)
    show False
    apply ‹¬∃ x, p x›
    exact ⟨x, ‹p x›⟩
  · intro (_ : ∀ x, ¬ p x) ⟨x, (_ : p x)⟩
    show False
    apply ‹∀ x, ¬ p x› x
    exact ‹p x›

example : (¬∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  · intro (_ : ¬∀ x, p x)
    show ∃ x, ¬ p x
    apply Classical.byContradiction
    intro (_ : ¬∃ x, ¬ p x)
    show False
    apply ‹¬∀ x, p x›
    intro x
    show p x
    apply Classical.byContradiction
    intro (_ : ¬ p x)
    show False
    apply ‹¬∃ x, ¬ p x›
    exact ⟨x, ‹¬ p x›⟩
  · intro ⟨x, (_ : ¬ p x)⟩ (_ : ∀ x, p x)
    show False
    apply ‹¬ p x›
    exact ‹∀ x, p x› x

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  · intro (_ : ∀ x, p x → r) ⟨x, (_ : p x)⟩
    show r
    exact ‹∀ x, p x → r› x ‹p x›
  · intro (_ : (∃ x, p x) → r) x (_ : p x)
    show r
    exact ‹(∃ x, p x) → r› ⟨x, ‹p x›⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  · intro ⟨x, (_ : p x → r)⟩ (_ : ∀ x, p x)
    show r
    exact ‹p x → r› (‹∀ x, p x› x)
  · intro (_ : (∀ x, p x) → r)
    show ∃ x, p x → r
    apply Classical.byContradiction
    intro (_ : ¬∃ x, p x → r)
    show False
    have : r := by
      apply ‹(∀ x, p x) → r›
      intro x
      show p x
      apply Classical.byContradiction
      intro (_ : ¬ p x)
      show False
      apply ‹¬∃ x, p x → r›
      exists x
      intro (_ : p x)
      show r
      exact absurd ‹p x› ‹¬ p x›
    apply ‹¬∃ x, p x → r›
    exact ⟨a, λ (_ : p a) => ‹r›⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  · intro ⟨x, (_ : r → p x)⟩ (_ : r)
    show ∃ x, p x
    exact ⟨x, ‹r → p x› ‹r›⟩
  · intro (_ : r → ∃ x, p x)
    show ∃ x, r → p x
    apply Classical.byContradiction
    intro (_ : ¬∃ x, r → p x)
    have : r := by
      apply Classical.byContradiction
      intro (_ : ¬r)
      show False
      apply ‹¬∃ x, r → p x›
      exists a
      intro (_ : r)
      show p a
      exact absurd ‹r› ‹¬r›
    have ⟨x, (_ : p x)⟩ := ‹r → ∃ x, p x› ‹r›
    show False
    apply ‹¬∃ x, r → p x›
    exists x
    intro (_ : r)
    exact ‹p x›

end ch4_ex5

end ex_1

namespace ex_2

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp [*]

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | assumption | apply Or.inl; assumption | apply Or.inr | constructor)

end ex_2
