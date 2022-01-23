/-= Chapter 7: Inductive types =-/

/- Enumerated types -/
namespace enumerated_types

inductive Weekday where
| sunday : Weekday
| monday : Weekday
| tuesday : Weekday
| wednesday : Weekday
| thursday : Weekday
| friday : Weekday
| saturday : Weekday

#check Weekday.sunday
#check Weekday.monday

section
open Weekday

#check sunday
#check monday
end

namespace omit_type

inductive Weekday where
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

end omit_type

section
open Weekday
def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday => 1
  | monday => 2
  | tuesday => 3
  | wednesday => 4
  | thursday => 5
  | friday => 6
  | saturday => 7
end

#eval numberOfDay Weekday.sunday
#eval numberOfDay Weekday.monday
#eval numberOfDay Weekday.tuesday

section pretty_print

set_option pp.all true
#print numberOfDay
#print numberOfDay.match_1
#print Weekday.casesOn
#check @Weekday.rec
#print Weekday.rec

end pretty_print

namespace repr

inductive Weekday where
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
deriving Repr

open Weekday

#eval tuesday

end repr

namespace add_to_namespace

inductive Weekday where
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
deriving Repr

namespace Weekday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday => monday
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday => saturday
  | monday => sunday
  | tuesday => monday
  | wednesday => tuesday
  | thursday => wednesday
  | friday => thursday
  | saturday => friday

#eval next (next tuesday)
#eval next (previous tuesday)

example : next (previous tuesday) = tuesday :=
  rfl

def next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday => rfl
  | monday => rfl
  | tuesday => rfl
  | wednesday => rfl
  | thursday => rfl
  | friday => rfl
  | saturday => rfl

namespace tactic_version

def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end tactic_version

end Weekday

end add_to_namespace

namespace bool

inductive Bool where
| false
| true

namespace Bool

def and (p q : Bool) : Bool :=
  match p with
  | true => q
  | false => false

def or (p q : Bool) : Bool :=
  match p with
  | true => true
  | false => q

def not (p : Bool) : Bool :=
  match p with
  | true => false
  | false => true

example (p : Bool) : not (not p) = p := by
  match p with
  | true => rfl
  | false => rfl

example (p q : Bool) : and p q = and q p := by
  match p, q with
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

end Bool

end bool

end enumerated_types

/- Constructors with arguments -/
namespace constructors_with_arguments

namespace prod_and_sum

inductive Prod (α : Type u) (β : Type v)
| mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
| inl : α → Sum α β
| inr : β → Sum α β

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b

end prod_and_sum

#check Prod.casesOn

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := λ _ => Nat) p (λ b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := λ _ => Nat) s (λ n => 2 * n) (λ n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

namespace named_arguments

inductive Prod (α : Type u) (β : Type v)
| mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v)
| inl (a : α) : Sum α β
| inr (b : β) : Sum α β

end named_arguments

namespace structures

structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)

structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
#eval yellow

namespace fields

structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr

end fields

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

end structures

namespace more_std_examples

inductive Sigma {α : Type u} (β : α → Type v) where
| mk : (a : α) → β a → Sigma β

inductive Option (α : Type u) where
| none : Option α
| some : α → Option α

inductive Inhabited (α : Type u) where
| mk : α → Inhabited α

end more_std_examples

-- Exercises
-- develop a notion of composition of partial functions
def compose
    {α : Type u} {β : Type v} {γ : Type w}
    (f : β → Option γ) (g : α → Option β) (x : α) : Option γ :=
  match g x with
  | some (y : β) => f y
  | none => none

-- show that it behaves as expected
def partial_id {α : Type u} : α → Option α := some
def partial_none {α : Type u} : α → Option α := λ _ => none

example : compose partial_id partial_none 3 = none := rfl
example : compose partial_none partial_id 3 = none := rfl
example : compose partial_id partial_id 3 = some 3 := rfl

-- show that Bool and Nat are inhabited
example : Inhabited Bool := Inhabited.mk false
example : Inhabited Nat := Inhabited.mk 0

-- the product of two inhabited types is inhabited
theorem prod_inhabited
    {α : Type u} {β : Type v} (ia : Inhabited α) (ib : Inhabited β)
    : Inhabited (α × β) :=
  match ia, ib with
  | Inhabited.mk a, Inhabited.mk b => Inhabited.mk (a, b)

-- the type of functions to an inhabited type is inhabited
theorem fn_inhabited
    {α : Type u} {β : Type v} (ib : Inhabited β)
    : Inhabited (α → β) :=
  let (Inhabited.mk b) := ib
  Inhabited.mk (λ _ => b)

end constructors_with_arguments

/- Inductively defined propositions -/
namespace inductively_defined_propositions

inductive False : Prop where

inductive True : Prop where
| intro : True

inductive And (a b : Prop) : Prop where
| intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
| inl : a → Or a b
| inr : b → Or a b

inductive Exists {α : Type u} (q : α → Prop) : Prop where
| intro : ∀ (a : α), q a → Exists q

inductive Subtype {α : Type u} (p : α → Prop) where
| mk : (x : α) → p x → Subtype p

end inductively_defined_propositions

/- Defining the natural numbers -/
namespace defining_the_natural_numbers

namespace my_nat

inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr

#check @Nat.rec
#check @Nat.recOn

namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => Nat.succ (add m n)

#eval add (succ (succ zero)) (succ zero)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat

end my_nat

open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := λ x => 0 + x = x)
    n
    (show 0 + 0 = 0 from rfl)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + succ n = succ n from
      calc
        _ = 0 + succ n   := rfl
        _ = succ (0 + n) := rfl
        _ = succ n       := by rw [ih])

theorem zero_add_tactics (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := λ x => 0 + x = x)
    n
    rfl
    (λ n ih => by simp [add_succ, ih])

theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := by
  apply Nat.recOn (motive := λ k => (m + n) + k = m + (n + k)) k
  · show (m + n) + 0 = m + (n + 0)
    rfl
  · intro k (ih : (m + n) + k = m + (n + k))
    show (m + n) + succ k = m + (n + succ k)
    calc
      _ = (m + n) + succ k   := rfl
      _ = succ ((m + n) + k) := rfl
      _ = succ (m + (n + k)) := by rw [ih]
      _ = m + succ (n + k)   := rfl
      _ = m + (n + succ k)   := rfl

theorem add_assoc_short (m n k : Nat) : (m + n) + k = m + (n + k) := by
  apply Nat.recOn (motive := λ k => (m + n) + k = m + (n + k)) k
  · rfl
  · intro k ih
    simp [Nat.add_succ, ih]

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) := by
  apply Nat.recOn (motive := λ x => succ n + x = succ (n + x))
  · show succ n + 0 = succ (n + 0)
    rfl
  · intro m (ih : succ n + m = succ (n + m))
    show succ n + succ m = succ (n + succ m)
    calc
      _ = succ n + succ m     := rfl
      _ = succ (succ n + m)   := rfl
      _ = succ (succ (n + m)) := by rw [ih]
      _ = succ (n + succ m)   := rfl

theorem add_comm (m n : Nat) : m + n = n + m := by
  apply Nat.recOn (motive := λ x => m + x = x + m) n
  · show m + 0 = 0 + m
    rw [Nat.zero_add, Nat.add_zero]
  · intro n (ih : m + n = n + m)
    show m + succ n = succ n + m
    calc
      _ = m + succ n   := rfl
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := by rw [succ_add]

theorem succ_add_short (n m : Nat) : succ n + m = succ (n + m) := by
  apply Nat.recOn (motive := λ x => succ n + x = succ (n + x))
  · simp
  · intro m ih
    simp only [add_succ, ih]

theorem add_comm_short (m n : Nat) : m + n = n + m := by
  apply Nat.recOn (motive := λ x => m + x = x + m) n
  · simp
  · intro n ih
    simp only [add_succ, succ_add, ih]

end defining_the_natural_numbers

/- Other recursive data types -/
namespace other_recursive_data_types

inductive List (α : Type u) where
| nil : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := rfl

theorem cons_append
    (a : α) (as bs : List α) : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) : append as nil = as := by
  apply List.recOn (motive := λ xs => append xs nil = xs) as
  · show append nil nil = nil
    rfl
  · intro a as (ih : append as nil = as)
    show append (cons a as) nil = cons a as
    calc
      _ = append (cons a as) nil := rfl
      _ = cons a (append as nil) := rfl
      _ = cons a as              := by rw [ih]

theorem append_assoc
    (as bs cs : List α)
    : append (append as bs) cs = append as (append bs cs) := by
  apply List.recOn
      (motive := λ xs => append (append xs bs) cs = append xs (append bs cs))
      as
  · show append (append nil bs) cs = append nil (append bs cs)
    rfl
  · intro a as (ih : append (append as bs) cs = append as (append bs cs))
    show append (append (cons a as) bs) cs = append (cons a as) (append bs cs)
    calc
      _ = append (append (cons a as) bs) cs := rfl
      _ = append (cons a (append as bs)) cs := rfl
      _ = cons a (append (append as bs) cs) := rfl
      _ = cons a (append as (append bs cs)) := by rw [ih]
      _ = append (cons a as) (append bs cs) := rfl

def length (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => Nat.succ (length as)

example : length (nil : List Nat) = 0 := rfl
example : length (cons 42 nil) = 1 := rfl

theorem length_append
    (as bs : List α) : length (append as bs) = length as + length bs := by
  apply List.recOn
      (motive := λ xs => length (append xs bs) = length xs + length bs)
      as
  · show length (append nil bs) = length nil + length bs
    calc
      _ = length (append nil bs) := rfl
      _ = length bs              := rfl
      _ = 0 + length bs          := by rw [Nat.zero_add]
      _ = length nil + length bs := rfl
  · intro a as (ih : length (append as bs) = length as + length bs)
    show length (append (cons a as) bs) = length (cons a as) + length bs
    calc
      _ = length (append (cons a as) bs)   := rfl
      _ = length (cons a (append as bs))   := rfl
      _ = Nat.succ (length (append as bs)) := rfl
      _ = Nat.succ (length as + length bs) := by rw [ih]
      _ = Nat.succ (length as) + length bs := by rw [←Nat.succ_add]
      _ = length (cons a as) + length bs   := rfl

end List

inductive BinaryTree where
| leaf : BinaryTree
| node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree where
| leaf : CBTree
| sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (λ _ => t)

def toCBTree : Nat → CBTree
| 0 => leaf
| n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree

end other_recursive_data_types

/- Tactics for inductive types -/
namespace tactics_for_inductive_types

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  · exact hz -- goal is p 0
  · apply hs -- goal is a : ℕ ⊢ p (succ a)

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl

namespace cases_data

def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

end cases_data

namespace cases_tuple

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl

end cases_tuple

namespace cases_multi

inductive Foo where
| bar₁ : Nat → Nat → Foo
| bar₂ : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar₁ a b => exact b
  | bar₂ c d e => exact e

end cases_multi

namespace cases_multi_swap

inductive Foo where
| bar₁ : Nat → Nat → Foo
| bar₂ : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar₂ c d e => exact e
  | bar₁ a b => exact b

end cases_multi_swap

namespace case_tactic

inductive Foo where
| bar₁ : Nat → Nat → Foo
| bar₂ : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar₂ c d e => exact e
  case bar₁ a b => exact b

end case_tactic

namespace case_tactic_swap

inductive Foo where
| bar₁ : Nat → Nat → Foo
| bar₂ : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar₁ a b => exact b
  case bar₂ c d e => exact e

end case_tactic_swap

example
    (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
    : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz -- goal is p 0
  apply hs -- goal is a : ℕ ⊢ p (succ a)

example
    (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
    : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz
  apply hs

example (p : Prop) (m n : Nat) (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

example (p : Prop) (m n : Nat) (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne 

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

theorem zero_add_case (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]

namespace induction_examples

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp[*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_succ, succ_add]

theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]

end induction_examples

#check @Nat.mod.inductionOn

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    cases this with
    | inl h₁ => exact absurd h h₁
    | inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption  

example :
    (λ (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2) =
    (λ (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

example (m n k : Nat) (h : succ (succ m) = succ (succ n)) : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction

end tactics_for_inductive_types

/- Inductive families -/
namespace inductive_families

inductive Vector (α : Type u) : Nat → Type u where
| nil : Vector α 0
| cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

inductive Eq {α : Sort u} (a : α) : α → Prop where
| refl {} : Eq a a

#check @Eq.rec

theorem subst
    {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | Eq.refl _ => h₂

section
set_option pp.all true
#print subst
#print subst.match_1
#print Eq.casesOn
end

theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | Eq.refl _ => Eq.refl _

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by
  cases h₂ with
  | refl => exact h₁
  
theorem congr
    {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by
  cases h with
  | refl => exact Eq.refl (f a)

end inductive_families

/- Mutual and nested inductive types -/
namespace mutual_and_nested_inductive_types

mutual
  inductive Even : Nat → Prop where
  | even_zero : Even 0
  | even_succ : {n : Nat} → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
  | odd_succ : {n : Nat} → Even n → Odd (n + 1)
end

mutual
  inductive Tree (α : Type u) where
  | node : α → TreeList α → Tree α

  inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
end

inductive BetterTree (α : Type u) where
| mk : α → List (BetterTree α) → BetterTree α

end mutual_and_nested_inductive_types

/- Exercises -/
namespace exercises

namespace ex_1

open Nat

def mul (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => m + (mul n m)

theorem zero_mul {n : Nat} : mul 0 n = 0 := rfl

theorem mul_zero {n : Nat} : mul n 0 = 0 := by
  induction n
  case zero =>
    show mul 0 0 = 0
    rfl
  case succ n ih =>
    have : mul n 0 = 0 := ih
    show mul (succ n) 0 = 0
    calc
      _ = mul (succ n) 0 := rfl
      _ = 0 + mul n 0    := rfl
      _ = mul n 0        := by rw [Nat.zero_add]
      _ = 0              := by rw [ih]

theorem succ_mul {n m : Nat} : mul (succ n) m = m + mul n m := rfl

theorem mul_succ {n m : Nat} : mul m (succ n) = m + mul m n := by
  induction m
  case zero =>
    show mul 0 (succ n) = 0 + mul 0 n
    simp only [zero_mul, Nat.zero_add]
  case succ m ih =>
    have : mul m (succ n) = m + mul m n := ih
    show mul (succ m) (succ n) = succ m + mul (succ m) n
    calc
      _ = mul (succ m) (succ n)   := rfl
      _ = succ n + mul m (succ n) := by rw [succ_mul]
      _ = succ n + (m + mul m n)  := by rw [ih]
      _ = (succ n + m) + mul m n  := by rw [Nat.add_assoc]
      _ = succ (n + m) + mul m n  := by rw [Nat.succ_add]
      _ = (n + succ m) + mul m n  := by rw [Nat.add_succ]
      _ = (succ m + n) + mul m n  := by rw [Nat.add_comm n]
      _ = succ m + (n + mul m n)  := by rw [Nat.add_assoc]
      _ = succ m + mul (succ m) n := by rw [succ_mul]

theorem mul_comm {n m : Nat} : mul n m = mul m n := by
  induction n
  case zero =>
    show mul 0 m = mul m 0
    simp only [zero_mul, mul_zero]
  case succ n ih =>
    have : mul n m = mul m n := ih
    show mul (succ n) m = mul m (succ n)
    calc
      _ = mul (succ n) m := rfl
      _ = m + mul n m    := by rw [succ_mul]
      _ = m + mul m n    := by rw [ih]
      _ = mul m (succ n) := by rw [mul_succ]

theorem right_distrib {n m k : Nat} : mul (n + m) k = mul n k + mul m k := by
  induction n
  case zero =>
    show mul (0 + m) k = mul 0 k + mul m k
    calc
      _ = mul (0 + m) k     := rfl
      _ = mul m k           := by rw [Nat.zero_add]
      _ = 0 + mul m k       := by rw [Nat.zero_add]
      _ = mul 0 k + mul m k := by rw [zero_mul]
  case succ n ih =>
    have : mul (n + m) k = mul n k + mul m k := ih
    show mul (succ n + m) k = mul (succ n) k + mul m k
    calc
      _ = mul (succ n + m) k       := rfl
      _ = mul (succ (n + m)) k     := by rw [Nat.succ_add]
      _ = k + mul (n + m) k        := by rw [succ_mul]
      _ = k + (mul n k + mul m k)  := by rw [ih]
      _ = (k + mul n k) + mul m k  := by rw [Nat.add_assoc]
      _ = mul (succ n) k + mul m k := by rw [succ_mul]

theorem mul_assoc {n m k : Nat} : mul (mul n m) k = mul n (mul m k) := by
  induction n
  case zero =>
    show mul (mul 0 m) k = mul 0 (mul m k)
    calc
      _ = mul (mul 0 m) k := rfl
      _ = mul 0 k := by rw [zero_mul]
      _ = 0 := by rw [zero_mul]
      _ = mul 0 (mul m k) := by rw [zero_mul]
  case succ n ih =>
    have : mul (mul n m) k = mul n (mul m k) := ih
    show mul (mul (succ n) m) k = mul (succ n) (mul m k)
    calc
      _ = mul (mul (succ n) m) k    := rfl
      _ = mul (m + mul n m) k       := by rw [succ_mul]
      _ = mul m k + mul (mul n m) k := by rw [right_distrib]
      _ = mul m k + mul n (mul m k) := by rw [ih]
      _ = mul (succ n) (mul m k)    := by rw [succ_mul]

theorem one_mul {m : Nat} : mul 1 m = m := by
  calc
    _ = mul 1 m        := rfl
    _ = mul (succ 0) m := rfl
    _ = m + mul 0 m    := by rw [succ_mul]
    _ = m + 0          := by rw [zero_mul]
    _ = m              := by rw [Nat.add_zero]

def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => n

theorem pred_succ {n : Nat} : pred (succ n) = n := by
  cases n
  case zero =>
    show pred (succ 0) = 0
    rfl
  case succ n =>
    show pred (succ (succ n)) = succ n
    rfl

def sub (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => match m with
    | 0 => n+1
    | m+1 => sub n m

theorem zero_sub {n : Nat} : sub 0 n = 0 := rfl

theorem sub_zero {n : Nat} : sub n 0 = n := by
  cases n
  case zero =>
    show sub 0 0 = 0
    rfl
  case succ n =>
    show sub (succ n) 0 = succ n
    rfl

theorem sub_same {n : Nat} : sub n n = 0 := by
  induction n
  case zero =>
    show sub 0 0 = 0
    rfl
  case succ n ih =>
    have : sub n n = 0 := ih
    show sub (succ n) (succ n) = 0
    calc
      _ = sub (succ n) (succ n) := rfl
      _ = sub n n               := rfl
      _ = 0                     := by rw [ih]

def pow (n m : Nat) : Nat :=
  match m with
  | 0 => 1
  | m+1 => mul n (pow n m)

theorem pow_zero {n : Nat} : pow n 0 = 1 := rfl

theorem pow_succ {n m : Nat} : pow n (succ m) = mul n (pow n m) := rfl

theorem zero_pow {m : Nat} : pow 0 (succ m) = 0 := rfl

theorem pow_add {n m k : Nat} : pow n (m + k) = mul (pow n m) (pow n k) := by
  induction m
  case zero =>
    show pow n (0 + k) = mul (pow n 0) (pow n k)
    calc
      _ = pow n (0 + k)           := rfl
      _ = pow n k                 := by rw [Nat.zero_add]
      _ = mul 1 (pow n k)         := by rw [one_mul]
      _ = mul (pow n 0) (pow n k) := by rw [pow_zero]
  case succ m ih =>
    have : pow n (m + k) = mul (pow n m) (pow n k) := ih
    show pow n (succ m + k) = mul (pow n (succ m)) (pow n k)
    calc
      _ = pow n (succ m + k)              := rfl
      _ = pow n (succ (m + k))            := by rw [Nat.succ_add]
      _ = mul n (pow n (m + k))           := by rw [pow_succ]
      _ = mul n (mul (pow n m) (pow n k)) := by rw [ih]
      _ = mul (mul n (pow n m)) (pow n k) := by rw [mul_assoc]
      _ = mul (pow n (succ m)) (pow n k)  := by rw [pow_succ]

theorem pow_pow {n m k : Nat} : pow (pow n m) k = pow n (mul m k) := by
  induction k
  case zero =>
    show pow (pow n m) 0 = pow n (mul m 0)
    calc
      _ = pow (pow n m) 0 := rfl
      _ = 1               := by rw [pow_zero]
      _ = pow n 0         := by rw [pow_zero]
      _ = pow n (mul m 0) := by rw [mul_zero]
  case succ k ih =>
    have : pow (pow n m) k = pow n (mul m k) := ih
    show pow (pow n m) (succ k) = pow n (mul m (succ k))
    calc
      _ = pow (pow n m) (succ k)          := rfl
      _ = mul (pow n m) (pow (pow n m) k) := by rw [pow_succ]
      _ = mul (pow n m) (pow n (mul m k)) := by rw [ih]
      _ = pow n (m + mul m k)             := by rw [pow_add]
      _ = pow n (mul m (succ k))          := by rw [mul_succ]

end ex_1

namespace ex_2

def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => 1 + length xs

def reverse_helper (xs : List α) (acc : List α) : List α :=
  match xs with
  | [] => acc
  | x :: xs => reverse_helper xs (x :: acc)

def reverse (xs : List α) : List α :=
  reverse_helper xs []

theorem length_nil : length ([] : List α) = 0 := rfl

theorem length_cons
    {x : α} {xs : List α} : length (x :: xs) = 1 + length xs := rfl

theorem reverse_nil : reverse ([] : List α) = [] := rfl

theorem reverse_helper_append
    {xs : List α} : ∀ ys, reverse_helper xs ys = reverse xs ++ ys := by
  induction xs
  case nil =>
    show ∀ ys, reverse_helper [] ys = reverse [] ++ ys
    intro ys
    calc
      _ = reverse_helper [] ys := rfl
      _ = ys := rfl
      _ = [] ++ ys := by rw [List.nil_append]
      _ = reverse [] ++ ys := by rw [reverse_nil]
  case cons x xs ih =>
    have : ∀ ys, reverse_helper xs ys = reverse xs ++ ys := ih
    show ∀ ys, reverse_helper (x :: xs) ys = reverse (x :: xs) ++ ys
    intro ys
    calc
      _ = reverse_helper (x :: xs) ys       := rfl
      _ = reverse_helper xs (x :: ys)       := rfl
      _ = reverse xs ++ x :: ys             := by rw [ih]
      _ = reverse xs ++ x :: ([] ++ ys)     := by rw [List.nil_append]
      _ = reverse xs ++ ((x :: []) ++ ys)   := by rw [List.cons_append]
      _ = (reverse xs ++ (x :: [])) ++ ys   := by rw [List.append_assoc]
      _ = reverse_helper xs (x :: []) ++ ys := by rw [ih]
      _ = reverse_helper (x :: xs) [] ++ ys := rfl
      _ = reverse (x :: xs) ++ ys           := rfl

theorem reverse_cons_append
    {x : α} {xs ys : List α}
    : reverse (x :: xs) ++ ys = reverse xs ++ x :: ys := by
  calc
    _ = reverse (x :: xs) ++ ys           := rfl
    _ = reverse_helper (x :: xs) [] ++ ys := rfl
    _ = reverse_helper xs (x :: []) ++ ys := rfl
    _ = (reverse xs ++ (x :: [])) ++ ys   := by rw [reverse_helper_append]
    _ = reverse xs ++ ((x :: []) ++ ys)   := by rw [List.append_assoc]
    _ = reverse xs ++ (x :: ([] ++ ys))   := by rw [List.cons_append]
    _ = reverse xs ++ (x :: ys)           := by rw [List.nil_append]

theorem reverse_singleton {x : α} : reverse [x] = [x] := by
  calc
    _ = reverse [x]             := rfl
    _ = reverse (x :: [])       := rfl
    _ = reverse (x :: []) ++ [] := by rw [List.append_nil]
    _ = reverse [] ++ (x :: []) := by rw [reverse_cons_append]
    _ = [] ++ (x :: [])         := by rw [reverse_nil]
    _ = x :: []                 := by rw [List.nil_append]
    _ = [x]                     := rfl

theorem length_append
    {xs ys : List α} : length (xs ++ ys) = length xs + length ys := by
  induction xs
  case nil =>
    show length ([] ++ ys) = length [] + length ys
    calc
      _ = length ([] ++ ys)     := rfl
      _ = length ys             := by rw [List.nil_append]
      _ = 0 + length ys         := by rw [Nat.zero_add]
      _ = length [] + length ys := by rw [length_nil]
  case cons x xs ih =>
    have : length (xs ++ ys) = length xs + length ys := ih
    show length (x :: xs ++ ys) = length (x :: xs) + length ys
    calc
      _ = length (x :: xs ++ ys)       := rfl
      _ = length (x :: (xs ++ ys))     := by rw [List.cons_append]
      _ = 1 + length (xs ++ ys)        := by rw [length_cons]
      _ = 1 + (length xs + length ys)  := by rw [ih]
      _ = (1 + length xs) + length ys  := by rw [Nat.add_assoc]
      _ = length (x :: xs) + length ys := by rw [length_cons]

theorem length_reverse {xs : List α} : length (reverse xs) = length xs := by
  induction xs
  case nil =>
    show length (reverse []) = length []
    calc
      _ = length (reverse []) := rfl
      _ = length [] := by rw [reverse_nil]
  case cons x xs ih =>
    have : length (reverse xs) = length xs := ih
    show length (reverse (x :: xs)) = length (x :: xs)
    calc
      _ = length (reverse (x :: xs))       := rfl
      _ = length (reverse (x :: xs) ++ []) := by rw [List.append_nil]
      _ = length (reverse xs ++ (x :: [])) := by rw [reverse_cons_append]
      _ = length (reverse xs) + length [x] := by rw [length_append]
      _ = length [x] + length (reverse xs) := by rw [Nat.add_comm]
      _ = length [x] + length xs           := by rw [ih]
      _ = 1 + length xs                    := rfl
      _ = length (x :: xs)                 := by rw [length_cons]

theorem reverse_append
    {xs ys : List α} : reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  induction xs
  case nil =>
    show reverse ([] ++ ys) = reverse ys ++ reverse []
    calc 
      _ = reverse ([] ++ ys)       := rfl
      _ = reverse ys               := by rw [List.nil_append]
      _ = reverse ys ++ []         := by rw [List.append_nil]
      _ = reverse ys ++ reverse [] := by rw [reverse_nil]
  case cons x xs ih =>
    have : reverse (xs ++ ys) = reverse ys ++ reverse xs := ih
    show reverse ((x :: xs) ++ ys) = reverse ys ++ reverse (x :: xs)
    calc
      _ = reverse ((x :: xs) ++ ys)               := rfl
      _ = reverse (x :: (xs ++ ys))               := by rw [List.cons_append]
      _ = reverse (x :: (xs ++ ys)) ++ []         := by rw [List.append_nil]
      _ = reverse (xs ++ ys) ++ (x :: [])         := by rw [reverse_cons_append]
      _ = (reverse ys ++ reverse xs) ++ (x :: []) := by rw [ih]
      _ = reverse ys ++ (reverse xs ++ (x :: [])) := by rw [List.append_assoc]
      _ = reverse ys ++ (reverse (x :: xs) ++ []) := by rw [reverse_cons_append]
      _ = reverse ys ++ reverse (x :: xs)         := by rw [List.append_nil]

theorem reverse_reverse {xs : List α} : reverse (reverse xs) = xs := by
  induction xs
  case nil =>
    show reverse (reverse []) = []
    calc
      _ = reverse (reverse []) := rfl
      _ = reverse []           := rfl
      _ = []                   := rfl
  case cons x xs ih =>
    have : reverse (reverse xs) = xs := ih
    show reverse (reverse (x :: xs)) = x :: xs
    calc
      _ = reverse (reverse (x :: xs))               := rfl
      _ = reverse (reverse (x :: xs) ++ [])         := by rw [List.append_nil]
      _ = reverse (reverse xs ++ (x :: []))         := by rw [reverse_cons_append]
      _ = reverse (x :: []) ++ reverse (reverse xs) := by rw [reverse_append]
      _ = reverse (x :: []) ++ xs                   := by rw [ih]
      _ = (x :: []) ++ xs                           := by rw [reverse_singleton]
      _ = x :: ([] ++ xs)                           := by rw [List.cons_append]
      _ = x :: xs                                   := by rw [List.nil_append]

end ex_2

namespace ex_3

inductive Term (V : Type u) where
| const (n : Nat)
| var (v : V)
| plus (s t : Term V) : Term V
| times (s t : Term V) : Term V

namespace Term

def eval {V : Type u} (varValue : V → Nat) (t : Term V) : Nat :=
  match t with
  | const n => n
  | var v => varValue v
  | plus s t => eval varValue s + eval varValue t
  | times s t => eval varValue s * eval varValue t

def simpleTerm : Term String := times (plus (var "x") (const 3)) (var "y")

def simpleVars (s : String) : Nat :=
  match s with
  | "x" => 1
  | "y" => 2
  | _ => 0

example : eval simpleVars simpleTerm = 8 := rfl

end Term

end ex_3

namespace ex_4

inductive BinOp where
| And | Or | Implies | Iff

inductive Formula (V : Type u) where
| const (b : Bool)
| var (v : V)
| not (p : Formula V)
| binOp (op : BinOp) (p q : Formula V)

open BinOp
open Formula

def and {V : Type u} (p q : Formula V) : Formula V := binOp And p q
def or {V : Type u} (p q : Formula V) : Formula V := binOp Or p q
def implies {V : Type u} (p q : Formula V) : Formula V := binOp Implies p q
def iff {V : Type u} (p q : Formula V) : Formula V := binOp Iff p q

def eval {V : Type u} (vars : V → Bool) (formula : Formula V) : Bool :=
  match formula with
  | const b => b
  | var v => vars v
  | Formula.not p => !(eval vars p)
  | binOp op p q =>
    let boolOp :=
      match op with
      | BinOp.And => (· && ·)
      | BinOp.Or => (· || ·)
      | BinOp.Implies => λ p q => p && !q
      | BinOp.Iff => (· == ·)
    boolOp (eval vars p) (eval vars q)

example : eval (λ _ : String => false) (const true) = true := rfl
example : eval (λ v => v == "x") (var "x") = true := rfl
example : eval (λ v => v == "x") (var "y") = false := rfl
example : eval (λ v => v == "x") (not (var "x")) = false := rfl

example 
  : eval (λ v => v == "x" || v == "y") (and (var "x") (var "y")) = true
  := rfl

example
  : eval (λ v => v == "x" || v != "y") (and (var "x") (var "y")) = false
  := rfl

example
  : eval (λ v => v != "x" || v == "y") (and (var "x") (var "y")) = false
  := rfl

def node_count {V : Type u} (formula : Formula V) : Nat :=
  let children_node_count := match formula with
  | const _ => 0
  | var _ => 0
  | Formula.not p => node_count p
  | binOp _ p q => node_count p + node_count q
  1 + children_node_count

example : node_count (var "x") = 1 := rfl
example : node_count (or (const false) (var "y")) = 3 := rfl

def formula_vars {V : Type u} (formula : Formula V) : List V :=
  match formula with
  | const _ => []
  | var v => [v]
  | Formula.not p => formula_vars p
  | binOp _ p q => formula_vars p ++ formula_vars q

def and_assoc : Formula String :=
  let p := var "p"
  let q := var "q"
  let r := var "r"
  iff (and (and p q) r) (and p (and q r))

example : (formula_vars and_assoc).contains "p" = true := rfl
example : (formula_vars and_assoc).contains "q" = true := rfl
example : (formula_vars and_assoc).contains "r" = true := rfl
example : (formula_vars and_assoc).contains "s" = false := rfl
example : (formula_vars and_assoc).contains "t" = false := rfl

def substitute
    {V : Type u} [BEq V] (into : Formula V) (v : V) (formula : Formula V)
    : Formula V :=
  match into with
  | const c => const c
  | var w => if v == w then formula else var w
  | Formula.not p => not (substitute p v formula)
  | binOp op p q => binOp op (substitute p v formula) (substitute q v formula)

def lem : Formula String := or (var "p") (not (var "p"))
def qr : Formula String := and (var "q") (var "r")
example : substitute lem "p" qr = or qr (not qr) := rfl

end ex_4

end exercises
