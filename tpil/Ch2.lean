/- Simple type theory -/
namespace simple_type_theory
-- Note: using namespaces early just to prevent conflicts

/- Define some constants. -/

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

/- Check their types. -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

/- Evaluate -/

#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat
#check Nat -> Nat

#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add

#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2

#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2

end simple_type_theory

/- Types as objects -/
namespace types_as_objects

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

#check Prod α β
#check α × β

#check Prod Nat Nat
#check Nat × Nat

#check List α
#check List Nat

#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Type
#check Type 0

#check List
#check Prod

namespace explicit_universe

universe u

def F (α : Type u) : Type u := Prod α α

#check F

end explicit_universe

namespace param_universe

def F.{u} (α : Type u) : Type u := Prod α α

#check F

end param_universe

end types_as_objects

/- Function abstraction and evaluation -/
namespace function_abs_eval

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#check fun x : Nat => x + 5
#check λ x : Nat => x + 5
#check fun x => x + 5
#check λ x => x + 5

#eval (λ x => x + 5) 10

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x
#check fun x : Nat => true
#check fun x : Nat => g (f x)
#check fun x => g (f x)

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

#check (fun x : Nat => x) 1
#check (fun x : Nat => true) 1

#check
  (fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x))
  Nat String Bool g f 0

#eval (fun x : Nat => x) 1
#eval (fun x : Nat => true) 1

end function_abs_eval

/- Definitions -/
namespace definitions

def double (x : Nat) : Nat :=
  x + x

#eval double 3

def double2 : Nat → Nat :=
  fun x => x + x

#eval double2 3

def double3 :=
  fun (x : Nat) => x + x

def pi := 3.14159265358979323846264

def add (x y : Nat) :=
  x + y

#eval add 3 2

def add2 (x : Nat) (y : Nat) :=
  x + y

#eval add2 (double 3) (7 + 9)

def greater (x y : Nat) :=
  if x > y then x
  else y

def doTwice (f : Nat → Nat) (x : Nat) :=
  f (f x)

#eval doTwice double 2

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3

end definitions

/- Local definitions -/
namespace local_definitions

#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2
-- def bar := (fun a => fun x : a => x + 2) Nat

end local_definitions

/- Variables and sections -/
namespace variables_and_sections

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose_var := g (f x)
def doTwice_var := h (h x)
def doThrice_var := h (h (h x))

#print compose_var
#print doTwice_var
#print doThrice_var

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose_sec := g (f x)
  def doTwice_sec := h (h x)
  def doThrice_sec := h (h (h x))
end useful

end variables_and_sections

/- Namespaces -/
namespace namespaces

namespace simple

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a -- error
-- #check f -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

end simple

namespace nested

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa

end nested

namespace reopen

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo

end reopen

end namespaces

/- What makes dependent type theory dependent? -/
namespace dependent

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat
#check cons Bool
#check cons

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

universe u
universe v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a)
    : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a)
    : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5

def h2 (x : Nat) : Nat :=
  (g Type (λ α => α) Nat x).2

#eval h2 5

end dependent

/- Implicit arguments -/
namespace implicit

universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α :=
  List.cons a as

def Lst.nil {α : Type u} : Lst α := List.nil

def Lst.append {α : Type u} (as bs : Lst α) : Lst α :=
  List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs

def ident {α : Type u} (x : α) := x

#check ident
#check ident 1
#check ident "hello"
#check @ident

namespace vars
  section 
    variable {α : Type u}
    variable (x : α)
    def ident := x
  end

  #check ident
  #check ident 4
  #check ident "hello"

end vars

#check List.nil
#check id

#check (List.nil : List Nat)
#check (id : Nat → Nat)

#check 2
#check (2 : Nat)
#check (2 : Int)

#check @id
#check @id Nat
#check @id Bool

#check @id Nat 1
#check @id Bool true

end implicit
