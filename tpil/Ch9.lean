/-= Chapter 9: Structures and records =-/

/- Declaring structures -/
namespace declaring_structures

structure Point (α : Type u) where
  mk :: (x : α) (y : α)

#check Point
#check @Point.rec
#check @Point.mk
#check @Point.x
#check @Point.y

namespace alternate_form

structure Point (α : Type u) where
  rect ::
  x : α
  y : α

example : Point Nat := Point.rect 3 4

end alternate_form

namespace default_constructor

structure Point (α : Type u) where
  x : α
  y : α

example : Point Nat := Point.mk 3 4

end default_constructor

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a := rfl
example (a b : α) : y (mk a b) = b := rfl

def p := Point.mk 10 20

#check p.x
#eval p.x
#eval p.y

namespace dot_notation

structure Point (α : Type u) where
  rect ::
  x : α
  y : α
deriving Repr

def Point.add (p q : Point Nat) :=
  Point.rect (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.rect 1 2
def q : Point Nat := Point.rect 3 4

#eval p.add q

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.rect (n * p.x) (n * p.y)

#eval p.smul 3

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := λ x => x * x

#eval xs.map f

end dot_notation

end declaring_structures

/- Objects -/
namespace objects

namespace basic_point

structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }
#check { y := 20, x := 10 : Point _ }
#check ({ x := 10, y := 20 } : Point Nat )

example : Point Nat := { y := 20, x := 10 }

end basic_point

namespace field_inference

structure MyStruct where
  {α : Type u}
  {β : Type v}
  a : α
  b : β

#check { a := 10, b := true : MyStruct }

end field_inference

namespace record_update

structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def p : Point Nat := { x := 1, y := 2 }

#eval { p with y := 3 }
#eval { p with x := 4 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat := { x := 5, y := 5, z := 5 }
def r : Point3 Nat := { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl

end record_update

end objects

/- Inheritance -/
namespace inheritance

namespace simple

structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
| red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color

end simple

namespace multiple

structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RgbValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RgbValue where
  no_blue : blue = 0

def p : Point Nat := { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0,  no_blue := rfl }

example : rgp.x = 10 := rfl
example : rgp.red = 200 := rfl

end multiple

end inheritance
