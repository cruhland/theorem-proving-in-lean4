/-== Chapter 3: Propositions and proofs ==-/

/- Working with propositions as types -/
namespace working_with_props

variable {p q : Prop}

theorem t1 : p → q → p := λ hp hq => hp

#print t1

namespace using_show

  theorem t1 : p → q → p :=
    λ hp : p =>
    λ hq : q =>
    show p from hp

end using_show

namespace as_function

  theorem t1 (hp : p) (hq : q) : p := hp

  #print t1

  axiom hp : p

  theorem t2 : q → p := t1 hp

end as_function

namespace axiom_unsafe

  axiom unsound : False
  -- Everything follows from false
  theorem ex : 1 = 0 :=
    False.elim unsound

end axiom_unsafe

namespace max_args

  theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp
  #print t1

end max_args

namespace min_args

  theorem t1 : ∀ {p q : Prop}, p → q → p :=
    fun {p q : Prop} (hp : p) (hq : q) => hp
  
  #print t1

end min_args

namespace prop_vars

  variable {p q : Prop}
  theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
  #print t1

end prop_vars

namespace more_prop_vars

  variable {p q : Prop}
  variable (hp : p)

  theorem t1 : q → p := fun (hq : q) => hp
  #print t1

end more_prop_vars

namespace apply_theorem

  theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

  variable (p q r s : Prop)

  #check t1 p q
  #check t1 r s
  #check t1 (r → s) (s → r)

  variable (h : r → s)
  #check t1 (r → s) (s → r) h

end apply_theorem

variable (p q r s : Prop)

-- Implication is transitive / function composition
theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

end working_with_props

/- Propositional logic -/
namespace propositional_logic

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

-- Conjunction
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p := 
  And.intro (And.right h) (And.left h)

#check λ (hp : p) (hq : q) => (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)

#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

-- Disjunction
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

variable (r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example (h : p ∨ q) : q ∨ p := h.elim Or.inr Or.inl

-- Negation and falsity
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p => 
  show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

-- Logical equivalence
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

example (h : p ∧ q) : q ∧ p := Iff.mp (and_swap p q) h

namespace concise

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    ⟨λ h => ⟨h.right, h.left⟩, λ h => ⟨h.right, h.left⟩⟩

  example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

end concise

end propositional_logic

/- Introducing auxiliary subgoals -/
namespace auxiliary

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

end auxiliary

/- Classical logic -/
namespace classical_logic

open Classical

variable (p : Prop)
#check em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
  (em p).elim
    (λ hp : p => hp)
    (λ hnp : ¬p => absurd hnp h)

example {p : Prop} (h : {q : Prop} → ¬¬q → q) : p ∨ ¬p :=
  suffices em_irrefutable : ¬¬(p ∨ ¬p) from h em_irrefutable
  show ¬¬(p ∨ ¬p) from λ em_refutable : ¬(p ∨ ¬p) =>
    suffices em₁ : p ∨ ¬p from absurd em₁ em_refutable
    show p ∨ ¬p from Or.inr λ hp : p =>
      suffices em₂ : p ∨ ¬p from absurd em₂ em_refutable
      show p ∨ ¬p from Or.inl hp

example (h : ¬¬p) : p :=
  byCases
    (λ hp : p => hp)
    (λ hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byContradiction (λ hnp : ¬p => show False from h hnp)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  (em p).elim
    (λ hp : p => 
      suffices hnq : ¬q from Or.inr hnq
      show ¬q from λ hq : q =>
        have hpq : p ∧ q := ⟨hp, hq⟩
        show False from absurd hpq h)
    (λ hnp : ¬p => Or.inl hnp)

end classical_logic

/- Exercises -/
namespace exercises

variable (p q r s : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  have swap : ∀ {x y : Prop}, x ∧ y → y ∧ x :=
    λ {x y : Prop} (hxy : x ∧ y) => ⟨hxy.right, hxy.left⟩
  ⟨swap, swap⟩

example : p ∨ q ↔ q ∨ p :=
  have swap : ∀ {x y : Prop}, x ∨ y → y ∨ x :=
    λ {x y : Prop} (hxy : x ∨ y) => hxy.elim Or.inr Or.inl
  ⟨swap, swap⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have fwd : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
    λ h : (p ∧ q) ∧ r =>
      have hp : p := h.left.left
      have hq : q := h.left.right
      have hr : r := h.right
      show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩
  have rev : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
    λ h : p ∧ (q ∧ r) =>
      have hp : p := h.left
      have hq : q := h.right.left
      have hr : r := h.right.right
      show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩
  show (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) from ⟨fwd, rev⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have fwd : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    λ hpqr : (p ∨ q) ∨ r => show p ∨ (q ∨ r) from hpqr.elim
      (λ hpq : p ∨ q => show p ∨ (q ∨ r) from hpq.elim
        (λ hp : p => Or.inl hp)
        (λ hq : q => Or.inr (Or.inl hq)))
      (λ hr : r => show p ∨ (q ∨ r) from Or.inr (Or.inr hr))
  have rev : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
    λ hpqr : p ∨ (q ∨ r) => show (p ∨ q) ∨ r from hpqr.elim
      (λ hp : p => show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
      (λ hqr : q ∨ r => show (p ∨ q) ∨ r from hqr.elim
        (λ hq : q => Or.inl (Or.inr hq))
        (λ hr : r => Or.inr hr))
  show (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) from ⟨fwd, rev⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have fwd : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := λ hpqr =>
    have hp : p := hpqr.left
    have hqr : q ∨ r := hpqr.right
    show (p ∧ q) ∨ (p ∧ r) from hqr.elim
      (λ hq => Or.inl ⟨hp, hq⟩)
      (λ hr => Or.inr ⟨hp, hr⟩)
  have rev : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := λ hpqpr =>
    show p ∧ (q ∨ r) from hpqpr.elim
      (λ hpq => ⟨hpq.left, Or.inl hpq.right⟩)
      (λ hpr => ⟨hpr.left, Or.inr hpr.right⟩)
  show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) from ⟨fwd, rev⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  have fwd : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) := λ hpqr =>
    show (p ∨ q) ∧ (p ∨ r) from hpqr.elim
      (λ hp => ⟨Or.inl hp, Or.inl hp⟩)
      (λ hqr => ⟨Or.inr hqr.left, Or.inr hqr.right⟩)
  have rev : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) := λ hpqpr =>
    have hpq : p ∨ q := hpqpr.left
    have hpr : p ∨ r := hpqpr.right
    show p ∨ (q ∧ r) from hpq.elim
      (λ hp => Or.inl hp)
      (λ hq => show p ∨ (q ∧ r) from hpr.elim
        (λ hp => Or.inl hp)
        (λ hr => Or.inr ⟨hq, hr⟩))
  show p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) from ⟨fwd, rev⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  have fwd : (p → (q → r)) → (p ∧ q → r) :=
    λ (hpqr : p → (q → r)) (hpq : p ∧ q) =>
      show r from hpqr hpq.left hpq.right
  have rev : (p ∧ q → r) → (p → (q → r)) :=
    λ (hpqr : p ∧ q → r) (hp : p) (hq : q) =>
      show r from hpqr ⟨hp, hq⟩
  show (p → (q → r)) ↔ (p ∧ q → r) from ⟨fwd, rev⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have fwd : ((p ∨ q) → r) → (p → r) ∧ (q → r) := λ hpqr =>
    have gpr : p → r := λ hp => hpqr (Or.inl hp)
    have gqr : q → r := λ hq => hpqr (Or.inr hq)
    show (p → r) ∧ (q → r) from ⟨gpr, gqr⟩
  have rev : (p → r) ∧ (q → r) → ((p ∨ q) → r) :=
    λ (hprqr : (p → r) ∧ (q → r)) (hpq : p ∨ q) =>
      have hpr : p → r := hprqr.left
      have hqr : q → r := hprqr.right
      show r from hpq.elim hpr hqr
  show ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) from ⟨fwd, rev⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have fwd : ¬(p ∨ q) → ¬p ∧ ¬q := λ hnpq =>
    have gnp : ¬p := λ hp => hnpq (Or.inl hp)
    have gnq : ¬q := λ hq => hnpq (Or.inr hq)
    show ¬p ∧ ¬q from ⟨gnp, gnq⟩
  have rev : ¬p ∧ ¬q → ¬(p ∨ q) :=
    λ (hnpnq : ¬p ∧ ¬q) (hpq : p ∨ q) =>
      have hnp : ¬p := hnpnq.left
      have hnq : ¬q := hnpnq.right
      show False from hpq.elim
        (λ hp : p => absurd hp hnp)
        (λ hq : q => absurd hq hnq)
  show ¬(p ∨ q) ↔ ¬p ∧ ¬q from ⟨fwd, rev⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ (hnpnq : ¬p ∨ ¬q) (hpq : p ∧ q) =>
    have hp : p := hpq.left
    have hq : q := hpq.right
    show False from hnpnq.elim
      (λ hnp : ¬p => absurd hp hnp)
      (λ hnq : ¬q => absurd hq hnq)

example : ¬(p ∧ ¬p) := λ hpnp =>
  have hp : p := hpnp.left
  have hnp : ¬p := hpnp.right
  show False from absurd hp hnp

example : p ∧ ¬q → ¬(p → q) :=
  λ (hpnq : p ∧ ¬q) (hpq : p → q) =>
    have hp : p := hpnq.left
    have hq : q := hpq hp
    have hnq : ¬q := hpnq.right
    show False from absurd hq hnq

example : ¬p → (p → q) :=
  λ (hnp : ¬p) (hp : p) =>
    show q from absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  λ (hnpq : ¬p ∨ q) (hp : p) =>
    show q from hnpq.elim
      (λ hnp : ¬p => absurd hp hnp)
      (λ hq : q => hq)

example : p ∨ False ↔ p :=
  have fwd : p ∨ False → p := λ hpf =>
    show p from hpf.elim
      (λ hp : p => hp)
      (λ hf : False => hf.elim)
  have rev : p → p ∨ False :=
    Or.inl
  show p ∨ False ↔ p from ⟨fwd, rev⟩

example : p ∧ False ↔ False :=
  have fwd : p ∧ False → False := And.right
  have rev : False → p ∧ False := False.elim
  show p ∧ False ↔ False from ⟨fwd, rev⟩

example : (p → q) → (¬q → ¬p) :=
  λ (hpq : p → q) (hnq : ¬q) (hp : p) =>
    have hq : q := hpq hp
    show False from hnq hq

example : ¬(p ↔ ¬p) := λ p_iff_np =>
  have hpnp : p → ¬p := p_iff_np.mp
  have hnpp : ¬p → p := p_iff_np.mpr
  have hnp : ¬p := λ hp => hpnp hp hp
  have hnnp : ¬¬p := λ hnp => hnp (hnpp hnp)
  show False from hnnp hnp

open Classical

def contrapositive_rev {p q : Prop} (hnqnp : ¬q → ¬p) (hp : p) : q :=
  (em q).elim
    (λ hq : q => hq)
    (λ hnq : ¬q => absurd hp (hnqnp hnq))

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := λ hprs =>
  show (p → r) ∨ (p → s) from (em r).elim
    (λ hr : r =>
      have gpr : p → r := λ _ => hr
      show (p → r) ∨ (p → s) from Or.inl gpr)
    (λ hnr : ¬r =>
      have gps : p → s := λ hp =>
        (hprs hp).elim
          (λ hr : r => show s from absurd hr hnr)
          (λ hs : s => show s from hs)
      show (p → r) ∨ (p → s) from Or.inr gps)

example : ¬(p ∧ q) → ¬p ∨ ¬q := λ hnpq =>
  show ¬p ∨ ¬q from (em p).elim
    (λ hp : p => show ¬p ∨ ¬q from (em q).elim
      (λ hq : q => absurd ⟨hp, hq⟩ hnpq)
      (λ hnq : ¬q => Or.inr hnq))
    (λ hnp : ¬p => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q := λ hnpq =>
  (em q).elim
    (λ hq : q => absurd (λ hp : p => hq) hnpq)
    (λ hnq : ¬q => (em p).elim
      (λ hp : p => ⟨hp, hnq⟩)
      (λ hnp : ¬p =>
        have hpq : p → q := contrapositive_rev (λ hnq : ¬q => hnp)
        show p ∧ ¬q from absurd hpq hnpq))

example : (p → q) → (¬p ∨ q) := λ hpq =>
  (em p).elim
    (λ hp : p => Or.inr (hpq hp))
    (λ hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) := contrapositive_rev

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := λ hpqp =>
  show p from (em p).elim
    (λ hp : p =>
      show p from hp)
    (λ hnp : ¬p =>
      have gpq : p → q := λ hp =>
        show q from absurd hp hnp
      show p from hpqp gpq)

end exercises
