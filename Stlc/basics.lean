import Mathlib.Tactic

-- Basic types --
inductive Typ : Type
| typ_base : Typ
| typ_arrow : Typ → Typ → Typ
deriving DecidableEq, Repr

-- Defining (pre)terms by recursion --
inductive Trm : Type
| bvar : ℕ → Trm
| fvar : ℕ → Trm
| abs : Trm → Trm
| app : Trm → Trm → Trm
deriving DecidableEq, Repr

namespace Trm

-- Notations --
notation t1 " -> " t2 => Typ.typ_arrow t1 t2
notation "€" t => bvar t
notation "$" t => fvar t
notation "λ" t => abs t
notation t1 " @ " t2 => app t1 t2

-- Defining substitution by induction on terms --
@[simp]
def subst (x : ℕ) (a : Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if y = x then a else (fvar y)
| abs u => abs (subst x a u)
| app u1 u2 => app (subst x a u1) (subst x a u2)

notation  "["x" // " a"] "u => subst x a u

-- Free variables --
def fv : Trm → Finset ℕ
| bvar _ => {}
| fvar y => {y}
| abs u => fv u
| app u1 u2 => (fv u1) ∪ (fv u2)

--We can always pick a fresh variable for a given term out of a fixed set.
lemma pick_fresh (t : Trm) (L : Finset ℕ) : ∃ (x : ℕ), x ∉ (L ∪ fv t) := by
  exact Infinite.exists_not_mem_finset (L ∪ fv t)

-- If a variable does not appear free in a term, then substituting for it has no effect --
lemma subst_fresh (t s : Trm) (y : ℕ) (h : y ∉ (fv t)) : ([y // s] t) = t := by
  induction t
  case bvar i =>
    rfl
  case fvar i =>
    simp only [subst]
    rw [if_neg]
    simp [fv] at h
    exact (fun p => h (p.symm))
  case abs u hu =>
    simp only [subst, abs.injEq]
    exact (hu h)
  case app u1 u2 h1 h2 =>
    simp only [subst, app.injEq]
    simp [fv] at h
    push_neg at h
    exact ⟨(h1 h.1), (h2 h.2)⟩
