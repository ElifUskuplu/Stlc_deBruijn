import Stlc.basics
import Stlc.context
import Stlc.reductions

open Typ
open Trm
open subst
open beta_red
open multi_red
open lc

namespace Trm

-- Defining substitutions over contexts --
@[simp]
def multi_subst (L : Finset ℕ) (f : L → Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if h : (y ∈ L) then (f ⟨y, h⟩) else (fvar y)
| abs T u => abs T (multi_subst L f u)
| app u1 u2 => app (multi_subst L f u1) (multi_subst L f u2)

--context_type takes a term in a context and outputs its type
@[simp]
def context_type Γ (x : context_terms Γ) : Typ :=
  match Γ, x with
  | [], ⟨_, h⟩ => by simp [context_terms] at h
  | (x, T) :: Γ, ⟨x', h⟩ =>
    if ha : x' = x then
      T
    else
      context_type Γ ⟨x', by simpa [context_terms, ha] using h⟩

--substitution over the empty context does nothing
lemma multi_subst_over_emp t (f : context_terms [] → Trm) :
    (multi_subst (context_terms []) f t) = t := by
  induction t
  case bvar i =>
    simp
  case fvar x =>
    simp
  case abs T t' ih =>
    simp at ih ⊢
    rw [ih]
  case app t1 t2 ih1 ih2 =>
    simp at ih1 ih2 ⊢
    exact ⟨ih1, ih2⟩

--substitution over [(x,T)] is the same as usual (single) substitution
lemma multi_subst_at_singleton t x T :
    (f : context_terms [(x, T)] → Trm)
    → (multi_subst (context_terms [(x, T)]) f t)
      = ([x // (f ⟨x, by simp⟩)] t) := by
  intro f
  induction t
  case bvar i =>
    simp
  case fvar y =>
    simp
    by_cases h : y = x
    . simp [h]
    . simp [h]
  case abs T t' ih =>
    simp
    exact ih
  case app t1 t2 ih1 ih2 =>
    simp
    exact ⟨ih1, ih2⟩

--if we have a function of terms of a context, say f,
--for a term u and variable x, we can extend the f with mapping x → u
@[simp]
def add_term Γ (f : context_terms Γ → Trm)
    (u : Trm) y T (x : context_terms ((y , T) :: Γ)) : Trm := by
  rcases x with ⟨x' , h⟩
  by_cases p : x' = y
  . exact u
  . simp [p] at h
    exact f ⟨x' , h⟩

--If y does not appear in t, then substitution over a context (y,T) ++ Γ
--is the same as substitution over Γ
lemma multi_subst_fresh Γ t u y T (h : y ∉ (fv t)) (f : context_terms Γ → Trm) :
    (multi_subst (context_terms ((y , T) :: Γ)) (add_term Γ f u y T) t)
     = (multi_subst (context_terms Γ) f t) := by
  induction t
  case bvar i =>
    rfl
  case fvar x =>
    simp [fv] at h
    simp only [multi_subst, context_terms, Finset.mem_union, Finset.mem_singleton, add_term]
    have p : x ≠ y := fun q => h q.symm
    simp [p]
  case abs T u hu =>
    simp only [multi_subst, abs.injEq]
    constructor
    simp only
    exact (hu h)
  case app u1 u2 h1 h2 =>
    simp only [multi_subst, app.injEq]
    simp [fv] at h
    exact ⟨(h1 h.1), (h2 h.2)⟩


--substitution over a context distributes over opening
lemma multi_subst_open_lemma_1 t1 t2 Γ : (f : context_terms Γ → Trm)
   → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩)) → (j : ℕ)
   → (multi_subst (context_terms Γ) f ({j ~> t2} t1))
     = ({j ~> multi_subst (context_terms Γ) f t2} (multi_subst (context_terms Γ) f t1)) := by
  induction t1
  case bvar k =>
    simp
    intros f _ j
    by_cases hjy : (j = k)
    . rw [if_pos, if_pos] <;> exact hjy
    . rw [if_neg, if_neg, multi_subst]
      <;> exact hjy
  case fvar y =>
   intro f lcf j
   by_cases hy : (y ∈ context_terms Γ)
   . simp [opening, multi_subst, hy]
     exact (opening_lc (f ⟨y, hy⟩) _ (lcf y hy) _)
   . simp [opening, multi_subst, hy]
  case abs T u ihu =>
   intro f lcf j
   simp [opening, multi_subst]
   exact (ihu f lcf (j + 1))
  case app u1 u2 ihu1 ihu2 =>
   intro f lcf j
   simp [opening, multi_subst]
   exact ⟨ihu1 f lcf j, ihu2 f lcf j⟩

--special case of previous fact at j=0
lemma multi_subst_open_lemma_2 Γ t u y T : lc u → y ∉ fv t
    → (f : context_terms Γ → Trm)
    → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩))
    → (multi_subst (context_terms ((y , T) :: Γ)) (add_term Γ f u y T) (open₀ t ($ y)))
      = (open₀ (multi_subst (context_terms Γ) f t) u) := by
  intro lcu hy f lcf
  rw [open₀ , multi_subst_open_lemma_1, multi_subst, ← open₀]
  rw [multi_subst_fresh Γ t u y T hy f]
  simp
  intro x h
  by_cases p : x = y
  . simp [p]
    exact lcu
  . simp [p] at h ⊢
    exact lcf x h

--When we open a term, we can instead open the term with a fresh variable and
--then multi-substitute for that variable.
lemma multi_subst_open Γ t y : y ∉ context_terms Γ
    → (f : context_terms Γ → Trm)
    → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩))
    → (multi_subst (context_terms Γ) f (open₀ t ($ y)))
      = (open₀ (multi_subst (context_terms Γ) f t) ($ y)) := by
  intro hy f lcf
  rw [open₀ , multi_subst_open_lemma_1, multi_subst, ← open₀]
  simp [hy]
  apply lcf

--if (x,T) appears in context Γ, then the context map sends Γ x to T
lemma context_type_eq_bind Γ (x : context_terms Γ) T :
    valid_ctx Γ → binds x T Γ → context_type Γ x = T := by
  induction Γ
  case nil =>
    intro _ bnd
    cases bnd
  case cons h Γ' ih =>
    intro vld bnd
    simp only [context_type, context_terms]
    by_cases p : h.1 = ↑x
    . simp [p] at bnd ⊢
      apply bnd
    . have q : (↑x ≠ h.1) := (fun z => p (z.symm))
      simp [q]
      apply ih
      apply valid_remove_cons _ _ _ vld
      apply binds_remove_mid_cons ↑x h.1 T h.2 Γ' [] bnd
      symm
      exact p

--if a term is locally closed, and there is list of locally closed terms, then
--substition with these terms is also locally closed.
lemma multi_subst_lc t Γ : lc t
    → (f : context_terms Γ → Trm)
    → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩))
    → lc ((multi_subst (context_terms Γ) f t)) := by
  intro lct f lcf
  induction lct
  case lc_var y =>
    rw [multi_subst]
    by_cases hxy : y ∈ context_terms Γ
    . simp [if_pos, hxy]
      exact (lcf y hxy)
    . simp [if_neg, hxy]
      exact (lc_var y)
  case lc_abs u T L a hu =>
    simp
    apply lc_abs _ _ (L ∪ (context_terms Γ))
    intro x hx
    simp at hx
    rw [← multi_subst_open Γ u x hx.2 f lcf]
    apply hu x hx.1
  case lc_app u1 u2 lcu1 lcu2 hu1 hu2 =>
    dsimp [multi_subst]
    apply (lc_app _ _ hu1 hu2)
