import Stlc.basics
import Stlc.open_close
import Stlc.context
import Stlc.reductions

open Typ
open Trm
open List

--Typing judgment
inductive typing : context → Trm → Typ → Prop
| typ_var (Γ : context) (x : ℕ) (T : Typ) : (valid_ctx Γ) → (binds x T Γ) → (typing Γ ($ x) T)
| typ_abs (L : Finset ℕ) (Γ : context) (t : Trm) (T1 T2 : Typ) :
        ((x : ℕ) → x ∉ L → (typing ((x, T1) :: Γ) (open₀ t ($ x)) T2)) → (typing Γ (abs t) (typ_arrow T1 T2))
| typ_app (Γ : context) (t₁ t₂ : Trm) (T1 T2 : Typ) :
        (typing Γ t₁ (typ_arrow T1 T2)) → (typing Γ t₂ T1) → typing Γ (app t₁ t₂) T2

open typing
open valid_ctx
open lc

--Typing judgments only allow valid contexts.
lemma typing_valid_ctx  Γ e T : typing Γ e T → valid_ctx Γ := by
  intro H
  induction H
  case typ_var _ _ _ h _ =>
    exact h
  case typ_abs L φ t T1 _ _ f =>
    let ⟨p1, p2⟩ := pick_fresh t L
    simp at p2
    apply valid_remove_cons
    apply (f p1 p2.1)
  case typ_app _ _ _ _ _ _ _ h1 _ =>
    exact h1
------------------------------------

--Weakining Rule
lemma typing_weakening_strengthened' (Γ Δ Ψ' : context) (t : Trm) (T : Typ) :
    typing Ψ' t T → (Ψ : context) → Ψ' = Ψ ++ Γ
    → valid_ctx (Ψ ++ Δ ++ Γ)
    → typing (Ψ ++ Δ ++ Γ) t T := by
  intro H
  induction H
  case typ_var φ x T' _ fT' =>
    intro φ p f
    apply typ_var
    exact f
    rw [p] at fT'
    exact (binds_weaken _ _ _ _ _ fT' f)
  case typ_abs L φ' s T1 T2 _ fT2 =>
    intro φ p f
    apply typ_abs (L ∪ context_terms (φ ++ Δ ++ Γ))
    intro x hx
    simp at hx
    apply (fT2 x hx.1 ((x,T1) :: φ))
    simp [p]
    apply valid_cons
    exact f
    simp [append_cons]
    intro q
    exact (hx.2 ((context_terms_iff_in_list x _).mpr q))
  case typ_app φ' t1 t2 T1 T2 _ _ fT1 fT2 =>
    intro φ p f
    apply typ_app
    exact (fT1 φ p f)
    exact (fT2 φ p f)

lemma typing_weakening_strengthened (Γ Δ Ψ : context) (t : Trm) (T : Typ) :
    typing (Ψ ++ Γ) t T
    → valid_ctx (Ψ ++ Δ ++ Γ)
    → typing (Ψ ++ Δ ++ Γ) t T := by
  intro H p
  apply (typing_weakening_strengthened' _ _ (Ψ ++ Γ))
  exact H
  exact rfl
  exact p

lemma typing_weakening (Γ Δ : context) (t : Trm) (T : Typ) :
    typing (Γ) t T → valid_ctx (Δ ++ Γ)
    → typing (Δ ++ Γ) t T := by
  intro H p
  rw [← nil_append (Δ ++ Γ)] at p
  apply (typing_weakening_strengthened Γ Δ [])
  simp
  exact H
  exact p

lemma typing_weakening_head (Γ : context) (t : Trm) (T S : Typ) (x : ℕ):
    ¬ (in_context x Γ) → typing Γ t T
    → typing ((x , S) :: Γ) t T := by
  intro notxl typt
  rw [← nil_append ((x , S) :: Γ), append_cons, nil_append]
  apply typing_weakening _ _ _ _ typt
  apply valid_push
  apply (typing_valid_ctx _ _ _ typt)
  exact notxl

--Substitution Rule
lemma typing_subst_var_case Γ Δ u S T z x :
    binds x T (Δ ++ (z, S) :: Γ)
    → valid_ctx (Δ ++ (z, S) :: Γ)
    → typing Γ u S → typing (Δ ++ Γ) ([z // u] ($ x)) T := by
  intro b v t
  simp only [subst]
  by_cases hxz : x = z
  . simp [if_pos hxz]
    rw [← hxz] at b v
    have h : T = S := by
      apply (binds_mid_eq x T S Γ Δ)
      simp only [← append_cons]
      exact b
      simp only [← append_cons]
      exact v
    apply typing_weakening
    simp [h, t]
    apply (valid_remove_mid_cons x S Γ Δ v)
  . simp [if_neg hxz]
    apply typ_var
    apply (valid_remove_mid_cons z S Γ Δ v)
    apply binds_remove_mid_cons
    apply b
    push_neg at hxz
    exact hxz

lemma typing_regular (t : Trm) (T : Typ) (Γ : context) :
    typing Γ t T -> lc t := by
  intro H
  induction H
  case typ_var _ x _ _ _ =>
    exact (lc.lc_var x)
  case typ_abs L _ u _ _ _ h' =>
    apply (lc.lc_abs u L)
    intro x hx
    exact (h' x hx)
  case typ_app _ t1 t2 _ _ _ _ f1 f2 =>
    apply (lc.lc_app)
    exact f1
    exact f2

lemma typing_subst_strengthened' Γ Δ' t u S T z :
    typing Δ' t T → ((φ : context) → Δ' = (φ ++ (z, S) :: Γ)
    → typing (φ ++ (z, S) :: Γ) t T
    → typing Γ u S → typing (φ ++ Γ) ([z // u] t) T ) := by
  intro H
  induction H
  case typ_var ψ x X h h' =>
    intro φ p G f
    apply typing_subst_var_case
    rw [p] at h'
    exact h'
    rw [p] at h
    exact h
    exact f
  case typ_abs L ψ s S1 S2 h h' =>
    intro Δ p _ f
    simp only [subst]
    apply typ_abs (L ∪ context_terms (Δ ++ Γ) ∪ {z}) (Δ ++ Γ) ([z // u] s) S1 S2
    intro x hx
    rw [subst_open_var s u]
    simp at hx
    push_neg at hx
    rw [← nil_append ((x, S1) :: (Δ ++ Γ)), append_cons, nil_append, ← append_assoc]
    apply (h' x hx.1)
    simp [p]
    rw [append_assoc, ← p]
    simp [h x hx.1]
    exact f
    apply (typing_regular _ _ _ f)
    simp at hx
    push_neg at hx
    exact (fun w => hx.2.2 w.symm)
  case typ_app ψ t1 t2 S1 S2 h h' f1 f2 =>
    intro φ p _ f
    simp only [subst]
    apply typ_app
    apply (f1 φ p)
    simp [← p, h]
    exact f
    apply (f2 φ p)
    simp [← p, h']
    exact f

lemma typing_subst_strengthened Γ Δ t u S T z :
    typing (Δ ++ (z, S) :: Γ) t T →
    typing Γ u S →
    typing (Δ ++ Γ) ([z // u] t) T := by
  intro H p
  apply (typing_subst_strengthened')
  exact H
  rfl
  exact H
  exact p

lemma typing_subst Γ t u S T z :
    typing ((z, S) :: Γ) t T →
    typing Γ u S →
    typing Γ ([z // u] t) T := by
  intro H p
  rw [← nil_append ((z, S) :: Γ)] at H
  rw [← nil_append Γ]
  apply typing_subst_strengthened
  exact H
  exact p
--------------------------------------------

lemma typing_rename Γ x y t T1 T2 :
    x ∉ fv t →  ¬ (in_context x Γ)
    → y ∉ fv t →  ¬ (in_context y Γ)
    → typing ((x, T1) :: Γ) (open₀ t ($ x)) T2
    → typing ((y, T1) :: Γ) (open₀ t ($ y)) T2 := by
  intro hx fx _ fy R
  by_cases hxy : x = y
  . rwa [hxy] at R
  . have ok_ctx : valid_ctx Γ := by
      apply valid_remove_cons
      apply typing_valid_ctx
      exact R
    have p := subst_intro t ($ y) (lc_var y) x hx
    rw [p]
    apply typing_subst ((y, T1) :: Γ) (open₀ t ($ x)) ($ y) T1 T2
    have q : ((x, T1) :: (y, T1) :: Γ) = [(x, T1)] ++ [(y, T1)] ++ Γ := by
      simp
    rw [q]
    apply typing_weakening_strengthened
    simp [R]
    apply (valid_push _ _ _ (valid_push _ _ _ ok_ctx fy))
    simp
    push_neg
    exact ⟨hxy, fx⟩
    apply typ_var
    apply valid_push _ _ _ ok_ctx fy
    simp

lemma typing_abs_intro Γ x t T1 T2 :
    x ∉ fv t →  ¬ (in_context x Γ)
    → typing ((x, T1) :: Γ) (open₀ t ($ x)) T2
    → typing Γ (abs t) (T1 -> T2) := by
  intro hx fx R
  apply typ_abs (fv t ∪ context_terms Γ)
  intro y hy
  simp at hy
  apply (typing_rename _ _ _ _ _ _ hx fx)
  exact hy.1
  exact (fun q => hy.2 ((context_terms_iff_in_list _ _).mpr q))
  exact R

lemma preservation_beta_red E e T :
    typing E e T
    → ((e' : Trm) →  beta_red e e' → typing E e' T) := by
  intro H
  induction H
  case typ_var φ x S _ _ =>
    intro e' p
    cases p
  case typ_abs L φ t S1 S2 _ a_ih =>
    intro e' p
    cases p
    next t1' L' a' =>
      apply typ_abs (L' ∪ L)
      intro x hx
      simp at hx
      apply (a_ih x hx.2 (open₀ t1' ($ x)))
      apply (a' x hx.1)
  case typ_app φ t1 t2 S1 S2 f1 f2 h1 h2 =>
    intro e' p
    cases p
    next e1 lce1 g =>
      cases f1
      next L h =>
        let ⟨x, hx⟩ := pick_fresh e1 L
        have q : lc t2 := by
          apply (typing_regular _ _ _ f2)
        simp at hx
        rw [subst_intro e1 t2 q x hx.2]
        apply (typing_subst)
        exact (h x hx.1)
        exact f2
    next e1 eve1 lct2 =>
      apply typ_app
      apply (h1 e1 eve1)
      exact f2
    next e2 lct1 eve2 =>
      apply typ_app
      exact f1
      apply (h2 e2 eve2)

lemma preservation_multi_red E e T :
    typing E e T
    → ((e' : Trm) →  multi_red e e' → typing E e' T) := by
  intro H e' eme'
  induction eme'
  next _ =>
    exact H
  next t2 t3 _ t2bt3 ih =>
      apply (preservation_beta_red _ _ _ ih _ t2bt3)
