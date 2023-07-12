import Stlc.basics
import Stlc.open_close
import Stlc.context
import Stlc.typing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

open Typ
open Trm
open valid_ctx
open typing
open lc

inductive value : Trm → Prop
| value_abs : ∀ e, lc (abs e) → value (abs e)

open value

lemma value_regular (t : Trm) : value t → lc t := by
  intro valt
  induction valt
  case value_abs _ lcu =>
    exact lcu

--call by value
inductive eval : Trm → Trm → Prop
| eval_beta : ∀ e1 e2, lc (abs e1) → value e2 → eval (app (abs e1) e2) (open₀ e1 e2)
| eval_app1 : ∀ e1 e1' e2, lc e2 → eval e1 e1' → eval (app e1 e2) (app e1' e2)
| eval_app2 : ∀ e1 e2 e2', lc e1 → eval e2 e2' → eval (app e1 e2) (app e1 e2')

open eval

lemma eval_regular (e1 e2 : Trm) : eval e1 e2 → lc e1 ∧ lc e2  := by
  intro ev12
  induction ev12
  case eval_beta u1 u2 lc1 v2 =>
    constructor
    . apply lc_app
      exact lc1
      exact (value_regular _ v2)
    . apply open_lc
      exact lc1
      exact (value_regular _ v2)
  case eval_app1 u1 u1' u2 lc2 _ f =>
    constructor
    . apply lc_app
      exact f.1
      exact lc2
    . apply lc_app
      exact f.2
      exact lc2
  case eval_app2 u1 u2 u2' lc1 _ f =>
    constructor
    . apply lc_app
      exact lc1
      exact f.1
    . apply lc_app
      exact lc1
      exact f.2

notation t1 " cbv-> " t2 => (eval t1 t2) 

lemma preservation E e T : typing E e T → ((e' : Trm) →  eval e e' → typing E e' T) := by
  intro H
  induction H
  case typ_var φ x S _ _ =>
    intro e' p
    cases p
  case typ_abs _ φ t S1 S2 _ _ =>
    intro e' p
    cases p
  case typ_app φ t1 t2 S1 S2 f1 f2 h1 h2 =>
    intro e' p
    cases p
    next e1 lce1 g =>
      cases f1
      next L h =>
        simp only
        have w := pick_fresh e1 L
        rcases w with ⟨x, hx⟩
        have q : lc t2 := by
          apply (typing_regular _ _ _ f2)
        simp at hx
        push_neg at hx
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
      
lemma progress e T : typing [] e T → (value e) ∨ (∃ e', eval e e') := by
  intro H
  generalize p : [] = Γ at H
  induction H
  case typ_var Γ x S _ bx =>
    simp [p.symm] at bx
  case typ_abs L Δ s S1 S2 f _ =>
    left
    apply value_abs
    apply lc_abs s L 
    intro x hx
    exact (typing_regular _ _ _ (f x hx))
  case typ_app Δ s1 s2 S1 S2 f g h1 h2 =>
    right
    simp [p] at h1
    simp [p] at h2
    by_cases val1 : value s1
    . by_cases val2 : value s2
      . cases val1
        next s3 lcs3 =>
          use (open₀ s3 s2)
          apply eval_beta
          exact lcs3
          exact val2
      . simp [val2] at h2
        rcases h2 with ⟨s3 , hs3⟩  
        use (s1 @ s3)
        apply eval_app2
        exact (value_regular _ val1)
        exact hs3
    . simp [val1] at h1
      rcases h1 with ⟨s3 , hs3⟩  
      use (s3 @ s2)
      apply eval_app1
      exact (typing_regular _ _ _ g)
      exact hs3
