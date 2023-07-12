import Stlc.basics
import Stlc.open_close
import Stlc.context
import Stlc.typing
import Stlc.reductions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

open Typ
open Trm
open valid_ctx
open typing
open lc
open beta_red
open para
open multi_red
open multi_para

lemma para_diamond t t1 t2 :
    (para t t1) ∧ (para t t2) → 
    ∃ t', (para t1 t') ∧ (para t2 t') := by
  intro ⟨tpt1, tpt2⟩
  cases tpt1
  case para_var x =>
    use t2
    exact ⟨tpt2, lc_para_refl t2 (para_regular _ _ tpt2).2⟩
  case para_red s1 s1' s2 s2' L f s2ps2' =>
    cases tpt2
    case para_red u1' u2' L' f' s2pu2' => 
      have q := pick_fresh u2' (L ∪ L' ∪ (fv u1') ∪ (fv s1') ∪ (fv s2'))
      rcases q with ⟨x, qx⟩
      simp at qx
      push_neg at qx
      rw [subst_intro u1' u2' (para_regular _ _ s2pu2').2 x qx.2.2.1]
      rw [subst_intro s1' s2' (para_regular _ _ s2ps2').2 x qx.2.2.2.1]
      have fact1 := (para_diamond s2 s2' u2' ⟨s2ps2', s2pu2'⟩)
      have fact2 := (para_diamond _ _ _ ⟨(f x qx.1) , (f' x qx.2.1)⟩)
      rcases fact1 with ⟨t', ⟨qs2', qu2'⟩⟩
      rcases fact2 with ⟨t'', ⟨qs1', qu1'⟩⟩  
      use [x // t'] t''
      constructor
      exact (para_subst (open₀ s1' ($ x)) t'' s2' t' qs1' qs2' x)
      exact (para_subst (open₀ u1' ($ x)) t'' u2' t' qu1' qu2' x)    
    case para_app u2 u2' s1pu2 s2pu2' =>
      cases s1pu2
      next u1' L' f' =>
        have q := pick_fresh u1' (L ∪ L' ∪ (fv u2') ∪ (fv s1') ∪ (fv s2'))
        rcases q with ⟨x, qx⟩
        simp at qx
        push_neg at qx
        rw [subst_intro s1' s2' (para_regular _ _ s2ps2').2 x qx.2.2.2.1]
        have fact1 := (para_diamond s2 s2' u2' ⟨s2ps2', s2pu2'⟩)        
        have fact2 := (para_diamond _ _ _ ⟨(f x qx.1) , (f' x qx.2.1)⟩)
        rcases fact1 with ⟨t', ⟨qs2', qu2'⟩⟩
        rcases fact2 with ⟨t'', ⟨qs1', qu1'⟩⟩  
        use [x // t'] t''
        constructor
        exact (para_subst (open₀ s1' ($ x)) t'' s2' t' qs1' qs2' x)
        sorry
  case para_app s1 s1' s2 s2' s1ps1' s2ps2' =>
    cases tpt2
    next u1 u1' u2' L f s2pu2' =>
      sorry
    next u1' u2' s1pu1' s2pu2' =>
      have fact1 := (para_diamond s2 s2' u2' ⟨s2ps2', s2pu2'⟩)
      have fact2 := (para_diamond s1 s1' u1' ⟨s1ps1', s1pu1'⟩)
      rcases fact1 with ⟨t', ⟨qs2', qu2'⟩⟩
      rcases fact2 with ⟨t'', ⟨qs1', qu1'⟩⟩
      use t'' @ t'
      constructor
      exact (para_app _ _ _ _ qs1' qs2')
      exact (para_app _ _ _ _ qu1' qu2')
  case para_abs s1 s2' L f =>
    sorry

lemma multi_para_diamond_core t t1 t2 : (para t t1) ∧ (multi_para t t2) → ∃ t', (multi_para t1 t') ∧ (para t2 t') := by
  intro ⟨tpt1, tmt2⟩
  induction tmt2
  case m_para_refl _ => 
    use t1
    constructor
    apply m_para_refl
    exact (para_regular _ _ tpt1).2
    exact tpt1
  case m_para_head s1 s2 _ s1ps2 h =>
    rcases h with ⟨t' , ⟨h1, h2⟩⟩
    have q := (para_diamond _ _ _ ⟨s1ps2 , h2⟩)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩
    use t''
    constructor
    exact (m_para_head _ _ _ h1 h4)
    exact h3  
  
lemma multi_para_diamond t t1 t2 : (multi_para t t1) ∧ (multi_para t t2) → ∃ t', (multi_para t1 t') ∧ (multi_para t2 t') := by
  intro ⟨tmpt1 , tmpt2⟩
  induction tmpt1
  case m_para_refl _ =>
    use t2
    exact ⟨tmpt2, m_para_refl t2 (multi_para_regular _ _ tmpt2).2⟩
  case m_para_head s1 s2 _ s1ps2 f =>
    rcases f with ⟨t', ⟨h1,h2⟩⟩
    have q := (multi_para_diamond_core _ _ _ ⟨s1ps2, h1⟩)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩ 
    use t''
    constructor
    exact h3
    exact (m_para_head _ _ _ h2 h4)

theorem beta_red_confluence : 
    ∀ t t1 t2, (multi_red t t1) ∧ (multi_red t t2) → 
    ∃ t', (multi_red t1 t') ∧ (multi_red t2 t') := by
  intro t t1 t2 ⟨trt1 , trt2⟩
  simp [multi_red_iff_multi_para] at trt1 trt2 ⊢
  exact (multi_para_diamond t t1 t2 ⟨trt1 , trt2⟩)
