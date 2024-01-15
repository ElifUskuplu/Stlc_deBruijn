import Stlc.basics
import Stlc.open_close
import Stlc.context
import Stlc.typing
import Stlc.reductions

open Typ
open Trm
open valid_ctx
open typing
open lc
open beta_red
open para
open multi_red
open multi_para

lemma para_diamond t t1 :
    para t t1 → ∀ t2, para t t2
    → ∃ t', (para t1 t') ∧ (para t2 t') := by
  intro tpt1
  induction tpt1
  case para_var x =>
    intro t2 tpt2
    use t2
    exact ⟨tpt2, lc_para_refl t2 (para_regular _ _ tpt2).2⟩
  case para_red s1 s1' s2 s2' L _ s2ps2' ih1 ih2 =>
    intro t2 tpt2
    cases tpt2
    case para_red u1' u2' L' f' s2pu2' =>
      let ⟨x, qx⟩ := pick_fresh u2' (L ∪ L' ∪ (fv u1') ∪ (fv s1') ∪ (fv s2'))
      simp at qx
      push_neg at qx
      rw [subst_intro u1' u2' (para_regular _ _ s2pu2').2 x qx.2.2.1]
      rw [subst_intro s1' s2' (para_regular _ _ s2ps2').2 x qx.2.2.2.1]
      have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
        apply ih2 _ s2pu2'
      have fact2 : ∃ t', para (open₀ s1' ($ x)) t' ∧ para (open₀ u1' ($ x)) t' := by
        apply ih1 _ qx.1 _ (f' _ qx.2.1)
      rcases fact1 with ⟨t', qt'⟩
      rcases fact2 with ⟨t'', qt''⟩
      use ([x // t'] t'')
      constructor
      apply para_subst_all _ _ _ _ qt''.1 qt'.1
      apply para_subst_all _ _ _ _ qt''.2 qt'.2
    case para_app u2 u2' s1pu2 s2pu2' =>
      cases s1pu2
      next s1'' L' f' =>
        let ⟨x, qx⟩ := pick_fresh s1' (L ∪ L' ∪ (fv s1''))
        simp at qx
        push_neg at qx
        have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
          apply ih2 _ s2pu2'
        have fact2 : ∃ t', para (open₀ s1' ($ x)) t' ∧ para (open₀ s1'' ($ x)) t' := by
          apply ih1 _ qx.1 _ (f' _ qx.2.1)
        rcases fact1 with ⟨t', qt'⟩
        rcases fact2 with ⟨t'', qt''⟩
        use (open₀ (close₀ t'' x) t')
        constructor
        . apply para_through _ _ _ _ x ⟨qx.2.2.2, by simp [close₀, (close_var_fv t'' x 0)]⟩
          rw [open_close_var _ _ (para_regular _ _ qt''.1).2]
          exact qt''.1
          exact qt'.1
        . apply para_red _ _ _ _ (fv (open₀ s1'' ($ x)) ∪ fv t'' ∪ {x})
          intro y qy
          rw [← close_open_var x s1'' qx.2.2.1]
          apply open_close_para _ _ _ _ qt''.2 qy
          exact qt'.2
  case para_app s1 s1' s2 s2' s1ps1' _ ih1 ih2 =>
      intro t2 tpt2
      cases tpt2
      case para_red t1' u1' u2' L f s2pu2' =>
        cases s1ps1'
        next s1'' L' f' =>
          let ⟨x, qx⟩ := pick_fresh u1' (L ∪ L' ∪ (fv s1''))
          simp at qx
          push_neg at qx
          have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
            apply ih2 _ s2pu2'
          have fact2 : ∃ t', para (λ s1'') t' ∧ para (λ u1') t' := by
            apply ih1 (λ u1') (para_abs _ _ L f)
          rcases fact1 with ⟨t', qt'⟩
          rcases fact2 with ⟨t'', qt''⟩
          cases qt''.1
          next w1 L'' f'' =>
            cases qt''.2
            next L''' f''' =>
              use (open₀ w1 t')
              constructor
              . apply para_red _ _ _ _ L'' f'' qt'.1
              . apply para_open_out _ _ _ _ L''' f''' qt'.2
      case para_app u1 u2' s1pu1 s2pu2' =>
        have fact1: ∃ t', para s1' t' ∧ para u1 t' := by
          apply ih1 _ s1pu1
        have fact2: ∃ t', para s2' t' ∧ para u2' t' := by
          apply ih2 _ s2pu2'
        rcases fact1 with ⟨t', qt'⟩
        rcases fact2 with ⟨t'', qt''⟩
        use (t' @ t'')
        constructor
        . apply para_app _ _ _ _ qt'.1 qt''.1
        . apply para_app _ _ _ _ qt'.2 qt''.2
  case para_abs s1 s2' L _ ih =>
    intro t2 tpt2
    cases tpt2
    next t2' L' f' =>
      let ⟨x, qx⟩ := pick_fresh s2' (L ∪ L' ∪ (fv t2'))
      simp at qx
      push_neg at qx
      have fact1 := ih x qx.1 _ (f' x qx.2.1)
      rcases fact1 with ⟨t', qt'⟩
      use (λ (close₀ t' x))
      constructor
      . apply para_abs _ _ (fv (open₀ s2' ($ x)) ∪ fv t' ∪ {x})
        intro y qy
        rw [← close_open_var x s2' qx.2.2.2]
        apply open_close_para _ _ _ _ qt'.1 qy
      . apply para_abs _ _ (fv (open₀ t2' ($ x)) ∪ fv t' ∪ {x})
        intro y qy
        rw [← close_open_var x t2' qx.2.2.1]
        apply open_close_para _ _ _ _ qt'.2 qy

lemma multi_para_diamond_core t t1 t2 :
    (para t t1) ∧ (multi_para t t2)
    → ∃ t', (multi_para t1 t') ∧ (para t2 t') := by
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
    have q := (para_diamond _ _ s1ps2 _ h2)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩
    use t''
    constructor
    exact (m_para_head _ _ _ h1 h4)
    exact h3

lemma multi_para_diamond t t1 t2 :
    (multi_para t t1) ∧ (multi_para t t2)
    → ∃ t', (multi_para t1 t') ∧ (multi_para t2 t') := by
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
    ∀ t t1 t2, (multi_red t t1) ∧ (multi_red t t2)
    → ∃ t', (multi_red t1 t') ∧ (multi_red t2 t') := by
  intro t t1 t2 ⟨trt1 , trt2⟩
  simp [multi_red_iff_multi_para] at trt1 trt2 ⊢
  exact (multi_para_diamond t t1 t2 ⟨trt1 , trt2⟩)
