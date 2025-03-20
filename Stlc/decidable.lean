import Stlc.normalization

open Typ
open Trm
open List
open typing
open valid_ctx
open lc

theorem typing_unique :
    ∀ t, lc t → ∀ Γ T1 T2,
    typing Γ t T1 → typing Γ t T2 → T1 = T2 := by
  intro t lct
  induction lct
  case lc_var x =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next _ bnd =>
      cases ty2
      next _ bnd' =>
        simp [binds] at bnd bnd'
        rw [bnd] at bnd'
        simp at bnd'
        exact bnd'
  case lc_abs u T L a ih =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next L1 U1 h1 =>
      cases ty2
      next L2 U2 h2 =>
        have ⟨x,hx⟩ := pick_fresh u (L ∪ L1 ∪ L2)
        simp at hx ⊢
        apply ih x hx.1 ((x,T) :: Γ) U1 U2 (h1 x hx.2.1) (h2 x hx.2.2.1)
  case lc_app t1 t2 lct1 lct2 ih1 ih2 =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next S1 sy1 sy2 =>
      cases ty2
      next U1 uy1 uy2 =>
        have this := ih1 _ _ _ sy2 uy2
        have this2 := ih2 _ _ _ sy1 uy1
        simp [this2] at this
        exact this

theorem typing_decidable :
    ∀ t Γ, lc t → valid_ctx Γ →
    (∃ T, typing Γ t T) ∨ ¬ (∃ T, typing Γ t T) := by
  intro t Γ lct vld
  induction lct generalizing Γ
  case lc_var x =>
    match h : (get x Γ) with
    | some T =>
        left
        use T
        apply typ_var Γ x T vld h
    | none =>
        right
        rintro ⟨T, typ⟩
        cases typ
        next _ ih =>
          simp [h] at ih
  case lc_abs u T L a ih =>
    have ⟨x,hx⟩ := pick_fresh u (L ∪ context_terms Γ)
    simp at hx
    cases H : (ih x hx.1 ((x,T) :: Γ)
        (valid_push Γ x T vld (not_context_terms_to_not_in_context _ _ hx.2.1)))
    next pos =>
      rcases pos with ⟨S, p⟩
      left
      use (T -> S)
      apply (typ_abs (fv u ∪ context_terms Γ) Γ)
      intro y hy
      simp at hy
      apply typing_rename _ _ _ _ _ _
              hx.2.2 (not_context_terms_to_not_in_context _ _ hx.2.1)
              hy.1 ((not_context_terms_to_not_in_context _ _ hy.2)) p
    next neg =>
      right
      rintro ⟨S,p⟩
      cases p
      next L' S' h =>
        have ⟨z,hz⟩ := pick_fresh u (L' ∪ context_terms Γ)
        simp at hz
        apply neg
        use S'
        apply typing_rename _ _ _ _ _ _
                hz.2.2 ((not_context_terms_to_not_in_context _ _ hz.2.1))
                hx.2.2 ((not_context_terms_to_not_in_context _ _ hx.2.1)) (h z hz.1)
  case lc_app t1 t2 lc1 lc2 ih1 ih2 =>
    cases (ih1 Γ vld)
    next pos =>
      rcases pos with ⟨T,p1⟩
      cases (ih2 Γ vld)
      next pos2 =>
        rcases pos2 with ⟨S,p2⟩
        match T with
        | typ_base =>
          right
          rintro ⟨T, P⟩
          cases P
          next S ty1 ty2 =>
            have q:= typing_unique _ lc1 _ _ _ p1 ty2
            simp at (q)
        | typ_arrow S1 S2 =>
          by_cases h : S1 = S
          . left
            use S2
            rw [← h] at p2
            apply typ_app Γ t1 t2 S1 S2 p1 p2
          . right
            rintro ⟨U, P⟩
            cases P
            next V ty1 ty2 =>
              have q := typing_unique _ lc1 _ _ _ p1 ty2
              simp at q
              have q' := typing_unique _ lc2 _ _ _ p2 ty1
              rw [← q'] at q
              apply (h q.1)
      next neg2 =>
        right
        rintro ⟨T, P⟩
        cases P
        next T1 ty1 ty2 =>
          apply neg2 ⟨_ , ty1⟩
    next neg =>
      right
      rintro ⟨T, P⟩
      cases P
      next T1 ty1 ty2 =>
        apply neg ⟨_ , ty2⟩

theorem typechecking_decidable t T Γ :
    lc t → valid_ctx Γ → (typing Γ t T) ∨ ¬(typing Γ t T) := by
  intro lct vld
  have this := typing_decidable t Γ lct vld
  cases this
  next pos =>
    rcases pos with ⟨S, P⟩
    by_cases h : S = T
    . rw [h] at P
      exact (Or.inl P)
    . right
      intro Q
      have q := typing_unique _ lct _ _ _ P Q
      exact h q
  next neg =>
    right
    simp at neg
    exact neg T
