import Stlc.basics
import Stlc.open_close
import Stlc.context

open Typ
open Trm
open valid_ctx
open lc

/- # Different Forms of β-reductions -/

--full beta reduction
inductive beta_red : Trm → Trm → Prop
| br_beta : ∀ t1 t2, lc (abs t1) → lc t2 → beta_red (app (abs t1) t2) (open₀ t1 t2)
| br_app1 : ∀ t1 t1' t2, lc t2 → beta_red t1 t1' → beta_red (app t1 t2) (app t1' t2)
| br_app2 : ∀ t1 t2 t2', lc t1 → beta_red t2 t2' → beta_red (app t1 t2) (app t1 t2')
| br_abs : ∀ t1 t1' (L : Finset ℕ),
    (∀ x, x ∉ L → beta_red (open₀ t1 ($ x)) (open₀ t1' ($ x))) → beta_red (abs t1) (abs t1')

open beta_red

lemma beta_red_regular : ∀ t1 t2, (beta_red t1 t2) → (lc t1) ∧ (lc t2) := by
  intro t1 t2 t1rt2
  induction t1rt2
  case br_beta s1 s2 lcas1 lcs2 =>
    constructor
    exact (lc_app (abs s1) s2 lcas1 lcs2)
    exact (open_lc s1 s2 lcas1 lcs2)
  case br_app1 s1 s1' s2 lcs2 _ h =>
    exact ⟨lc_app s1 s2 h.1 lcs2, lc_app s1' s2 h.2 lcs2⟩
  case br_app2 s1 s2 s2' lcs1 _ h =>
    exact ⟨lc_app s1 s2 lcs1 h.1, lc_app s1 s2' lcs1 h.2⟩
  case br_abs s1 s1' L _ h =>
    constructor
    . apply (lc_abs s1 L (fun x hx => (h x hx).1))
    . apply (lc_abs s1' L (fun x hx => (h x hx).2))

lemma beta_rename t1 t2 x y : beta_red t1 t2
    → beta_red ([x // ($ y)] t1) ([x // ($ y)] t2) := by
  intro R
  induction R
  case br_beta s1 s2 lc1 lc2 =>
    rw [open₀]
    rw [subst_open_rec s1 s2 ($ y) x 0 (lc_var y)]
    rw [← open₀]
    apply br_beta
    . rw [← subst]
      apply subst_lc
      exact lc1
      exact (lc_var y)
    . apply subst_lc
      exact lc2
      exact (lc_var y)
  case br_app1 s1 s1' s2 lc2 bs1' h =>
    simp only [subst]
    apply br_app1
    apply subst_lc
    apply lc2
    apply (lc_var)
    exact h
  case br_app2 s1 s2 s2' lc1 bs2' h =>
    simp only [subst]
    apply br_app2
    apply subst_lc
    apply lc1
    apply (lc_var)
    exact h
  case br_abs s1 s1' L h f =>
    simp only [subst]
    apply br_abs _ _ (L ∪ {x})
    intro z hz
    simp at hz
    push_neg at hz
    simp [subst_open_var s1 ($ y) (lc_var y) x z hz.2.symm]
    simp [subst_open_var s1' ($ y) (lc_var y) x z hz.2.symm]
    exact (f z hz.1)

lemma beta_abs_intro t1 t2 x :
    beta_red (open₀ t1 ($ x)) (open₀ t2 ($ x))
    → x ∉ fv t1 → x ∉ fv t2 → beta_red (λ t1) (λ t2) := by
  intro R fx1 fx2
  apply br_abs t1 t2 ∅
  intro y _
  rw [subst_intro _ _ _ x fx1, subst_intro _ _ _ x fx2]
  apply beta_rename
  exact R
  exact (lc_var y)
  exact (lc_var y)

lemma beta_red_subst_out t1 t2 x u :
    (beta_red t1 t2) ∧ (lc u)
    → (beta_red ([x // u] t1) ([x // u] t2)) := by
  rintro ⟨t1bt2, lcu⟩
  induction t1bt2
  case br_beta s1 s2 lc1 lc2 =>
    simp only [subst]
    have q : ([x // u] open₀ s1 s2) = open₀ ([x // u] s1) ([x // u] s2) := by
      simp [open₀]
      apply subst_open_rec
      exact lcu
    rw [q]
    apply br_beta
    rw [← subst]
    apply subst_lc
    exact lc1
    exact lcu
    apply subst_lc
    exact lc2
    exact lcu
  case br_app1 s1 s1' s2 lc2 s1bs1' f =>
    simp only [subst]
    apply br_app1
    apply subst_lc
    exact lc2
    exact lcu
    exact f
  case br_app2 s1 s2 s2' lc1 s2bs2' f =>
    simp only [subst]
    apply br_app2
    apply subst_lc
    exact lc1
    exact lcu
    exact f
  case br_abs s1 s2 L f h =>
    simp only [subst]
    let ⟨y, hy⟩ := pick_fresh ([x // u] s1) (L ∪ (fv ([x // u] s2)) ∪ {x})
    apply beta_abs_intro _ _ y
    simp at hy
    push_neg at hy
    rw [subst_open_var _ _ lcu , subst_open_var _ _ lcu]
    apply (h y hy.1)
    exact (fun p => hy.2.2.1 p.symm)
    exact (fun p => hy.2.2.1 p.symm)
    simp at hy
    push_neg at hy
    exact hy.2.2.2
    simp at hy
    push_neg at hy
    exact hy.2.1

-------------------------

--paralel reduction
inductive para : Trm → Trm → Prop
| para_var : ∀ x, para ($ x) ($ x)
| para_red : ∀ t1 t1' t2 t2' (L : Finset ℕ),
    (∀ x, x ∉ L → para (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    para t2 t2' →
    para (app (abs t1) t2) (open₀ t1' t2')
| para_app : ∀ t1 t1' t2 t2', para t1 t1' → para t2 t2' → para (app t1 t2) (app t1' t2')
| para_abs : ∀ t1 t1' (L : Finset ℕ) ,
    (∀ x, x ∉ L → para (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    para (abs t1) (abs t1')

open para

lemma para_regular : ∀ t1 t2, (para t1 t2) → (lc t1) ∧ (lc t2) := by
  intro t1 t2 t1pt2
  induction t1pt2
  case para_var s =>
    exact ⟨lc_var s, lc_var s⟩
  case para_red s1 s1' s2 s2' L _ _ h h' =>
    constructor
    . apply (lc_app (abs s1) s2)
      exact (lc_abs s1 L (fun x hx => (h x hx).1))
      exact h'.1
    . apply (open_lc s1' s2')
      exact (lc_abs s1' L (fun x hx => (h x hx).2))
      exact h'.2
  case para_app s1 s1' s2 s2' _ _ h1 h2 =>
    exact ⟨lc_app s1 s2 h1.1 h2.1, lc_app s1' s2' h1.2 h2.2⟩
  case para_abs s1 s1' L _ h =>
    constructor
    . exact (lc_abs s1 L (fun x hx => (h x hx).1))
    . exact (lc_abs s1' L (fun x hx => (h x hx).2))

lemma lc_para_refl : ∀ t, lc t → para t t := by
  intro t lct
  induction lct
  case lc_var x =>
    exact (para_var x)
  case lc_abs u L _ h =>
    apply (para_abs u u L)
    exact h
  case lc_app u1 u2 _ _ h h' =>
    exact (para_app u1 u1 u2 u2 h h')

lemma para_subst_all t1 t2 s1 s2 :
    (para t1 t2) → (para s1 s2)
    → ∀ x, (para ([x // s1] t1) ([x // s2] t2)) := by
  intro t1pt2 s1ps2 x
  induction t1pt2
  case para_var y =>
    simp only [subst]
    by_cases hyx : y = x
    . simp only [if_pos hyx]
      exact s1ps2
    . simp only [if_neg hyx]
      exact (para_var y)
  case para_red u1 u1' u2 u2' L f u2pu2' g h =>
    simp only [subst]
    rw [open₀, (subst_open_rec u1' u2' s2 x 0 (para_regular _ _ s1ps2).2), ← open₀]
    apply para_red _ _ _ _ (L ∪ {x})
    intro y hy
    simp at hy
    push_neg at hy
    have p : x ≠ y := (fun q => (hy.2 q.symm))
    rw [subst_open_var u1 s1 (para_regular _ _ s1ps2).1 x y p]
    rw [subst_open_var u1' s2 (para_regular _ _ s1ps2).2 x y p]
    exact (g y hy.1)
    exact h
  case para_app u1 u1' u2 u2' u1pu1' u2pu2' f g =>
    simp only [subst]
    apply para_app
    exact f
    exact g
  case para_abs u1 u1' L f g =>
    simp only [subst] at g ⊢
    apply para_abs _ _ (L ∪ {x})
    intro y hy
    simp at hy
    push_neg at hy
    have p : x ≠ y := (fun q => (hy.2 q.symm))
    rw [subst_open_var _ _ _ x y p, subst_open_var _ _ _ x y p]
    exact (g y hy.1)
    exact (para_regular _ _ s1ps2).2
    exact (para_regular _ _ s1ps2).1

lemma para_open_out t t' u u' (L : Finset ℕ) :
    (∀ x, x ∉ L → para (open₀ t ($ x)) (open₀ u ($ x)))
    → para t' u' → para (open₀ t t') (open₀ u u') := by
  intro f tpu'
  let ⟨x, qx⟩ := pick_fresh t (L ∪ (fv u))
  simp at qx
  push_neg at qx
  rw [subst_intro t t' (para_regular _ _ tpu').1 x qx.2.2]
  rw [subst_intro u u' (para_regular _ _ tpu').2 x qx.2.1]
  apply para_subst_all
  exact (f x qx.1)
  exact tpu'

lemma opening_closing_para t u x y z :
    para t u → y ∉ ((fv t) ∪ (fv u) ∪ {x})
    → para (opening z ($ y) (closing z x t))
           (opening z ($ y) (closing z x u)) := by
  intro tpu hy
  simp at hy
  push_neg at hy
  rw [open_close_subst t x y (para_regular _ _ tpu).1 z]
  rw [open_close_subst u x y (para_regular _ _ tpu).2 z]
  apply para_subst_all _ _ _ _ tpu (para_var y)

lemma open_close_para t u x y :
    para t u → y ∉ ((fv t) ∪ (fv u) ∪ {x})
    → para (open₀ (close₀ t x) ($ y))
           (open₀ (close₀ u x) ($ y)) := opening_closing_para t u x y 0

lemma para_through t1 t2 u1 u2 x :
    (x ∉ fv t1 ∧ x ∉ fv t2)
    → (para (open₀ t1 ($ x)) (open₀ t2 ($ x)))
    → (para u1 u2) → (para (open₀ t1 u1) (open₀ t2 u2)) := by
  rintro ⟨h1, h2⟩ f g
  rw [subst_intro t1 u1 (para_regular _ _ g).1 x h1]
  rw [subst_intro t2 u2 (para_regular _ _ g).2 x h2]
  apply para_subst_all
  exact f
  exact g

---------------------------
--multiple-step reduction
inductive multi_red : Trm → Trm → Prop
| mr_refl : ∀ t, lc t → multi_red t t
| mr_head : ∀ t1 t2 t3, (multi_red t1 t2) → beta_red t2 t3 → multi_red t1 t3

open multi_red

lemma multi_red_trans t1 t2 t3 :
    (multi_red t1 t2) → (multi_red t2 t3) → (multi_red t1 t3) := by
  intro t1mlt2 t2mlt3
  induction t2mlt3
  case mr_refl _ =>
    exact t1mlt2
  case mr_head s1 s2 _ s2bs3 f =>
    apply mr_head
    . exact f
    . exact s2bs3

lemma multi_red_regular :
    ∀ t1 t2, (multi_red t1 t2) → (lc t1) ∧ (lc t2) := by
  intro t1 t2 t1mt2
  induction t1mt2
  case mr_refl s =>
    exact ⟨s, s⟩
  case mr_head s1 s2 _ s2bs3 h =>
    exact ⟨h.1, (beta_red_regular s1 s2 s2bs3).2⟩

lemma beta_to_multi_red :
    ∀ t1 t2, (beta_red t1 t2) → (multi_red t1 t2) := by
  intro t1 t2 t1rt2
  apply (mr_head t1 t1 t2)
  apply (mr_refl t1)
  exact (beta_red_regular t1 t2 t1rt2).1
  exact t1rt2

lemma multi_red_abs_intro' u1 u2 x :
    multi_red u1 u2
    → (∀ t1 t2, u1 = open₀ t1 ($ x) → u2 = open₀ t2 ($ x)
       → x ∉ fv t1 → x ∉ fv t2 → multi_red (λ t1) (λ t2)) := by
  intro u1mu2
  induction u1mu2
  case mr_refl t =>
    intro t1 t2 p1 p2 fx1 fx2
    rw [p1] at p2
    have q := open₀_injective _ _ _ fx1 fx2 p2
    rw [q]
    apply mr_refl
    apply lc_abs t2 ∅
    intro z _
    rw [subst_intro t2 ($ z) (lc_var z) x fx2]
    apply subst_lc
    rw [← q, ← p1]
    exact t
    exact (lc_var z)
  case mr_head s1 s2 _ s1bs2 f =>
    intro t1 t2 p1 p2 fx1 fx2
    apply mr_head _ (λ(close₀ s1 x)) _
    apply (f t1 (close₀ s1 x))
    exact p1
    rw [← (open_close_var x s1 (beta_red_regular _ _ s1bs2).1).symm]
    exact fx1
    simp [close₀, close_var_fv s1 x 0]
    apply (beta_abs_intro (close₀ s1 x) t2)
    rw [← p2]
    rw [← (open_close_var x s1 (beta_red_regular _ _ s1bs2).1).symm]
    exact s1bs2
    simp [close₀, close_var_fv s1 x 0]
    exact fx2

lemma multi_red_abs_intro t1 t2 x :
    multi_red (open₀ t1 ($ x)) (open₀ t2 ($ x))
    → x ∉ fv t1 → x ∉ fv t2 → multi_red (λ t1) (λ t2) := by
  intro R hx1 hx2
  apply (multi_red_abs_intro' (open₀ t1 ($ x)) (open₀ t2 ($ x)) x)
  exact R
  simp
  simp
  exact hx1
  exact hx2

lemma multi_red_abs t1 t2 (L : Finset ℕ):
    (∀ x, x ∉ L → multi_red (open₀ t1 ($ x)) (open₀ t2 ($ x)))
    → multi_red (λ t1) (λ t2) := by
  intro f
  let ⟨x, hx⟩ := pick_fresh t2 (L ∪ (fv t1))
  simp at hx
  push_neg at hx
  apply (multi_red_abs_intro t1 t2 x)
  apply (f x hx.1)
  exact hx.2.1
  exact hx.2.2

lemma multi_red_app1 t1 t1' t2 :
    (multi_red t1 t1') ∧ (lc t2)
    → (multi_red (app t1 t2) (app t1' t2)) := by
  rintro ⟨t1mt2, lct2⟩
  induction t1mt2
  case mr_refl t =>
    apply mr_refl
    apply lc_app
    exact t
    exact lct2
  case mr_head s1 s2 _ s1bs2 f =>
    apply mr_head _ (s1 @ t2) _
    exact f
    apply br_app1
    exact lct2
    exact s1bs2

lemma multi_red_app2 t1 t2 t2' :
    (multi_red t2 t2') ∧ (lc t1)
    → (multi_red (app t1 t2) (app t1 t2')) := by
  rintro ⟨t1mt2, lct1⟩
  induction t1mt2
  case mr_refl t =>
    apply mr_refl
    apply lc_app
    exact lct1
    exact t
  case mr_head s1 s2 _ s1bs2 f =>
    apply mr_head _ (t1 @ s1) _
    exact f
    apply br_app2
    exact lct1
    exact s1bs2

lemma multi_red_subst_in t x u1 u2 :
    (multi_red u1 u2) ∧ (lc t)
    → (multi_red ([x // u1] t) ([x // u2] t)) := by
  rintro ⟨u1mu2, lct⟩
  induction lct
  case lc_var i =>
    simp only [subst]
    by_cases hix : i = x
    . simp [if_pos hix]
      exact u1mu2
    . simp [if_neg hix]
      exact (mr_refl _ (lc_var i))
  case lc_abs u L h f =>
    simp [subst]
    apply multi_red_abs _ _ (L ∪ {x})
    intro y hy
    simp at hy
    push_neg at hy
    rw [subst_open_var u u1 (multi_red_regular _ _ u1mu2).1 x y]
    rw [subst_open_var u u2 (multi_red_regular _ _ u1mu2).2 x y]
    apply (f y hy.1)
    exact (fun s => hy.2 s.symm)
    exact (fun s => hy.2 s.symm)
  case lc_app s1 s2 lc1 lc2 h1 h2 =>
    simp [subst]
    apply multi_red_trans _ (([x // u2] s1) @ ([x // u1] s2)) _
    apply multi_red_app1
    constructor
    . apply h1
    . apply subst_lc
      exact lc2
      apply (multi_red_regular _ _ u1mu2).1
    apply multi_red_app2
    constructor
    . apply h2
    . apply subst_lc
      apply lc1
      apply (multi_red_regular _ _ u1mu2).2

lemma multi_red_subst_all t1 t2 x u1 u2 :
    (multi_red t1 t2) ∧ (multi_red u1 u2)
    → (multi_red ([x // u1] t1) ([x // u2] t2)) := by
  rintro ⟨t1mt2, u1mu2⟩
  induction t1mt2
  case mr_refl lct =>
    apply multi_red_subst_in
    exact ⟨u1mu2, lct⟩
  case mr_head s1 s2 _ s1bs2 f =>
     apply mr_head _ ([x // u2] s1) _
     exact f
     apply beta_red_subst_out
     exact ⟨s1bs2, (multi_red_regular _ _ u1mu2).2⟩

lemma multi_red_through t1 t2 u1 u2 x :
    (x ∉ fv t1 ∧ x ∉ fv t2) →
    (multi_red (open₀ t1 ($ x)) (open₀ t2 ($ x))) →
    (multi_red u1 u2) →
    (multi_red (open₀ t1 u1) (open₀ t2 u2)) := by
  rintro ⟨h1, h2⟩ f g
  rw [subst_intro t1 u1 (multi_red_regular _ _ g).1 x h1]
  rw [subst_intro t2 u2 (multi_red_regular _ _ g).2 x h2]
  apply multi_red_subst_all
  exact ⟨f, g⟩

------------------------

--multiple-step paralel reduction
inductive multi_para : Trm → Trm → Prop
| m_para_refl : ∀ t, lc t → multi_para t t
| m_para_head : ∀ t1 t2 t3, (multi_para t1 t2) → para t2 t3 → multi_para t1 t3

open multi_para

lemma multi_para_trans : ∀ t1 t2 t3,
    (multi_para t1 t2) → (multi_para t2 t3) → (multi_para t1 t3) := by
  intro t1 t2 t3 t1mpt2 t2mpt3
  induction t2mpt3
  case m_para_refl _ =>
   exact t1mpt2
  case m_para_head s1 s2 _ s1ps2 f =>
   apply (m_para_head t1 s1 s2)
   exact f
   exact s1ps2

lemma multi_para_regular : ∀ t1 t2, (multi_para t1 t2) → (lc t1) ∧ (lc t2) := by
  intro t1 t2 t1mpt2
  induction t1mpt2
  case m_para_refl lct =>
    exact ⟨lct, lct⟩
  case m_para_head s1 s2 _ s1ps2 h =>
    exact ⟨h.1, (para_regular s1 s2 s1ps2).2⟩

lemma para_to_multi_para : ∀ t1 t2, (para t1 t2) → (multi_para t1 t2) := by
  intro t1 t2 t1pt2
  induction t1pt2
  case para_var x =>
    exact (m_para_refl ($ x) (lc_var x))
  case para_red s1 s1' s2 s2' L f s2ps2' _ b =>
    apply (m_para_head _ ((abs s1) @ s2) (open₀ s1' s2'))
    . apply (m_para_refl ((abs s1) @ s2))
      apply lc_app
      apply lc_abs s1 L
      exact (fun x hx => (para_regular _ _ (f x hx)).1)
      exact (multi_para_regular _ _ b).1
    . apply (para_red s1 s1' s2 s2' L f s2ps2')
  case para_app s1 s1' s2 s2' s1ps1' s2ps2' _ _ =>
    apply m_para_head _ (s1 @ s2)
    . apply m_para_refl
      apply (lc_app _ _ (para_regular _ _ s1ps1').1 (para_regular _ _ s2ps2').1)
    . exact (para_app s1 s1' s2 s2' s1ps1' s2ps2')
  case para_abs s1 s1' L f _ =>
    apply (m_para_head _ (abs s1) (abs s1'))
    . apply (m_para_refl (abs s1))
      apply (lc_abs s1 L)
      intro x hx
      exact (para_regular _ _ (f x hx)).1
    . apply (para_abs s1 s1' L f)

------------------------


/- # Equivalence between multi-β reduction and multi-paralel reduction -/

lemma beta_red_to_para : ∀ t t', beta_red t t' → para t t' := by
  intro t t' trt'
  induction trt'
  case br_beta t1 t2 lcat1 lct2 =>
    apply (para_red t1 t1 t2 t2 ∅)
    simp
    intro x
    exact (lc_para_refl _ (open_var_lc x t1 lcat1))
    exact (lc_para_refl _ lct2)
  case br_app1 t1 t1' t2 lct2 _ h =>
    apply (para_app t1 t1' t2 t2)
    exact h
    exact (lc_para_refl _ lct2)
  case br_app2 t1 t2 t2' lct1 _ h =>
    apply (para_app t1 t1 t2 t2')
    exact (lc_para_refl _ lct1)
    exact h
  case br_abs t1 t1' L _ h =>
    apply (para_abs t1 t1' L)
    exact h

lemma multi_red_to_para : ∀ t t', multi_red t t' → multi_para t t' := by
  intro t t' tmrt'
  induction tmrt'
  case mr_refl lct =>
    exact (m_para_refl t lct)
  case mr_head t1 t2 _ t1rt2 t2pt3 =>
    apply m_para_head
    exact t2pt3
    exact (beta_red_to_para t1 t2 t1rt2)

lemma para_to_multi_red : ∀ t t', para t t' → multi_red t t' := by
  intro t t' tpt'
  induction tpt'
  case para_var x =>
    exact (mr_refl ($ x) (lc_var x))
  case para_red t1 t1' t2 t2' L f t2pt2' h h' =>
    apply (multi_red_trans ((abs t1) @ t2) (open₀ t1 t2) (open₀ t1' t2'))
    . apply (beta_to_multi_red ((abs t1) @ t2) (open₀ t1 t2))
      apply (br_beta t1 t2)
      have lcabst1 : lc (abs t1):= by
        apply (lc_abs t1 L)
        intro x hx
        have := f x hx
        exact (para_regular (open₀ t1 ($ x)) (open₀ t1' ($ x)) (f x hx)).1
      exact lcabst1
      exact (para_regular t2 t2' t2pt2').1
    . have  ⟨x, hx⟩ : ∃ x : ℕ, x ∉ (L ∪ (fv t1) ∪ (fv t1')) := by
        exact Infinite.exists_not_mem_finset (L ∪ (fv t1) ∪ (fv t1'))
      simp at hx
      push_neg at hx
      apply (multi_red_through t1 t1' t2 t2' x)
      constructor
      .  exact (hx.2).1
      .  exact (hx.2).2
      apply (h x (hx.1))
      exact h'
  case para_app t1 t1' t2 t2' t1pt1' t2pt2' h1 h2 =>
    apply (multi_red_trans (t1 @ t2) (t1' @ t2) (t1' @ t2'))
    . apply (multi_red_app1 t1 t1' t2)
      exact ⟨h1 , (para_regular t2 t2' t2pt2').1⟩
    . apply (multi_red_app2 t1' t2 t2')
      exact ⟨h2 , (para_regular t1 t1' t1pt1').2⟩
  case para_abs t1 t1' L _ h =>
    apply (multi_red_abs t1 t1' L h)

lemma multi_para_to_multi_red : ∀ t t', multi_para t t' → multi_red t t' := by
  intro t t' tmpt'
  induction tmpt'
  case m_para_refl lct =>
    exact (mr_refl t lct)
  case m_para_head t1 t2 _ t1pt2 t1mlt2 =>
    apply (multi_red_trans t t1 t2)
    exact t1mlt2
    exact (para_to_multi_red t1 t2 t1pt2)

lemma multi_red_iff_multi_para : ∀ t1 t2, (multi_red t1 t2) ↔ (multi_para t1 t2) := by
  intro t1 t2
  constructor
  . exact (multi_red_to_para t1 t2)
  . exact (multi_para_to_multi_red t1 t2)
