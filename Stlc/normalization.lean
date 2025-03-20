import Stlc.basics
import Stlc.context
import Stlc.typing
import Stlc.reductions
import Stlc.confluence
import Stlc.multi_subst

open Typ
open Trm
open lc
open typing

namespace Trm

--a term is reducible if it reducts
def reducible (t : Trm) : Prop := ∃ t', beta_red t t'

--a term is normal if it is not reducible
def normal (t : Trm) : Prop := ¬ (reducible t)

--a term is normal iff it has no multi-step reduct
lemma normal_has_no_proper_multi_red (t : Trm) :
    normal t → ∀ t', multi_red t t' → t = t' := by
  intro nt t' tmt'
  induction tmt'
  case mr_refl _ =>
    rfl
  case mr_head t2 t3 tmt2 t2bt3 ih =>
    by_contra p
    rw [ih] at nt
    apply nt
    exact ⟨t3, t2bt3⟩

-- a term is normalizable if it has a normal multi-step reduct
def normalizable (t : Trm) : Prop := ∃ t', ((multi_red t t') ∧ (normal t'))

-- a term t is strongly normalizable if any one-step reduction sequence
--starting with t must terminate
def strongly_normalizable (t : Trm) : Prop :=
  ∀ (f : Nat → Trm), (((f 0 = t) ∧ (∀ n, (beta_red (f n) (f (Nat.succ n))))) → False)

--the following is an inductive version of being strongly normalizable
inductive SN : Trm → Prop
  | sn : (∀ t', (beta_red t t') → SN t') → SN t

--Both are logically equivalent
lemma strongly_normalizable_iff_SN t :
    strongly_normalizable t ↔ SN t := by
  constructor
  . contrapose
    intro notsnt
    have this : ∀ u , ¬ SN u → ∃ t', beta_red u t' ∧ ¬ SN t' := by
      intro u notsnu
      by_contra F
      push_neg at F
      apply notsnu (SN.sn F)
    choose f w hw using this
    let f' : Nat → {u // ¬ SN u} := fun n =>
      Nat.iterate (fun (x : {u // ¬ SN u}) => ⟨f x.1 x.2, hw x.1 x.2⟩) n ⟨t, notsnt⟩
    let f'' := (fun n => (f' n).1)
    intro G
    apply G f''
    constructor
    . rfl
    . intro n
      have rel := w (f' n).1 (f' n).2
      have eq1 : ((f' n).1) = (f'' n) := by rw []
      have eq2 : (f (f' n).1 (f' n).2) = (f'' (n + 1)) := by
        simp [f'', f', Function.iterate_succ_apply']
      simp [← eq1, ← eq2, rel]
  . intro snt
    induction snt
    case sn t' _ ih =>
      rintro f ⟨p , F⟩
      let f' : ℕ → Trm := fun n => Nat.rec (f 1) (fun n _ => f (Nat.succ (Nat.succ n))) n
      apply ih (f 1) (by rw [← p]; exact (F 0)) f'
      constructor
      . rfl
      . intro n
        induction n
        case zero =>
          exact (F 1)
        case succ n _ =>
          exact (F (Nat.succ (Nat.succ n)))

--one-step reduction preserves being strongly normalizable
lemma beta_red_preserves_SN (t : Trm) : SN t → ∀ t', beta_red t t' → SN t' := by
  intro snt
  cases snt
  next F =>
    exact F

--multi-step reduction preserves being strongly normalizable
lemma multi_red_preserves_SN (t t' : Trm) : SN t → multi_red t t' → SN t' := by
  intro snt tmt'
  induction tmt'
  case mr_refl _ =>
    exact snt
  case mr_head t2 t3 _ t2bt3 ih =>
    exact (beta_red_preserves_SN _ ih _ t2bt3)

--for a locally closed term s, if applying s to t is strongly normalizing,
--then t is strongly normalizing
lemma SN_app1 t s : lc s → SN (t @ s) → SN t := by
  intro lcs sn2ts
  generalize h : (t @ s) = t' at sn2ts
  induction sn2ts generalizing t with
  | sn F IH =>
    subst h
    apply SN.sn
    intro t' tbt'
    apply IH (t' @ s) (beta_red.br_app1 t t' s lcs tbt') _ rfl

-- If a term has two normal reducts, they must be the same
lemma normal_is_unique (t : Trm) :
    ∀ t1 t2, ((multi_red t t1) ∧ (normal t1)) ∧ ((multi_red t t2) ∧ (normal t2))
    → t1 = t2 := by
  intro t1 t2
  rintro ⟨⟨tmt1, n1⟩ , ⟨tmt2, n2⟩⟩
  have this : ∃ t3, multi_red t1 t3 ∧ multi_red t2 t3 := by
    exact (beta_red_confluence t t1 t2 ⟨tmt1, tmt2⟩)
  rcases this with ⟨t3, ⟨t1mt3, t2mt3⟩⟩
  rw [normal_has_no_proper_multi_red t1 n1 t3 t1mt3]
  rw [normal_has_no_proper_multi_red t2 n2 t3 t2mt3]

-- Definition of strongly computable terms by Jeremy Avigad.
-- This construction is also known as logical relations.
-- The definition is valid for locally closed terms.
@[simp]
def SC : Typ → Set Trm
  | typ_base => {t | (lc t) ∧ SN t}
  | typ_arrow t1 t2 =>
    {t | (lc t) ∧ (∀ u, ((lc u) ∧ (u ∈ SC t1)) → (t @ u) ∈ SC t2)}

-- By definition, strongly computable terms are locally closed.
lemma SC_regular A t : t ∈ (SC A) → lc t := by
  intro H
  induction A
  case typ_base =>
    exact H.1
  case typ_arrow t1 t2 _ _ =>
    exact H.1

-- A term is neutral if it is not an abstraction.
@[simp]
def neutral : Trm → Prop
| bvar _ => true
| fvar _ => true
| abs _ _ => false
| app _ _ => true

-- CR2 says that if t is strongly computable, then any multi-step reduct of t
-- is also strongly computable.
theorem CR2 : ∀ A t, (∀ t', t ∈ SC A → multi_red t t' → t' ∈ SC A) := by
  intro A
  induction A
  case typ_base =>
    intro t t' sct tmt'
    exact ⟨(multi_red_regular _ _ tmt').2, (multi_red_preserves_SN _ _ sct.2 tmt')⟩
  case typ_arrow A1 A2 _ ih2 =>
    intro t t' sct tmt'
    constructor
    . apply (multi_red_regular _ _ tmt').2
    . intro u H
      have this1 : (t @ u) ∈ SC (A2) := (sct.2 u H)
      apply ih2 (t @ u) (t' @ u) this1 (multi_red_app1 _ _ _ ⟨tmt', H.1⟩)

-- CR1 says that strongly computable terms are strongly normalizing.
-- CR3 says that if a locally closed term t is neutral, also any
-- one-step reduct of t is strongly computable, then t is strongly computable.
theorem CR_1_3 : ∀ A t,
    (t ∈ SC A → SN t) ∧ --CR1
    (lc t → neutral t → (∀ t', beta_red t t' → t' ∈ SC A) → t ∈ SC A) := by --CR3
  intro A
  induction A
  case typ_base =>
    intro t
    constructor
    . exact (fun sct => sct.2) --CR1 base case
    . exact (fun lct _ F => ⟨lct, SN.sn (fun s tbs => (F s tbs).2)⟩) --CR3 base case
  case typ_arrow A1 A2 ih1 ih2 =>
    intro t
    constructor
    . rintro ⟨_, H⟩ --CR1 arrow case
      let ⟨x, p2⟩ := pick_fresh t ∅
      simp at p2
      have this2 : ($ x) ∈ SC A1 := by
        apply (ih1 ($ x)).2 (lc_var x) (by simp)
        intro t' nbt
        cases nbt
      have this3 : (app t ($ x)) ∈ SC A2 := H ($ x) ⟨lc_var x , this2⟩
      have this4 : SN (app t ($ x)) := (ih2 (app t ($ x))).1 this3
      apply (SN_app1 _ _ (lc_var x) this4)
    . intro lct nt F --CR3 arrow case
      constructor
      . exact lct
      . intro u Hu
        have this1 : SN u := (ih1 _).1 Hu.2
        induction this1
        case sn u _ ihu =>
        apply (ih2 (t @ u)).2 (lc_app _ _ lct Hu.1) (by simp)
        intro t' tubt'
        cases tubt'
        next a _ _ =>
          simp [neutral] at nt
        next a tba lcu =>
          have this2 : a ∈ SC (A1 -> A2) := (F a tba)
          apply (this2.2 u Hu)
        next c lct ubc =>
          apply ihu c ubc
          constructor
          . apply (beta_red_regular _ _ ubc).2
          . apply CR2 _ _ _ Hu.2 (beta_to_multi_red _ _ ubc)

def CR1 A t := (CR_1_3 A t).1

def CR3 A t := (CR_1_3 A t).2

-- Free variables are always strongly computable.
lemma SC_var A x : ($ x) ∈ SC A := by
  induction A
  case typ_base =>
    constructor
    . apply lc_var x
    . apply SN.sn
      intro t tbx
      cases tbx
  case typ_arrow A1 A2 _ _ =>
    apply CR3 _ _ (lc_var x) (by simp)
    intro t' bred
    cases bred

-- Criteria for strongly computable lambda terms:
-- Suppose for all variable x not occured in t and strongly computable u, we have
-- [x//u]tˣ is strongly computable. Then λt is strongly computable.
theorem SC_lambda A1 A2 t : lc (λA1, t)
    → (∀ u x, x ∉ fv t → u ∈ SC A1 → ([x // u] (open₀ t ($ x))) ∈ SC A2)
    → (λ A1, t) ∈ SC (A1 -> A2) := by
  intro lct F
  have this : (∃ y, (open₀ t ($ y)) ∈ SC A2) := by
    let ⟨y, hy⟩ := pick_fresh t ∅
    simp at hy
    have this : ($ y) ∈ SC A1 := SC_var A1 y
    have this2 : (open₀ t ($ y)) ∈ SC A2 := by
      rw [subst_intro t ($ y) (lc_var y) y hy]
      exact (F ($ y) y hy this)
    exact ⟨y, this2⟩
  rcases this with ⟨y, hy⟩
  constructor
  . exact lct
  . intro u Hu
    have snu := CR1 _ _ Hu.2
    have snt := CR1 _ _ hy
    generalize h : (open₀ t ($ y)) = w at snt
    induction snt generalizing t with
    | sn _ iht' =>
      rw [← h] at iht'
      induction snu
      case sn u _ ihu =>
        apply CR3 _ _ (lc_app _ _ lct Hu.1) (by simp)
        intro t'' bred
        cases bred
        next lct' lcu =>
          let ⟨z, hz⟩ := pick_fresh t {0}
          simp at hz
          push_neg at hz
          rw [subst_intro _ _ Hu.1 z hz.2]
          apply (F u z hz.2 Hu.2)
        next t1' t'bt1' lcu =>
          cases t'bt1'
          next t'' L a =>
            let ⟨x, hx⟩ := pick_fresh t (L ∪ (fv t''))
            simp at hx
            have this3 : beta_red (open₀ t ($ y)) (open₀ t'' ($ y)) := by
              rw [subst_intro t ($ y) (lc_var y) x hx.2.2]
              rw [subst_intro t'' ($ y) (lc_var y) x hx.2.1]
              apply beta_rename _ _ _ _ (a x hx.1)
            apply (iht' (open₀ t'' ($ y)) this3 t''
                (beta_red_regular _ _ (beta_red.br_abs _ _ _ _ a)).2)
            intro u z hz scu
            rw [← subst_intro t'' u (SC_regular _ _ scu) z hz]
            have this4 : open₀ t u ∈ SC A2 := by
              rw [subst_intro t u (SC_regular _ _ scu) x hx.2.2]
              apply F u x hx.2.2 scu
            apply CR2 _ _ _ this4
            apply beta_to_multi_red
            rw [subst_intro t'' u (SC_regular _ _ scu) x hx.2.1]
            rw [subst_intro t u (SC_regular _ _ scu) x hx.2.2]
            apply beta_red_subst_out _ _ _ _ ⟨a x hx.1, (SC_regular _ _ scu)⟩
            apply CR2 _ _ _ hy (beta_to_multi_red _ _ this3)
            rfl
        next u1' lct' ubu1 =>
          apply ihu u1' ubu1
          have this5 := (beta_red_regular _ _ ubu1).2
          exact ⟨this5, CR2 _ _ _ Hu.2 (beta_to_multi_red _ _ ubu1)⟩
          intro t1 bred t2 typ2 F2 op2 q2
          apply CR2
          apply iht' t1 bred _ typ2 F2 op2 q2
          apply (beta_to_multi_red _ _ (beta_red.br_app2 _ _ _ (typ2) ubu1))

-- We can generalize the previous theorem:
-- Suppose for all strongly computable u, the opened term tᵘ is strongly computable.
-- Then λt is strongly computable.
theorem SC_lambda_term A1 A2 t : lc (λ A1,t)
    → (∀ u, u ∈ SC A1 → (open₀ t u) ∈ SC A2)
    → (λ A1, t) ∈ SC (A1 -> A2) := by
  intro lct F
  apply SC_lambda _ _ _ lct
  intro u x fvx scu
  rw [← subst_intro _ _ (SC_regular _ _ scu) x fvx]
  apply F u scu

-- Fundamental lemma about logical relations:
-- Suppose (x1:A1, x2:A2, ..., xn:An) ⊢ t : A. Then for any strongly computable ui:Ai,
-- we have ([x1//u1, x2//u2, ..., xn//un] t) is strongly computable.
lemma SC_subst t A : typing Γ t A
    → (f : (context_terms Γ) → Trm)
    → (∀ x (h : x ∈ (context_terms Γ)), (f ⟨x, h⟩) ∈ SC (context_type Γ ⟨x, h⟩))
    → (multi_subst (context_terms Γ) f t) ∈ SC A := by
  intro typt
  induction typt
  case typ_var Δ y T vld bnd =>
    intro f Hf
    simp only [multi_subst]
    by_cases h : y ∈ context_terms Δ
    . simp [h, ← context_type_eq_bind Δ ⟨y, h⟩ T vld bnd]
      apply (Hf y h)
    . simp [h]
      apply SC_var
  case typ_abs L Δ u T1 T2 a ih =>
    intro f Hf
    apply SC_lambda_term
    rw [← multi_subst]
    apply multi_subst_lc _ _ (typing_regular _ _ _ (typ_abs L Δ u T1 T2 a))
    exact (fun x hx => (SC_regular _ _ (Hf x hx)))
    intros u1 scu1
    let ⟨x, hx⟩ := pick_fresh u L
    simp at hx
    have this : (∀ y (s : y ∈ (context_terms ((x, T1) :: Δ))),
        ((add_term Δ f u1 x T1) ⟨y, s⟩) ∈ SC (context_type ((x, T1) :: Δ) ⟨y, s⟩)) := by
      intro y s
      by_cases p : y = x
      . simp [p, scu1]
      . simp [p] at s ⊢
        apply Hf y s
    have this2 := ih x hx.1 (add_term Δ f u1 x T1) this
    rw [multi_subst_open_lemma_2] at this2
    exact this2
    apply (SC_regular _ _ scu1)
    apply hx.2
    exact (fun y s => (SC_regular _ _ (Hf y s)))
  case typ_app Δ t1 t2 T1 T2 _ typt2 ih1 ih2 =>
    intro f Hf
    cases (ih1 f Hf)
    next L R =>
      apply R (multi_subst (context_terms Δ) f t2)
      constructor
      . apply multi_subst_lc
        apply (typing_regular _ _ _ typt2)
        exact (fun x hx => (SC_regular _ _ (Hf x hx)))
      . apply (ih2 f Hf)

-- Final theorem:
-- By CR1 and substitution lemma, we have every typeable term is strongly normalizing.
theorem strong_normalization t T : typing [] t T → SN t := by
  intro typt
  apply CR1 T t
  let ⟨x, hx⟩ := pick_fresh t ∅
  simp at hx
  let f : context_terms [(x, T)] → Trm := fun _ => ($ x)
  have this : multi_subst (context_terms [(x, T)]) f t = t := by
    rw [multi_subst_at_singleton]
    rw [subst_fresh _ _ _ hx]
  rw [← this]
  apply SC_subst
  apply typing_weakening [] [(x, T)] _ _ typt
  apply valid_push _ _ _ (valid_ctx.valid_nil) (by simp)
  exact (fun y hy => SC_var _ _)
