import Stlc.basics

namespace Trm

/- Variable opening turns some bound variables into free variables.
It is used to investigate the body of an abstraction.
Variable closing turns some free variables into bound variables.
It is used to build an abstraction given a representation of its body. -/

@[simp]
def opening (k : ℕ) (u : Trm) : Trm → Trm
| bvar i => if k = i then u else (bvar i)
| fvar x => fvar x
| abs T t => abs T (opening (k + 1) u t)
| app t1 t2 => app (opening k u t1) (opening k u t2)

notation " {" k " ~> " u "} " t => opening k u t

--Opening at index zero
def open₀ t u := opening 0 u t

lemma open_var_fv (t u: Trm) :
    (k : ℕ) → fv (opening k u t) ⊆ (fv t) ∪ (fv u) := by
  induction t
  case bvar i =>
    intro k
    simp [opening]
    by_cases h : k = i
    . rw [if_pos h, fv]
      simp
    . rw [if_neg h, fv]
      simp
  case fvar x =>
    simp [opening, fv]
  case abs T t ht =>
    simp [opening, fv]
    exact (fun k => ht (k + 1))
  case app t1 t2 ht1 ht2 =>
    simp [opening, fv]
    intro k
    apply (@Finset.Subset.trans ℕ _ ((fv t1 ∪ fv u) ∪ (fv t2 ∪ fv u)) _)
    exact Finset.union_subset_union (ht1 k) (ht2 k)
    simp [Finset.union_assoc]
    refine Finset.union_subset_union_right ?_
    rw [Finset.union_comm]
    simp

lemma opening_lc_lemma (t u v : Trm) :
    (i j: ℕ) → i ≠ j
    → ({j ~> u} t) = ({i ~> v} ({j ~> u} t))
    → t = ({i ~> v} t) := by
  induction t
  case bvar k =>
   intro i j neqij h
   by_cases hik : (i = k)
   . simp [opening, ← hik] at h
     rw [hik]
     rw [if_neg] at h
     rwa [hik] at h
     exact (fun hij => neqij (symm hij))
   . simp [opening]
     rw [if_neg]
     exact hik
  case fvar y =>
   intro i j _ _
   rfl
  case abs T u hu =>
   intro i j neqij h
   simp [opening] at h
   simp [opening]
   exact ((hu (i + 1) (j + 1) (Iff.mpr Nat.succ_ne_succ neqij)) h)
  case app u1 u2 hu1 hu2 =>
   intro i j neqij h
   simp [opening] at h
   simp [opening]
   constructor
   exact (hu1 i j neqij h.1)
   exact (hu2 i j neqij h.2)

----------------------------------------------------------------------
@[simp]
def closing (k x : ℕ) : Trm → Trm
| bvar i => bvar i
| fvar i => if x = i then (bvar k) else (fvar i)
| abs T t => abs T (closing (k + 1) x t)
| app t1 t2 => app (closing k x t1) (closing k x t2)

notation " { " k " <~ " x " } " t => closing k x t

--Closing at index zero
def close₀ u x := closing 0 x u

lemma close_var_fv (t : Trm) (x : ℕ) :
    (k : ℕ) → fv (closing k x t) = (fv t) \ {x} := by
  induction t
  case bvar _ =>
    simp [closing, fv]
  case fvar y =>
    intro k
    simp [closing, fv]
    by_cases hy : x = y
    . rw [if_pos hy, fv, hy]
      simp
    . rw [if_neg hy, fv]
      simp [hy]
  case abs T u hu =>
    intro k
    simp [closing, fv]
    exact (hu (k + 1))
  case app u1 u2 hu1 hu2 =>
    intro k
    simp [closing, fv]
    simp [hu1 k, hu2 k]
    exact Eq.symm (Finset.union_sdiff_distrib (fv u1) (fv u2) {x})

----------------------------------------------------------------------
--Locally closed terms
inductive lc : Trm → Prop
| lc_var : ∀ x : ℕ, lc (fvar x)
| lc_abs : ∀ t : Trm, ∀ T : Typ, ∀ L : Finset ℕ,
   (∀ x : ℕ, x ∉ L → lc (open₀ t ($ x))) → lc (abs T t)
| lc_app : ∀ t1 t2 : Trm, lc t1 → lc t2 → lc (app t1 t2)

open lc

/-The predicate “body t” asserts that t describes
the body of a locally closed abstraction.-/
def body t := ∃ (L : Finset ℕ), ∀ x, x ∉ L → lc (open₀ t ($ x))

lemma lc_abs_iff_body : ∀ t T, lc (abs T t) ↔ body t := by
  intro t T
  constructor
  . intro h
    cases h
    next L a =>
      use L
  . rintro ⟨L, h⟩
    exact (lc_abs t T L h)
----------------------------------------------------------------------
/-The following lemmas show that opening and closing
are inverses of each other on variables.-/
--1) Close(Open)=Id
lemma close_open (x : ℕ) (t : Trm) :
    x ∉ fv t → (k : ℕ) → closing k x (opening k ($ x) t) = t := by
  intro hx
  induction t
  case bvar i =>
    intro j
    simp [opening, closing]
    by_cases hi : j = i
    . rw [if_pos]
      simp only [closing, ite_true, bvar.injEq, hi]
      exact hi
    . rw [if_neg]
      simp only [closing]
      exact hi
  case fvar y =>
    simp [opening, closing]
    simp [fv] at hx
    exact hx
  case abs u hu =>
    simp [opening, closing] at hu ⊢
    rw [fv] at hx
    exact (fun p => hu hx (p + 1))
  case app u1 u2 hu1 hu2 =>
    simp [opening, closing]
    simp [fv] at hx
    exact (fun p => ⟨hu1 hx.1 p, hu2 hx.2 p⟩)

--special case of close_open at j=0
lemma close_open_var (x : ℕ) (t : Trm) :
    x ∉ fv t → close₀ (open₀ t ($ x)) x = t := fun hx => close_open x t hx 0

--Using this fact, we can show open₀ is injective on terms.
lemma open₀_injective (x : ℕ) (t1 t2 : Trm) :
    x ∉ fv t1 → x ∉ fv t2 → open₀ t1 ($ x) = open₀ t2 ($ x) → t1 = t2 := by
  intro hx1 hx2 eq
  rw [← close_open_var x t1 hx1]
  rw [← close_open_var x t2 hx2]
  rw [eq]

----------------------------------------------------------------------
--2) Open(Close)=Id
--First, we need a lemma.
lemma open_close_lemma (x y z : ℕ) (t : Trm) : x ≠ y → y ∉ fv t
    → ((i j : ℕ) → i ≠ j → ({ i ~> ($ y)} ({j ~> ($ z)} ({j <~ x} t)))
      = ({j ~> ($ z)} ({j <~ x} ({i ~> ($ y)} t))) ):= by
  intro neqxy hy
  induction t
  case bvar k =>
    intro i j neqij
    simp only [opening]
    by_cases hik : i = k
    . simp only [closing, opening]
      rw [if_pos hik]
      rw [if_neg]
      simp only [opening, closing]
      rw [if_pos hik, if_neg neqxy, opening]
      exact (fun p => neqij (by rw [← p] at hik; exact hik))
    . rw [if_neg hik]
      simp [opening]
      by_cases hjk : j = k
      . rw [if_pos hjk]
        simp only [opening]
      . rw [if_neg hjk]
        simp only [opening, ite_eq_right_iff]
        intro ik
        simp
        exact (hik ik)
  case fvar a =>
    intro i j _
    simp only [closing]
    by_cases hxa : x = a
    . simp only [opening, closing]
      rw [if_pos hxa]
      simp only [opening, ite_true]
    . simp only [opening, closing]
      rw [if_neg hxa]
      simp only [opening]
  case abs T u hu =>
    simp only [ne_eq, opening, abs.injEq]
    rw [fv] at hy
    intro i j neqij
    simp only [closing, opening, abs.injEq]
    constructor
    simp only
    apply (hu hy (i + 1) (j + 1))
    exact Iff.mpr Nat.succ_ne_succ neqij
  case app u1 u2 hu1 hu2 =>
    intro i j neqij
    simp only [closing, opening, app.injEq]
    simp [fv] at hy
    exact ⟨hu1 hy.1 i j neqij, hu2 hy.2 i j neqij⟩

lemma open_close (x : ℕ) (t : Trm) :
    lc t → (k : ℕ) → opening k ($ x) (closing k x t) = t := by
  intro lct
  induction lct
  case lc_var y =>
    intro j
    simp [closing]
    by_cases hxy : x = y
    . rw [if_pos, hxy]
      simp [closing]
      exact hxy
    . rw [if_neg]
      simp [closing]
      exact hxy
  case lc_abs u T L _ hu =>
    intro j
    simp [closing, opening]
    let ⟨y, hy⟩ := pick_fresh u (L ∪ (fv ($ x)) ∪ (fv (( {j + 1 ~> $ x} { j + 1 <~ x } u))))
    simp at hy
    apply (open₀_injective y ( {j + 1 ~> $ x} { j + 1 <~ x } u)  u (hy.2.2.1) (hy.2.2.2))
    rw [← (hu y (hy.1) (j + 1))]
    simp [open₀]
    apply (open_close_lemma x y x u)
    have hyx := hy.2.1
    simp [fv] at hyx
    exact (fun p => hyx p.symm)
    exact hy.2.2.2
    exact (Nat.succ_ne_zero j).symm
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro j
    simp [opening, closing]
    exact ⟨hu1 j, hu2 j⟩

--special case of open_close at j=0
lemma open_close_var (x : ℕ) (t : Trm) :
    lc t → open₀ (close₀ t x) ($ x) = t := by
  intro lct
  exact (open_close x t lct 0)

--Using this fact, we can show closing is injective on terms.
lemma closing_injective (x i : ℕ) (t1 t2 : Trm) :
    lc t1 → lc t2 → closing i x t1 = closing i x t2 → t1 = t2 := by
  intro lct1 lct2 eq
  rw [← open_close x t1 lct1 i]
  rw [← open_close x t2 lct2 i]
  rw [eq]

-----------------------------------------
--Auxilary lemma about opening
lemma opening_lc (t u : Trm) : lc t → (k : ℕ) → (t = {k ~> u} t) := by
  intro lce
  induction lce
  case lc_var x =>
    intro _
    rfl
  case lc_abs v T L _ hv =>
    intro i
    simp [open₀] at hv
    rw [opening]
    have  ⟨x, hx⟩ : ∃ x : ℕ, x ∉ L := by
      exact Infinite.exists_not_mem_finset L
    have h : v = { i + 1 ~> u } v := by
      apply (opening_lc_lemma v ($ x) u (i + 1) 0)
      exact Nat.succ_ne_zero i
      exact (hv x hx (i + 1))
    rw [← h]
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro i
    simp [opening]
    exact ⟨hu1 i, hu2 i⟩

lemma open₀_lc (t u : Trm) : lc t → (t = open₀ t u) := by
  intro lce
  simp [open₀]
  apply (opening_lc t u lce 0)

--Free variable substitution distributes over index substitution.
lemma subst_open_rec (t1 t2 u : Trm) : (i j : ℕ) → lc u
    → ([i // u] ({j ~> t2} t1)) = ({j ~> [i // u] t2} ([i // u] t1)) := by
  induction t1
  case bvar k =>
   intro i j _
   by_cases hjk : (j = k)
   . simp [opening]
     rw [if_pos, if_pos] <;> exact hjk
   . simp [opening]
     rw [if_neg, if_neg, subst]
     <;> exact hjk
  case fvar y =>
   intro i j lcu
   by_cases hyi : (y = i)
   . simp [opening, subst]
     rw [if_pos]
     exact (opening_lc u ([ i // u ] t2) lcu j)
     exact hyi
   . simp [opening, subst]
     rw [if_neg]
     exact (opening_lc ($ y) ([ i // u ] t2) (lc.lc_var y) j)
     exact hyi
  case abs T v hv =>
   intro i j lcu
   simp [opening, subst]
   exact (hv i (j + 1) lcu)
  case app u1 u2 hu1 hu2 =>
   intro i j lcu
   simp [opening, subst]
   exact ⟨hu1 i j lcu, hu2 i j lcu⟩

--The lemma above is most often used with k = 0 and e2 as some fresh variable.
--Therefore, it simplifies matters to define the following useful corollary.
lemma subst_open_var (t u : Trm) : lc u → (i j : ℕ) → i ≠ j
    → (open₀ ([i // u] t) ($ j)) = ([i // u] (open₀ t ($ j))) := by
  intro lcu i j neqij
  simp [open₀]
  rw [subst_open_rec t ($ j) u i 0 lcu]
  rw [subst, if_neg]
  exact (fun p => neqij (Eq.symm p))


--When we open a term, we can instead open the term with a fresh variable and
--then substitute for that variable.
lemma subst_intro (t u : Trm) : lc u → (x : ℕ) → x ∉ (fv t)
    → (open₀ t u) = ([x // u] (open₀ t ($ x))) := by
  intro lcu x hx
  simp [open₀]
  rw [subst_open_rec t ($ x) u x 0 lcu]
  rw [subst, if_pos]
  rw [subst_fresh]
  exact hx
  rfl

lemma subst_lc (t u : Trm) : (x : ℕ) → lc t → lc u → lc ([x // u] t) := by
  intro x lct lcu
  induction lct
  case lc_var y =>
    rw [subst]
    by_cases hxy : y = x
    . rw [if_pos]
      exact lcu
      exact hxy
    . rw [if_neg]
      exact (lc_var y)
      exact hxy
  case lc_abs v T L _ hv =>
    apply (lc_abs ([ x // u ] v) T (L ∪ {x}))
    intro x₀ hx₀
    have t1 : x₀ ∉ L := by
      intro s
      exact (hx₀ (Finset.mem_union_left {x} s))
    have t2 : x₀ ≠ x := by
      simp at hx₀
      push_neg at hx₀
      exact hx₀.2
    rw [subst_open_var v u lcu x x₀ t2.symm]
    exact (hv x₀ t1)
  case lc_app t1 t2 lct1 lct2 ht1 ht2 =>
    dsimp [subst]
    apply (lc_app ( [ x // u ] t1) ( [ x // u ] t2) ht1 ht2)

lemma open_var_body : ∀ x t, body t → lc (open₀ t ($ x)) := by
  intro x t bt
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ : ∃ y : ℕ, y ∉ (L ∪ {x} ∪ (fv t)) := by
      exact Infinite.exists_not_mem_finset (L ∪ {x} ∪ (fv t))
  simp at hy
  push_neg at hy
  rw [subst_intro t ($ x) (lc_var x) y (hy.2.2)]
  apply (subst_lc (open₀ t ($ y)) ($ x))
  exact (a y hy.1)
  exact (lc_var x)

lemma open_var_lc : ∀ x t, lc (abs T t) → lc (open₀ t ($ x)) := by
  intro x t lcat
  rw [lc_abs_iff_body t] at lcat
  exact (open_var_body x t lcat)

lemma open_body : ∀ t u, body t → lc u → lc (open₀ t u) := by
  intro t u bt lcu
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ : ∃ y : ℕ, y ∉ (L ∪ (fv t)) := by
      exact Infinite.exists_not_mem_finset (L ∪ (fv t))
  simp at hy
  rw [subst_intro t u lcu y hy.2]
  exact (subst_lc (open₀ t ($ y)) u y (a y hy.1) lcu)

--general version of open_var_lc
lemma open_lc : ∀ t u, lc (abs T t) → lc u → lc (open₀ t u) := by
  intro t u lcat lcu
  rw [lc_abs_iff_body t] at lcat
  exact (open_body t u lcat lcu)

lemma open_close_subst t x y :
    lc t → (∀ k, (opening k ($ y) (closing k x t)) = ([x // ($ y)] t)) := by
  intro lct
  induction lct
  case lc_var y =>
    simp only [closing, subst]
    by_cases hxy : x = y
    . simp [if_pos hxy, if_pos hxy.symm]
    . have hyx : y ≠ x := (fun p => (hxy p.symm))
      simp [if_neg hxy, if_neg hyx]
  case lc_abs s T L f h =>
    simp [opening, subst, abs.injEq]
    intro k
    let ⟨w, qw⟩ := pick_fresh s (L ∪ {x} ∪ (fv ( {k + 1 ~> $ y} { k + 1 <~ x } s)) ∪ (fv ([x // $ y] s)))
    simp at qw
    push_neg at qw
    have hwx : x ≠ w := (fun p => (qw.2.1 p.symm))
    have fact := h w qw.1 (k + 1)
    rw [← subst_open_var _ _ (lc_var y) _ _ hwx, open₀] at fact
    rw [← open_close_lemma _ _ _ _ hwx, ← open₀] at fact
    apply open₀_injective w _
    exact qw.2.2.1
    exact qw.2.2.2.1
    exact fact
    exact qw.2.2.2.2
    exact Nat.ne_of_beq_eq_false rfl
  case lc_app u1 u2 _ _ f1 f2 =>
    intro k
    simp
    exact ⟨f1 k, f2 k⟩
