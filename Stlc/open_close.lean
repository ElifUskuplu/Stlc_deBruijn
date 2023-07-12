import Stlc.basics

namespace Trm

/- Variable opening turns some bound variables into free variables. 
It is used to investigate the body of an abstraction. 
Variable closing turns some free variables into bound variables. 
It is used to build an abstraction given a representation of its body. -/

@[simp]
def opening (x : ℕ) (a : Trm) : Trm → Trm
| bvar i => if x = i then a else (bvar i)
| fvar i => fvar i
| abs u => abs (opening (x + 1) a u)
| app u1 u2 => app (opening x a u1) (opening x a u2)

notation " {" x " ~> " a "} " u => opening x a u

--Opening at index zero
def open₀ u a := opening 0 a u 

lemma open_var_fv (t u: Trm) : (j : ℕ) → fv (opening j u t) ⊆ (fv t) ∪ (fv u) := by
  induction t
  case bvar i =>
    intro j
    simp [opening]
    by_cases h : j = i
    . rw [if_pos h, fv]
      simp
    . rw [if_neg h, fv]
      simp
  case fvar i => 
    simp [opening, fv]
  case abs s hs =>
    simp [opening, fv]
    exact (fun j => hs (j + 1))
  case app s1 s2 hs1 hs2 =>
    simp [opening, fv]
    intro j
    apply (@Finset.Subset.trans ℕ _ ((fv s1 ∪ fv u) ∪ (fv s2 ∪ fv u)) _)
    exact Finset.union_subset_union (hs1 j) (hs2 j)
    simp [Finset.union_assoc]
    refine Finset.union_subset_union_right ?_
    rw [Finset.union_comm]
    simp

lemma opening_lc_core (e a b : Trm) : (i j: ℕ) → i ≠ j → 
  ({j ~> a} e) = ({i ~> b} ({j ~> a} e)) → e = ({i ~> b} e) := by
  induction e
  case bvar y =>
   intro i j neqij h
   by_cases hiy : (i = y)
   . simp [opening, ← hiy] at h
     rw [hiy]
     rw [if_neg] at h
     rwa [hiy] at h
     exact (fun hij => neqij (symm hij))
   . simp [opening]
     rw [if_neg]
     exact hiy
  case fvar y =>
   intro i j _ _ 
   rfl
  case abs u hu =>
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
| abs u => abs (closing (k + 1) x u)
| app u1 u2 => app (closing k x u1) (closing k x u2)

notation " { " k " <~ " x " } " u => closing k x u

--Closing at index zero
def close₀ u a := closing 0 a u 

lemma close_var_fv (t : Trm) (x : ℕ) : (j : ℕ) → fv (closing j x t) = (fv t) \ {x} := by
  induction t
  case bvar _ =>
    simp [closing, fv]
  case fvar i =>
    intro j
    simp [closing, fv]
    by_cases hi : x = i
    . rw [if_pos hi, fv, hi]
      simp
    . rw [if_neg hi, fv]
      simp [hi]
  case abs u hu =>
    intro j
    simp [closing, fv]
    exact (hu (j + 1))
  case app u1 u2 hu1 hu2 =>
    intro j
    simp [closing, fv]
    simp [hu1 j, hu2 j]
    exact Eq.symm (Finset.union_sdiff_distrib (fv u1) (fv u2) {x})

----------------------------------------------------------------------
--Locally closed terms
inductive lc : Trm → Prop
| lc_var : ∀ x : ℕ, lc (fvar x)
| lc_abs : ∀ a : Trm, ∀ L : Finset ℕ, 
   (∀ x : ℕ, x ∉ L → lc (open₀ a ($ x))) → lc (abs a)
| lc_app : ∀ u1 u2 : Trm, lc u1 → lc u2 → lc (app u1 u2)

open lc

/-The predicate “body t” asserts that t describes 
the body of a locally closed abstraction.-/
def body t := ∃ (L : Finset ℕ), ∀ x, x ∉ L → lc (open₀ t ($ x)) 

lemma lc_abs_iff_body : ∀ t, lc (abs t) ↔ body t := by
  intro t
  constructor
  . intro h
    cases h 
    next L a =>
      use L
      exact a          
  . rintro ⟨L, h⟩ 
    exact (lc_abs t L h)
----------------------------------------------------------------------   
/-The following lemmas show that opening and closing 
are inverses of each other on variables.-/
--1) Close(Open)=Id
lemma close_open (x : ℕ) (t : Trm) : x ∉ fv t → (j : ℕ) → closing j x (opening j ($ x) t) = t := by
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
  case fvar i =>
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
    push_neg at hx
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
lemma open_close_core_fact (x y z : ℕ) (t : Trm) : x ≠ y → y ∉ fv t → 
    ((i j : ℕ) → i ≠ j → ({ i ~> ($ y)} ({j ~> ($ z)} ({j <~ x} t))) = 
       ({j ~> ($ z)} ({j <~ x} ({i ~> ($ y)} t))) ):= by
  intro neqxy hy
  induction t
  case bvar a =>
    intro i j neqij
    simp only [opening]
    by_cases hia : i = a
    . rw [if_pos hia]
      rw [if_neg]
      simp only [opening, closing]
      rw [if_pos hia, if_neg neqxy, opening]
      exact (fun p => neqij (by rw [← p] at hia; exact hia))
    . rw [if_neg hia]
      simp only [opening]
      by_cases hja : j = a
      . rw [if_pos hja]
        simp only [opening]
      . rw [if_neg hja]
        simp only [opening, ite_eq_right_iff]
        exact hia
  case fvar a =>
    intro i j _
    simp only [closing]
    by_cases hxa : x = a
    . rw [if_pos hxa]
      simp only [opening, ite_true, opening._eq_2]
    . rw [if_neg hxa]
      simp only [opening]
  case abs u hu =>
    simp only [ne_eq, opening, abs.injEq]
    rw [fv] at hy
    intro i j neqij
    apply (hu hy (i + 1) (j + 1))
    exact Iff.mpr Nat.succ_ne_succ neqij
  case app u1 u2 hu1 hu2 =>
    intro i j neqij
    simp only [opening, app.injEq]
    simp [fv] at hy
    push_neg at hy
    exact ⟨hu1 hy.1 i j neqij, hu2 hy.2 i j neqij⟩  

lemma open_close (x : ℕ) (t : Trm) : lc t → (j : ℕ) → opening j ($ x) (closing j x t) = t := by
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
  case lc_abs u L _ hu =>
    intro j
    simp [closing, opening]
    have z := pick_fresh u (L ∪ (fv ($ x)) ∪ (fv (( {j + 1 ~> $ x} { j + 1 <~ x } u))))
    rcases z with ⟨y, hy⟩
    simp at hy
    push_neg at hy
    apply (open₀_injective y ( {j + 1 ~> $ x} { j + 1 <~ x } u)  u (hy.2.2.1) (hy.2.2.2))
    rw [← (hu y (hy.1) (j + 1))]
    simp [open₀]
    apply (open_close_core_fact x y x u)
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
lemma opening_lc (e a : Trm) : lc e → (i : ℕ) → (e = {i ~> a} e) := by
  intro lce 
  induction lce
  case lc_var x =>
    intro _
    rfl
  case lc_abs u L _ hu =>
    intro i
    simp [open₀] at hu
    rw [opening]
    have  ⟨x, hx⟩ : ∃ x : ℕ, x ∉ L := by
      exact Infinite.exists_not_mem_finset L
    have t : u = { i + 1 ~> a } u := by
      apply (opening_lc_core u ($ x) a (i + 1) 0)
      exact Nat.succ_ne_zero i
      exact (hu x hx (i + 1))
    rw [← t] 
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro i
    simp [opening]
    exact ⟨hu1 i, hu2 i⟩  

lemma open₀_lc (e a : Trm) : lc e → (e = open₀ e a) := by
  intro lce
  simp [open₀]
  apply (opening_lc e a lce 0) 

--Free variable substitution distributes over index substitution.
lemma subst_open_rec (e1 e2 a : Trm) : (i j : ℕ) → lc a →
   ([i // a] ({j ~> e2} e1)) = ({j ~> [i // a] e2} ([i // a] e1)) := by
  induction e1
  case bvar y =>
   intro i j _
   by_cases hjy : (j = y)
   . simp [opening]
     rw [if_pos, if_pos] <;> exact hjy
   . simp [opening]
     rw [if_neg, if_neg, subst]
     <;> exact hjy 
  case fvar y =>
   intro i j lca
   by_cases hyi : (y = i)
   . simp [opening, subst]
     rw [if_pos]
     exact (opening_lc a ([ i // a ] e2) lca j)
     exact hyi
   . simp [opening, subst]
     rw [if_neg]
     exact (opening_lc ($ y) ([ i // a ] e2) (lc.lc_var y) j)
     exact hyi
  case abs u hu =>
   intro i j lca
   simp [opening, subst]
   exact (hu i (j + 1) lca)
  case app u1 u2 hu1 hu2 =>
   intro i j lca
   simp [opening, subst]
   exact ⟨hu1 i j lca, hu2 i j lca ⟩ 

--The lemma above is most often used with k = 0 and e2 as some fresh variable. 
--Therefore, it simplifies matters to define the following useful corollary.
lemma subst_open_var (e a : Trm) : lc a → (i j : ℕ) → i ≠ j →
    (open₀ ([i // a] e) ($ j)) = ([i // a] (open₀ e ($ j))) := by
  intro lca i j neqij
  simp [open₀]
  rw [subst_open_rec e ($ j) a i 0 lca]
  rw [subst, if_neg]
  exact (fun p => neqij (Eq.symm p))


--When we open a term, we can instead open the term with a fresh variable and 
--then substitute for that variable.
lemma subst_intro (e a : Trm) : lc a → (i : ℕ) → i ∉ (fv e) → 
    (open₀ e a) = ([i // a] (open₀ e ($ i))) := by
  intro lca i hi
  simp [open₀]
  rw [subst_open_rec e ($ i) a i 0 lca]
  rw [subst, if_pos]
  rw [subst_fresh]
  exact hi
  rfl

lemma subst_lc (e a : Trm) : (x : ℕ) → lc e → lc a → lc ([x // a] e) := by
  intro x lce lca
  induction lce
  case lc_var y =>
    rw [subst]
    by_cases hxy : y = x
    . rw [if_pos]
      exact lca
      exact hxy
    . rw [if_neg]
      exact (lc_var y)
      exact hxy
  case lc_abs u L _ hu =>
    apply (lc_abs ([ x // a ] u) (L ∪ {x}))
    intro x₀ hx₀
    have t1 : x₀ ∉ L := by
      intro s
      exact (hx₀ (Finset.mem_union_left {x} s))
    have t2 : x₀ ≠ x := by
      simp at hx₀
      push_neg at hx₀
      exact hx₀.2
    rw [subst_open_var u a lca x x₀ t2.symm]
    exact (hu x₀ t1)  
  case lc_app u1 u2 lcu1 lcu2 hu1 hu2 =>
    dsimp [subst]
    apply (lc_app ( [ x // a ] u1) ( [ x // a ] u2) hu1 hu2)

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

lemma open_var_lc : ∀ x t, lc (abs t) → lc (open₀ t ($ x)) := by
  intro x t lcat
  rw [lc_abs_iff_body t] at lcat
  exact (open_var_body x t lcat)

lemma open_body : ∀ t u, body t → lc u → lc (open₀ t u) := by
  intro t u bt lcu
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ : ∃ y : ℕ, y ∉ (L ∪ (fv t)) := by
      exact Infinite.exists_not_mem_finset (L ∪ (fv t))
  simp at hy
  push_neg at hy
  rw [subst_intro t u lcu y hy.2]
  exact (subst_lc (open₀ t ($ y)) u y (a y hy.1) lcu)

--general version of open_var_lc
lemma open_lc : ∀ t u, lc (abs t) → lc u → lc (open₀ t u) := by
  intro t u lcat lcu
  rw [lc_abs_iff_body t] at lcat
  exact (open_body t u lcat lcu)

