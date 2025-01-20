import Stlc.basics

/-
In order to make typing judgments, we need the notion of context.
The definition is designed to talk about "(x : T)"-like assumptions.
-/
open List

notation "context" => List (ℕ × Typ)

@[simp]
def context_terms : context → (Finset ℕ)
| [] => ∅
| ((x, _) :: Γ') => {x} ∪ (context_terms Γ')

@[simp]
def in_context (a : ℕ) : context → Prop
| [] => False
| (b :: m) => (a = b.1) ∨ (in_context a m)

lemma context_terms_iff_in_list (a : ℕ) (Γ : context) :
    (a ∈ context_terms Γ) ↔ in_context a Γ := by
  induction Γ
  case nil =>
    simp only [context_terms, Finset.not_mem_empty, in_context]
  case cons b Γ' f =>
    simp only [context_terms, Finset.mem_union, Finset.mem_singleton, in_context]
    rw [f]

lemma in_context_append_neg (a : ℕ) (Γ Δ : context) :
    ¬ (in_context a (Γ ++ Δ)) → ¬ (in_context a Γ) ∧ ¬ (in_context a Δ) := by
  intro H
  induction Γ
  case nil =>
    simp only [in_context, not_false_eq_true, true_and] at H ⊢
    rwa [nil_append] at H
  case cons b Γ' f =>
    simp [in_context] at H f ⊢
    exact ⟨⟨H.1, (f (H.2)).1⟩, (f (H.2)).2⟩

lemma in_context_append_neg' (a : ℕ) (Γ Δ : context) :
    ¬ (in_context a Γ) ∧ ¬ (in_context a Δ) → ¬ (in_context a (Γ ++ Δ)) := by
  rintro ⟨H1, H2⟩
  induction Γ
  case nil =>
    simp only [nil_append]
    exact H2
  case cons b Γ' f =>
    simp [in_context, append_eq] at H1 ⊢
    exact ⟨H1.1, f H1.2⟩

-- We can only bind variable once per context --
inductive valid_ctx : context → Prop where
| valid_nil : valid_ctx []
| valid_cons (Γ : context) (x : ℕ) (T : Typ) :
    (valid_ctx Γ) → (¬ (in_context x Γ)) → valid_ctx ((x, T) :: Γ)

open valid_ctx

--Properties of valid contexts
lemma valid_push (Γ : context) (x : ℕ) (T : Typ) :
    valid_ctx Γ → ¬ (in_context x Γ) → valid_ctx ([(x, T)] ++ Γ) := by
  simp only [singleton_append]
  exact (valid_cons Γ x T)

lemma valid_remove_mid (Γ Δ Ψ : context) :
    valid_ctx (Ψ ++ Δ ++ Γ) -> valid_ctx (Ψ ++ Γ) := by
  induction Ψ
  case nil =>
    induction Δ
    case nil =>
      simp only [append_nil, nil_append, imp_self]
    case cons b Δ' f =>
      simp only [nil_append, cons_append] at f ⊢
      intro H
      cases H
      next x S p p' =>
        exact (f p)
  case cons b Ψ f =>
    simp only [cons_append, append_assoc]
    intro H
    cases H
    next x S p p' =>
      simp only [cons_append, append_assoc] at f p ⊢
      apply valid_cons
      exact (f p)
      apply in_context_append_neg'
      constructor
      exact (in_context_append_neg _ _ _ p').1
      exact (in_context_append_neg _ _ _ (in_context_append_neg _ _ _ p').2).2

lemma valid_remove_mid_cons (x : ℕ) (T : Typ) (Γ Δ : context) :
    valid_ctx (Δ ++ (x, T) :: Γ)
    → valid_ctx (Δ ++ Γ) := by
  intro H
  simp only [append_cons Δ (x, T) Γ] at H
  apply valid_remove_mid
  exact H

lemma valid_remove_cons (x : ℕ) (T : Typ) (Γ : context) :
    valid_ctx ((x, T) :: Γ)
    → valid_ctx (Γ) := by
  intro H
  rw [← nil_append Γ]
  apply valid_remove_mid_cons
  simp
  exact H

--Extracting (x : T) from a context
@[simp]
def get (x : ℕ) : context → Option Typ
| [] => none
| (y , S) :: Γ' => if x = y then some S else get x Γ'

@[simp]
def binds x T (Γ : context) := (get x Γ = some T)

--Properties of binds
lemma binds_singleton (x : ℕ) (T : Typ) : binds x T [(x, T)] := by
  simp only [binds]
  simp only [_root_.get]
  simp only [ite_true]

lemma binds_singleton_tail (x : ℕ) (T : Typ) (Γ : context) :
    binds x T ([(x, T)] ++ Γ) := by
  simp [binds, _root_.get, append_eq, nil_append, ite_true]

lemma binds_tail (x : ℕ) (T : Typ) (Γ Δ : context) :
    binds x T Γ → (¬ (in_context x Δ)) → binds x T (Δ ++ Γ) := by
  intro bx nx
  simp [binds] at bx ⊢
  induction Δ
  case nil =>
    simp only [nil_append, bx]
  case cons b Δ' f' =>
    simp [in_context] at nx
    push_neg at nx
    simp [_root_.get, append_eq]
    rw [if_neg nx.1]
    apply (f' nx.2)

lemma binds_head (x : ℕ) (T : Typ) (Γ Δ : context) :
    binds x T Γ → binds x T (Γ ++ Δ) := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    simp only [binds, _root_.get, append_eq]
    by_cases hxb : x = b.1
    . simp only [cons_append, _root_.get]
      rw [if_pos hxb, if_pos hxb]
      exact id
    . simp only [cons_append, _root_.get]
      rw [if_neg hxb]
      intro H
      simp [binds] at f
      rw [if_neg hxb]
      exact (f H)

--Case analysis on binds
lemma binds_concat_inv' (x : ℕ) (T : Typ) (Γ Δ : context) :
    binds x T (Γ ++ Δ)
    → ((in_context x Γ) ∨ ¬(binds x T Δ))
    → (binds x T Γ) := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    intro bxT h
    rcases h with h1 | h2
    . by_cases hxb : x = b.1
      . simp [if_pos hxb] at bxT ⊢
        exact bxT
      . simp [if_neg hxb] at bxT ⊢
        apply f
        exact bxT
        simp [in_context, hxb] at h1
        left
        exact h1
    . simp only [binds, _root_.get]
      by_cases hxb : x = b.1
      . simp [if_pos hxb] at bxT ⊢
        exact bxT
      . simp [if_neg hxb] at bxT ⊢
        apply f
        exact bxT
        right
        exact h2

lemma binds_concat_inv (x : ℕ) (T : Typ) (Γ Δ : context) :
    binds x T (Γ ++ Δ)
    → ((¬ (in_context x Γ)) ∧ (binds x T Δ)) ∨ (binds x T Γ) := by
  intro bxT
  refine Iff.mpr or_iff_not_imp_left ?_
  intro H
  apply binds_concat_inv' _ _ _ _ bxT
  push_neg at H
  exact Iff.mpr or_iff_not_imp_left H

lemma binds_singleton_inv (x y : ℕ) (X Y : Typ) :
    binds x X [(y,Y)] → (x = y) ∧ (X = Y) := by
  simp only [binds, _root_.get]
  intro H
  by_cases hxy : x = y
  . simp [if_pos hxy] at H
    exact ⟨hxy, H.symm⟩
  . simp [if_neg hxy] at H

lemma binds_mid (x : ℕ) (T : Typ) (Δ Γ : context) :
    valid_ctx (Γ ++ [(x,T)] ++ Δ)
    → binds x T (Γ ++ [(x,T)] ++ Δ) := by
  induction Γ
  case nil =>
    simp only [nil_append, singleton_append, binds, _root_.get, append_eq, ite_true, implies_true]
  case cons b Γ' f =>
    intro H
    cases H
    next y S H' g =>
      simp only [binds, _root_.get, append_eq, append_assoc, singleton_append] at f H' g ⊢
      by_cases hxy : x = y
      . simp [if_pos hxy]
        have ⟨_, t2⟩ := in_context_append_neg _ _ _ g
        simp at t2
        push_neg at t2
        by_contra _
        exact (t2.1 hxy.symm)
      . simp [if_neg hxy]
        exact (f H')

lemma binds_mid_eq (x : ℕ) (T S : Typ) (Γ Δ : context) :
    binds x T (Δ ++ [(x,S)] ++ Γ)
    → valid_ctx (Δ ++ [(x,S)] ++ Γ) →  T = S := by
  induction Δ
  case nil =>
    simp only [binds, _root_.get, append_eq, nil_append, ite_true, Option.some.injEq, singleton_append]
    exact (fun p _ => p.symm)
  case cons b Δ' f =>
    intro p H
    cases H
    next y S' H' g =>
      simp only [binds, _root_.get, append_eq, append_assoc, singleton_append] at p f H' g ⊢
      by_cases hxy : x = y
      . have ⟨_, t2⟩ := in_context_append_neg _ _ _ g
        simp at t2
        push_neg at t2
        by_contra _
        exact (t2.1 hxy.symm)
      . simp [if_neg hxy] at p
        exact (f p H')

lemma binds_mid_eq_cons (x : ℕ) (T S : Typ) (Γ Δ : context) :
    binds x T (Δ ++ (x,S) :: Γ)
    → valid_ctx (Δ ++ (x,S) :: Γ) → T = S := by
  intro p H
  simp only [append_cons Δ (x, S) Γ] at p H
  exact (binds_mid_eq x T S Γ Δ p H)

--Additional properties of binds
lemma binds_in_context (x : ℕ) (T : Typ) (Γ : context) :
    binds x T Γ → in_context x Γ := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    simp only [binds, _root_.get, in_context] at f ⊢
    by_cases hxb : x = b.1
    . simp only [if_pos hxb]
      intro _
      exact (Or.inl hxb)
    . simp only [if_neg hxb]
      intro p
      exact (Or.inr (f p))

lemma binds_fresh (x : ℕ) (T : Typ) (Γ : context) :
    ¬ in_context x Γ → ¬ binds x T Γ := by
  contrapose
  simp only [not_not]
  exact (binds_in_context x T Γ)

lemma binds_concat_ok (x : ℕ) (T : Typ) (Γ Δ : context) :
    binds x T Γ -> valid_ctx (Δ ++ Γ) -> binds x T (Δ ++ Γ) := by
  induction Δ
  case nil =>
    simp only [binds, nil_append]
    exact (fun p _ => p)
  case cons b Δ' f =>
    intro p H
    cases H
    next y S H' g =>
      simp only [binds, _root_.get, append_eq] at H' ⊢
      by_cases hxy : x = y
      . simp [if_pos hxy]
        by_contra
        apply g
        apply binds_in_context y T (Δ' ++ Γ)
        rw [← hxy]
        exact (f p H')
      . simp [if_neg hxy]
        exact (f p H')

lemma binds_weaken (x : ℕ) (T : Typ) (Γ Δ Ψ: context) :
    binds x T (Ψ ++ Γ)
    → valid_ctx (Ψ ++ Δ ++ Γ)
    → binds x T (Ψ ++ Δ ++ Γ) := by
  induction Ψ
  case nil =>
    simp only [binds, nil_append]
    exact (fun p H => (binds_concat_ok _ _ _ _ p H))
  case cons b Ψ' f =>
    intro p H
    cases H
    next y S H' g =>
      simp only [binds, _root_.get, append_eq, append_assoc, in_context] at f H' p g ⊢
      by_cases hxy : x = y
      . simp [if_pos hxy] at p ⊢
        exact p
      . simp [if_neg hxy] at p ⊢
        exact (f p H')

lemma binds_weaken_at_head (x : ℕ) (T : Typ) (Γ Δ : context) :
    binds x T Δ → valid_ctx (Γ ++ Δ)
    → binds x T (Γ ++ Δ) := (binds_weaken x T Δ Γ [])

lemma binds_remove_mid (x y : ℕ) (T S : Typ) (Γ Δ : context) :
    binds x T (Γ ++ ([(y,S)] ++ Δ))
    → x ≠ y → binds x T (Γ ++ Δ) := by
  intro p H
  have t := (binds_concat_inv x T Γ ([(y,S)] ++ Δ) p)
  rcases t with ⟨t11, t12⟩ | t2
  . apply (binds_tail x T Δ Γ)
    simp [if_neg H] at t12
    exact t12
    exact t11
  . apply (binds_head _ _ _ _ t2)

lemma binds_remove_mid_cons  (x y : ℕ) (T S : Typ) (Γ Δ : context) :
    binds x T (Δ ++ (y, S) :: Γ)
    → x ≠ y → binds x T (Δ ++ Γ) := by
  intro H p
  apply (binds_remove_mid x y T S Δ Γ)
  rwa [append_cons, append_assoc] at H
  exact p
