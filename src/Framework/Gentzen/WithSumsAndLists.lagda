
 ==========================================================
 =                                                        =
 =  Gentzen-style translation with sums and finite lists  =
 =                                                        =
 ==========================================================

    Chuangjie Xu, November 2026

We extend the translation and its fundamental theorem to System T
with sums and finite lists.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import SystemT.WithSumsAndLists

\end{code}

■ Nucleus and translation

A generalized nucleus consists of a type operation J and term
families η and κ, available in every context. Their instances may
have free variables; no monad laws are assumed.

The translation applies J at data types and translates functions
and products componentwise. The auxiliary translation ⟨_⟩ᴰ
translates the components of a data type before applying J.
The operation KE extends κ to arbitrary translated result types.

\begin{code}

module Framework.Gentzen.WithSumsAndLists
       (J : Ty → Ty)
       (η : {Γ : Cxt} {A : Ty} → T Γ (A ⇾ J A))
       (κ : {Γ : Cxt} {A B : Ty} → T Γ ((A ⇾ J B) ⇾ J A ⇾ J B))
 where

mutual
 ⟨_⟩ᴶ : Ty → Ty
 ⟨ dataᵀ D ⟩ᴶ = J (⟨ D ⟩ᴰ)
 ⟨ σ ⊠ τ ⟩ᴶ = ⟨ σ ⟩ᴶ ⊠ ⟨ τ ⟩ᴶ
 ⟨ σ ⇾ τ ⟩ᴶ = ⟨ σ ⟩ᴶ ⇾ ⟨ τ ⟩ᴶ

 ⟨_⟩ᴰ : DataTy → Ty
 ⟨ nat ⟩ᴰ = ι
 ⟨ sum σ τ ⟩ᴰ = ⟨ σ ⟩ᴶ ⊞ ⟨ τ ⟩ᴶ
 ⟨ list σ ⟩ᴰ = Listᵀ ⟨ σ ⟩ᴶ

⟪_⟫ᴶ : Cxt → Cxt
⟪ ε ⟫ᴶ = ε
⟪ Γ ₊ ρ ⟫ᴶ = ⟪ Γ ⟫ᴶ ₊ ⟨ ρ ⟩ᴶ

⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ᴶ ∈ ⟪ Γ ⟫ᴶ ∥
⟨ zero ⟩ᵛ  = zero
⟨ suc i ⟩ᵛ = suc ⟨ i ⟩ᵛ

KE : {A : Ty} (ρ : Ty) {Γ : Cxt} → T Γ ((A ⇾ ⟨ ρ ⟩ᴶ) ⇾ J A ⇾ ⟨ ρ ⟩ᴶ)
KE (dataᵀ D) = κ
KE (σ ⊠ τ)   = Lam (Lam (Pair · (KE σ · Lam (Pr1 · (ν₂ · ν₀)) · ν₀)
                              · (KE τ · Lam (Pr2 · (ν₂ · ν₀)) · ν₀)))
KE (σ ⇾ τ)   = Lam (Lam (Lam (KE τ · Lam (ν₃ · ν₀ · ν₁) · ν₁)))

infix 60 _ᴶ

_ᴶ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᴶ ⟨ ρ ⟩ᴶ
Var i ᴶ = Var ⟨ i ⟩ᵛ
Lam t ᴶ = Lam (t ᴶ)
(f · u) ᴶ = f ᴶ · u ᴶ
Pair ᴶ = Pair
Pr1 ᴶ = Pr1
Pr2 ᴶ = Pr2
Zero ᴶ = η · Zero
Suc ᴶ = κ · (η ○ Suc)
Rec {ρ} ᴶ = Lam (Lam (KE ρ · (Rec · ν₁ · (ν₀ ○ η))))
Inj1 ᴶ = η ○ Inj1
Inj2 ᴶ = η ○ Inj2
Case {ρ = ρ} ᴶ = Lam (Lam (KE ρ · (Case · ν₁ · ν₀)))
Nil ᴶ = η · Nil
Cons ᴶ = Lam (κ · (η ○ (Cons · ν₀)))
LRec {ρ = ρ} ᴶ =
  Lam (Lam (KE ρ · (LRec · ν₁ · Lam (Lam (ν₂ · ν₁ · (η · ν₀))))))

\end{code}

■ Logical relation between ⟦ ρ ⟧ʸ and ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ

Given a base relation between ⟦ dataᵀ D ⟧ʸ and ⟦ ⟨ dataᵀ D ⟩ᴶ ⟧ʸ for
each data type D, we extend it to a logical relation for each type.

\begin{code}

module LogicalRelation
       (Rᴰ : (D : DataTy) → ⟦ dataᵀ D ⟧ʸ → ⟦ ⟨ dataᵀ D ⟩ᴶ ⟧ʸ → Set)
 where

 R : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
 R (dataᵀ D) = Rᴰ D
 R (σ ⊠ τ) x a = R σ (pr₁ x) (pr₁ a) × R τ (pr₂ x) (pr₂ a)
 R (σ ⇾ τ) f g = ∀ {x a} → R σ x a → R τ (f x) (g a)

 Rˣ : (Γ : Cxt) → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ → Set
 Rˣ ε ⋆ ⋆ = 𝟙
 Rˣ (Γ ₊ ρ) (γ , x) (δ , a) = Rˣ Γ γ δ × R ρ x a

 R[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
        → Rˣ Γ γ δ → (i : ∥ ρ ∈ Γ ∥) → R ρ (γ ₍ i ₎) (δ ₍ ⟨ i ⟩ᵛ ₎)
 R[Var] (_ , θ) zero = θ
 R[Var] (ξ , _) (suc i) = R[Var] ξ i

\end{code}

■ Lifted relation between ⟦ dataᵀ D ⟧ʸ and ⟦ ⟨ D ⟩ᴰ ⟧ʸ

In the compatibility conditions, the interpretation of η and the
function supplied to the interpretation of κ take inputs of type
⟦ ⟨ D ⟩ᴰ ⟧ʸ, before the outer J is applied.  To compare these
inputs with source data, we lift R through the data constructors,
obtaining S.

\begin{code}

 data S⊞ (σ τ : Ty) : ⟦ σ ⊞ τ ⟧ʸ → ⟦ ⟨ σ ⟩ᴶ ⊞ ⟨ τ ⟩ᴶ ⟧ʸ → Set where
  left  : ∀ {x a} → R σ x a → S⊞ σ τ (inl x) (inl a)
  right : ∀ {y b} → R τ y b → S⊞ σ τ (inr y) (inr b)

 data Slist (σ : Ty) : ⟦ Listᵀ σ ⟧ʸ → ⟦ Listᵀ ⟨ σ ⟩ᴶ ⟧ʸ → Set where
  nil  : Slist σ [] []
  cons : ∀ {x a xs as} → R σ x a → Slist σ xs as → Slist σ (x ∷ xs) (a ∷ as)

 S : (D : DataTy) → ⟦ dataᵀ D ⟧ʸ → ⟦ ⟨ D ⟩ᴰ ⟧ʸ → Set
 S nat = _≡_
 S (sum σ τ) = S⊞ σ τ
 S (list σ) = Slist σ

\end{code}

■ Compatibility conditions on the nucleus operations

\begin{code}

 η-compatible : Set
 η-compatible
   = {D : DataTy} {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ} → ∀ {x a}
   → S D x a → R (dataᵀ D) x (⟦ η ⟧ᵐ γ a)

 κ-compatible : Set
 κ-compatible
   = {D E : DataTy} {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
     {f : ⟦ dataᵀ D ⟧ʸ → ⟦ dataᵀ E ⟧ʸ} {g : ⟦ ⟨ D ⟩ᴰ ⟧ʸ → ⟦ J (⟨ E ⟩ᴰ) ⟧ʸ}
   → (∀ {x a} → S D x a → R (dataᵀ E) (f x) (g a))
   → ∀ {x w} → R (dataᵀ D) x w → R (dataᵀ E) (f x) (⟦ κ ⟧ᵐ γ g w)

 R[KE] : κ-compatible
       → {D : DataTy} (ρ : Ty) → ∀ {Γ} {γ : ⟦ Γ ⟧ˣ}
       → {f : ⟦ dataᵀ D ⟧ʸ → ⟦ ρ ⟧ʸ} {g : ⟦ ⟨ D ⟩ᴰ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ}
       → (∀ {x a} → S D x a → R ρ (f x) (g a))
       → ∀ {x w} → R (dataᵀ D) x w → R ρ (f x) (⟦ KE ρ ⟧ᵐ γ g w)
 R[KE] Rκ (dataᵀ E) = Rκ
 R[KE] Rκ (σ ⊠ τ) p r = R[KE] Rκ σ (pr₁ ∘ p) r , R[KE] Rκ τ (pr₂ ∘ p) r
 R[KE] Rκ (σ ⇾ τ) p r q = R[KE] Rκ τ (λ s → p s q) r

\end{code}

■ Fundamental theorem of logical relations

\begin{code}

 module Soundness (Rη : η-compatible) (Rκ : κ-compatible) where

  FTLR : ∀ {Γ ρ} (t : T Γ ρ) {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
       → Rˣ Γ γ δ → R ρ (⟦ t ⟧ᵐ γ) (⟦ t ᴶ ⟧ᵐ δ)
  FTLR (Var i) ξ = R[Var] ξ i
  FTLR (Lam t) ξ θ = FTLR t (ξ , θ)
  FTLR (f · u) ξ = FTLR f ξ (FTLR u ξ)
  FTLR Pair _ p q = p , q
  FTLR Pr1 _ = pr₁
  FTLR Pr2 _ = pr₂
  FTLR Zero _ = Rη refl
  FTLR Suc _ = Rκ (λ e → Rη (ap suc e))
  FTLR (Rec {ρ}) _ {b} {b'} rb {h} {h'} rh = R[KE] Rκ ρ step
   where
    step : {i j : ℕ} → i ≡ j
         → R ρ (rec b h i) (rec b' (λ k → h' (⟦ η ⟧ᵐ _ k)) j)
    step {0} refl = rb
    step {suc i} refl = rh (Rη refl) (step {i} refl)
  FTLR Inj1 _ θ = Rη (left θ)
  FTLR Inj2 _ θ = Rη (right θ)
  FTLR (Case {σ} {τ} {ρ}) _ {f} {f'} rf {g} {g'} rg =
    R[KE] Rκ ρ branches
   where
    branches : ∀ {x a} → S (sum σ τ) x a
             → R ρ (case f g x) (case f' g' a)
    branches (left p)  = rf p
    branches (right q) = rg q
  FTLR (Nil {σ}) _ = Rη nil
  FTLR (Cons {σ}) _ rx =
    Rκ (λ rs → Rη (cons rx rs))
  FTLR (LRec {σ} {ρ}) _ {b} {b'} rb {h} {h'} rh =
    R[KE] Rκ ρ inner
   where
    inner : ∀ {xs as} → S (list σ) xs as
          → R ρ (listrec b h xs) (listrec b' (λ z zs → h' z (⟦ η ⟧ᵐ _ zs)) as)
    inner nil = rb
    inner (cons rx rs) = rh rx (Rη rs) (inner rs)

  closed-FTLR : ∀ {ρ} (t : T ε ρ) → R ρ ⟦ t ⟧ ⟦ t ᴶ ⟧
  closed-FTLR t = FTLR t ⋆

\end{code}
