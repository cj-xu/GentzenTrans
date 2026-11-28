
 =====================================
 =                                   =
 =  Application: Uniform continuity  =
 =                                   =
 =====================================

    Chuangjie Xu, August 2019

    Updated in February 2020 and restructured in November 2026

Given a T-definable function f : ℕᴺ → ℕ, we construct a T-definable
function φ : ℕᴺ → ℕ such that, for each δ : ℕᴺ, φ(δ) is a modulus of
uniform continuity for f on the subspace of sequences bounded
pointwise by δ.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.UniformViaGentzen where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries
open import Applications.Continuity.Definitions
import Framework.Gentzen.LogicalRelation as GentzenLR

\end{code}

■ If f is uniformly continuous on Δ = {α : ℕᴺ | ∀i(αi ≤ δi)} with a
  modulus m, then RangeBound(m,f,δ) bounds the values of f on Δ.

\begin{code}

RangeBound : {Γ : Cxt} → T Γ (ι ⇾ (ιᶥ ⇾ ι) ⇾ ιᶥ ⇾ ι)
RangeBound = Rec · Lam ν₀
          --   rec (λ f → f)
        · Lam (Lam (Lam (Lam (MaxUpTo · Lam (ν₃ · Lam (ν₃ · (ν₁ ☆ ν₀)) · (Tail · ν₁)) · (Head · ν₀)))))
--       (λ n   g    f    δ → MaxUpTo  (λ i → g  (λ α → f   (i ✶ α))     (tail δ))      (head δ))
-- i.e.
-- RangeBound  0      f δ = f δ
-- RangeBound (suc n) f δ = MaxUpTo (λ i → RangeBound n (λ α → f (i ✶ α)) (tail δ)) (head δ)

RangeBound-spec
  : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ℕᴺ → ℕ} {δ : ℕᴺ}
  → (m : ℕ) → (∀{α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ m ] β → f α ≡ f β)
  → ∀ α → α ≤¹ δ → f α ≤ ⟦ RangeBound ⟧ᵐ γ m f δ
RangeBound-spec γ {f} {δ}  0      p α r = ≤refl' (p r ≤¹refl ≡[zero])
RangeBound-spec γ {f} {δ} (suc m) p α r = ≤trans claim₁ (≤trans claim₂ claim₃)
 where
  s : head α ✶ tail α ≤¹ δ
  s  0      = r 0
  s (suc i) = r (suc i)
  claim₀ : f α ≡ f (head α ✶ tail α)
  claim₀ = p r s (≡[suc] refl ≡[]-refl)
  claim₁ : f α ≤ f (head α ✶ tail α)
  claim₁ = ≤refl' claim₀
  q : ∀{α' β} → α' ≤¹ tail δ → β ≤¹ tail δ → α' ≡[ m ] β → f (head α ✶ α') ≡ f (head α ✶ β)
  q u v em = p (✶≤¹ u (r 0)) (✶≤¹ v (r 0)) (≡[suc] refl em)
  claim₂ : f (head α ✶ tail α) ≤ ⟦ RangeBound ⟧ᵐ γ m (λ β → f (head α ✶ β)) (tail δ)
  claim₂ = RangeBound-spec γ m q (tail α) (r ∘ suc)
  claim₃ : ⟦ RangeBound ⟧ᵐ γ m (λ β → f (head α ✶ β)) (tail δ) ≤ ⟦ RangeBound ⟧ᵐ γ (suc m) f δ
  claim₃ = MaxUpTo-spec (r 0) γ (λ i → ⟦ RangeBound ⟧ᵐ γ m (λ β → f (i ✶ β)) (tail δ))
  --   ⟦ RangeBound ⟧ᵐ γ (suc m) f δ
  -- ≡ ⟦ MaxUpTo ⟧ᵐ γ (λ i → ⟦ RangeBound ⟧ᵐ γ m (λ β → f (i ✶ β)) (tail δ)) (head δ)

\end{code}

■ A nucleus for uniform continuity

\begin{code}

Jι : Ty
Jι = (ιᶥ ⇾ ι) ⊠ (ιᶥ ⇾ ι)

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam (Pair · Lam ν₁ · Lam Zero)
-- λ n . ⟨ λα.n , λα.0 ⟩

κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Lam (Lam (Pair · Lam (Pr1 · (ν₂ · (Pr1 · ν₁ · ν₀)) · ν₀)
--  λ g   w →   (  ( λ α → V    (g    (V     w    α))   α )
                   · Lam (Max · (MaxUpTo · Lam (Pr2 · (ν₃ · ν₀) · ν₁) · (RangeBound · (Pr2 · ν₁ · ν₀) · (Pr1 · ν₁) · ν₀)) · (Pr2 · ν₁ · ν₀))))
--               , ( λ δ → max  (MaxUpTo  (λ i → M    (g    i)   δ)    (RangeBound   (M     w    δ)    (V     w)    δ))   (M     w    δ)))

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import Framework.Gentzen.Translation Jι η κ

\end{code}

■ The generic element Ω

\begin{code}

-- Α(n) := ⟨ λα.αn , λα.n+1 ⟩
Α : {Γ : Cxt} → T Γ (ι ⇾ Jι)
Α = Lam (Pair · Lam (ν₀ · ν₁) · Lam (Suc · ν₁))
--  λ n .     ⟨ λ α . α   n   , λ α . n+1 ⟩
Ω : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
Ω = κ · Α

\end{code}

■ A parametrized logical relation for uniform continuity

\begin{code}

private

 V M : (ℕᴺ → ℕ) × (ℕᴺ → ℕ) → ℕᴺ → ℕ
 V = pr₁  -- value component
 M = pr₂  -- modulus component

Rι : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι δ n w =  (n ≡ V w δ)
         -- n is the value of w at δ
          × (∀{α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ M w δ ] β → V w α ≡ V w β)
         -- M(w,δ) is a modulus of uniform continuity of V(w) on inputs bounded by δ

module LR (δ : ℕᴺ) = GentzenLR Jι η κ (Rι δ)
open import Framework.Gentzen.Genericity Jι η κ ιᶥ Rι

Rη : (δ : ℕᴺ) → LR.η-compatible δ
Rη δ _ n = refl , (λ _ _ _ → refl)

Rκ : (δ : ℕᴺ) → LR.κ-compatible δ
Rκ δ γ {f} {g} ζ {n} {w} (e , prf) = trans e₀ e₁ , goal
 where
  e₀ : f n ≡ V (g n) δ
  e₀ = pr₁ (ζ n)
  e₁ : V (g n) δ ≡ V (g (V w δ)) δ
  e₁ = ap (λ x → V (g x) δ) e
  m : ℕ
  m = M (⟦ κ ⟧ᵐ γ g w) δ
  goal : ∀{α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ m ] β
       → V (g (V w α)) α ≡ V (g (V w β)) β
  goal {α} {β} u v em = trans claim₀ claim₂
   where
    m₀ m₁ m₂ : ℕ
    m₀ = M (g (V w α)) δ
    m₁ = ⟦ MaxUpTo ⟧ᵐ γ (λ i → M (g i) δ) (⟦ RangeBound ⟧ᵐ γ (M w δ) (V w) δ)
    m₂ = M w δ
    m₀≤m₁ : m₀ ≤ m₁
    m₀≤m₁ = MaxUpTo-spec (RangeBound-spec γ (M w δ) prf α u) γ (λ i → M (g i) δ)
    m₀≤m : m₀ ≤ m
    m₀≤m = ≤trans m₀≤m₁ (Max-spec₀ m₁ m₂)
    em₀ : α ≡[ m₀ ] β
    em₀ = ≡[≤] em m₀≤m
    em₂ : α ≡[ m₂ ] β
    em₂ = ≡[≤] em (Max-spec₁ m₁ m₂)
    claim₀ : V (g (V w α)) α ≡ V (g (V w α)) β
    claim₀ = pr₂ (ζ (V w α)) u v em₀
    claim₁ : V w α ≡ V w β
    claim₁ = prf u v em₂
    claim₂ : V (g (V w α)) β ≡ V (g (V w β)) β
    claim₂ = ap (λ x → V (g x) β) claim₁

RΩ : {Γ : Cxt} → is-generic (Ω {Γ})
RΩ _ δ {n} {w} = Rκ δ ⋆ claim {n} {w}
 where
  claim : ∀ i → Rι δ (δ i) (⟦ Α ⟧ i)
  claim i = refl , (λ _ _ em → ≡[]-< em ≤refl)

\end{code}

■ Theorem: Every closed term t : ιᶥ ⇾ ι of T has a modulus of
           uniform continuity given by the term Pr2(tᴶΩ).

\begin{code}

𝐌 : T ε (ιᶥ ⇾ ι) → T ε (ιᶥ ⇾ ι)
𝐌 t = Pr2 · (t ᴶ · Ω)

uniform-modulus-correct
 : (t : T ε (ιᶥ ⇾ ι))
 → ⟦ 𝐌 t ⟧ is-a-modulus-of-uniform-continuity-of ⟦ t ⟧
uniform-modulus-correct t = MoUC-is-extensional claim₀ claim₁
 where
  cor : (α : ℕᴺ) → Rι α (⟦ t ⟧ α) ⟦ t ᴶ · Ω ⟧
  cor α = FTLR t ⋆ (λ {n} {w} → RΩ ⋆ α {n} {w})
   where
    open LR.Soundness α (Rη α) (Rκ α) using (FTLR)
  claim₀ : ∀ α → ⟦ t ⟧ α ≡ V ⟦ t ᴶ · Ω ⟧ α
  claim₀ α = pr₁ (cor α)
  claim₁ : M ⟦ t ᴶ · Ω ⟧ is-a-modulus-of-uniform-continuity-of V ⟦ t ᴶ · Ω ⟧
  claim₁ {δ} = pr₂ (cor δ)

\end{code}
