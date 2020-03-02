
 ================================
 =                              =
 =  §3.3.2  Uniform continuity  =
 =                              =
 ================================

    Chuangjie Xu, August 2019

    Updated in February 2020

For T-definable function f : ℕᴺ → ℕ we construct a modulus of uniform
continuity, that is, a function φ : ℕᴺ → ℕ such that f is uniformly
continuous on the subspace {α : ℕᴺ | ∀i(αi ≤ δi)} with a modulus φ(δ)
for each sequence δ.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries

module UniformContinuity where

\end{code}

■ Preliminaries

\begin{code}

_≤¹_ : ℕᴺ → ℕᴺ → Set
α ≤¹ β = ∀ i → α i ≤ β i

≤¹refl : ∀{α} → α ≤¹ α
≤¹refl i = ≤refl

✶≤¹ : {α β : ℕᴺ} {n : ℕ} → α ≤¹ tail β → n ≤ β 0 → n ✶ α ≤¹ β
✶≤¹ u r  0      = r
✶≤¹ u r (suc i) = u i

_is-a-modulus-of-uniform-continuity-of_ : (ℕᴺ → ℕ) → (ℕᴺ → ℕ) → Set
φ is-a-modulus-of-uniform-continuity-of f =
  ∀{δ α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ φ δ ] β → f α ≡ f β

MoUC-is-extensional : {f g φ : ℕᴺ → ℕ} → (∀ α → f α ≡ g α)
                    → φ is-a-modulus-of-uniform-continuity-of g
                    → φ is-a-modulus-of-uniform-continuity-of f
MoUC-is-extensional {f} {g} {φ} ex mcg {δ} {α} {β} u v em = begin
  f α ≡⟨ ex α ⟩
  g α ≡⟨ mcg u v em ⟩
  g β ≡⟨ sym (ex β) ⟩
  f β ∎

--
-- If f is uniformly continuous on Δ = {α : ℕᴺ | ∀i(αi ≤ δi)} with a
-- modulus m, then it has a maximum image Ψ(m,f,δ) on Δ.
--
Ψ : {Γ : Cxt} → T Γ (ι ⇾ (ιᶥ ⇾ ι) ⇾ ιᶥ ⇾ ι)
Ψ = Rec · Lam (Lam (ν₁ · ν₀))
--   rec (λ f   δ  → f δ)
        · Lam (Lam (Lam (Lam (Φ · Lam (ν₃ · Lam (ν₃ · (ν₁ ☆ ν₀)) · (Tail · ν₁)) · (Head · ν₀)))))
--       (λ n   g    f    δ → Φ  (λ i → g  (λ α → f   (i ✶ α))     (tail δ))      (head δ))
-- i.e.
-- Ψ  0      f δ = f 0ʷ
-- Ψ (suc n) f δ = Φ (λ i → Ψ n (λ α → f (i ✶ α)) (tail δ)) (head δ)

Ψ-spec : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ℕᴺ → ℕ} {δ : ℕᴺ}
       → (m : ℕ) → (∀{α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ m ] β → f α ≡ f β)
       → ∀ α → α ≤¹ δ → f α ≤ ⟦ Ψ ⟧ᵐ γ m f δ
Ψ-spec γ {f} {δ}  0      p α r = ≤refl' (p r ≤¹refl ≡[zero])
Ψ-spec γ {f} {δ} (suc m) p α r = ≤trans claim₁ (≤trans claim₂ claim₃)
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
  claim₂ : f (head α ✶ tail α) ≤ ⟦ Ψ ⟧ᵐ γ m (λ β → f (head α ✶ β)) (tail δ)
  claim₂ = Ψ-spec γ m q (tail α) (r ∘ suc)
  claim₃ : ⟦ Ψ ⟧ᵐ γ m (λ β → f (head α ✶ β)) (tail δ) ≤ ⟦ Ψ ⟧ᵐ γ (suc m) f δ
  claim₃ = Φ-spec (r 0) γ (λ i → ⟦ Ψ ⟧ᵐ γ m (λ β → f (i ✶ β)) (tail δ))
  --   ⟦ Ψ ⟧ᵐ γ (suc m) f δ
  -- ≡ ⟦ Φ ⟧ᵐ γ (λ i → ⟦ Ψ ⟧ᵐ γ m (λ β → f (i ✶ β)) (tail δ)) (head δ)

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
                   · Lam (Max · (Φ · Lam (Pr2 · (ν₃ · ν₀) · ν₁) · (Ψ · (Pr2 · ν₁ · ν₀) · (Pr1 · ν₁) · ν₀)) · (Pr2 · ν₁ · ν₀))))
--               , ( λ δ → max  (Φ  (λ i → M    (g    i)   δ)    (Ψ   (M     w    δ)    (V     w)    δ))   (M     w    δ)))

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import GentzenTranslation Jι η κ

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

V M : (ℕᴺ → ℕ) × (ℕᴺ → ℕ) → ℕᴺ → ℕ
V = pr₁  -- value component
M = pr₂  -- modulus component

--
-- Base case of the logical relation
--
Rι : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι δ n w =  (n ≡ V w δ)
         -- n is the value of w at δ
          × (∀{α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ M w δ ] β → V w α ≡ V w β)
         -- M(w,δ) is a modulus of uniform continuity of V(w) on inputs bounded by δ

--
-- η preserves the logical relation
--
Rη : (δ : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → Rι δ n (⟦ η ⟧ᵐ γ n)
Rη δ _ n = refl , (λ _ _ _ → refl)

--
-- κ preserves the logical relation
--
Rκ : (δ : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → Rι δ (f i) (g i)) → ∀ {n w} → Rι δ n w → Rι δ (f n) (⟦ κ ⟧ᵐ γ g w)
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
    m₁ = ⟦ Φ ⟧ᵐ γ (λ i → M (g i) δ) (⟦ Ψ ⟧ᵐ γ (M w δ) (V w) δ)
    m₂ = M w δ
    m₀≤m₁ : m₀ ≤ m₁
    m₀≤m₁ = Φ-spec (Ψ-spec γ (M w δ) prf α u) γ (λ i → M (g i) δ)
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

--
-- Ω preserves the logical relation
--
RΩ : (δ : ℕᴺ)
   → ∀{n w} → Rι δ n w → Rι δ (δ n) (⟦ Ω ⟧ w)
 -- i.e.  R δ δ ⟦ Ω ⟧
RΩ δ {n} {w} = Rκ δ ⋆ claim {n} {w}
 where
  claim : ∀ i → Rι δ (δ i) (⟦ Α ⟧ i)
  claim i = refl , (λ _ _ em → ≡[]-< em ≤refl)

--
-- Extend Rι to R for all types of T
--
R : ℕᴺ → {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
R δ = LR._R_
 where
  import LogicalRelation Jι η κ (Rι δ) (Rη δ) (Rκ δ) as LR

--
-- Corollary of the Fundamental Theorem of Logical Relation
--
Cor[R] : {ρ : Ty} (t : T ε ρ) (δ : ℕᴺ) → R δ ⟦ t ⟧ ⟦ t ᴶ ⟧
Cor[R] t δ = LR.FTLR t ⋆
 where
  import LogicalRelation Jι η κ (Rι δ) (Rη δ) (Rκ δ) as LR

\end{code}

■ Theorem: Every closed term t : ℕᴺ ⇾ ℕ of T has a modulus of
           uniform continuity given by the term M(tᴶΩ).

\begin{code}

Thm[UC] : (t : T ε (ιᶥ ⇾ ι))
        → M ⟦ t ᴶ · Ω ⟧ is-a-modulus-of-uniform-continuity-of ⟦ t ⟧
Thm[UC] t = MoUC-is-extensional claim₀ claim₁
 where
  claim₀ : ∀ α → ⟦ t ⟧ α ≡ V ⟦ t ᴶ · Ω ⟧ α
  claim₀ α = pr₁ (Cor[R] t α (λ {n} {w} → RΩ α {n} {w}))
  claim₁ : M ⟦ t ᴶ · Ω ⟧ is-a-modulus-of-uniform-continuity-of V ⟦ t ᴶ · Ω ⟧
  claim₁ {δ} = pr₂ (Cor[R] t δ (λ {n} {w} → RΩ δ {n} {w}))

\end{code}
