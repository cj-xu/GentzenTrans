
 =====================================
 =                                   =
 =  A Kuroda-style translation of T  =
 =                                   =
 =====================================

    Chuangjie Xu, July 2019

    Updated in October 2026 and restructured in November 2026

This module defines a Kuroda-style monadic translation of System T
and proves its fundamental theorem of logical relations. Its
call-by-value treatment of application follows the pattern of
Powell's translation in [1]: the translated function and argument
are both handled through the Kleisli operation before application.
Here the translation is parametrized by a type-indexed nucleus
rather than a particular state monad, and the proof does not
require the monad laws.

References.

□ Thomas Powell.  A functional interpretation with state.  In:
  Proceedings of the Thirty third Annual IEEE Symposium on Logic in
  Computer Science (LICS 2018), IEEE Computer Society Press, 2018,
  pp. 839–848.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries

module Framework.Kuroda
       (J : Ty → Ty)
       (η : {Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ))
       (κ : {Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ))
 where

⟨_⟩ᴷ ⟨_⟩ : Ty → Ty
⟨ ρ ⟩ᴷ    = J ⟨ ρ ⟩
⟨ ι ⟩     = ι
⟨ σ ⊠ τ ⟩ = ⟨ σ ⟩ ⊠ ⟨ τ ⟩
⟨ σ ⇾ τ ⟩ = ⟨ σ ⟩ ⇾ J ⟨ τ ⟩

⟪_⟫ : Cxt → Cxt
⟪ ε ⟫     = ε
⟪ Γ ₊ ρ ⟫ = ⟪ Γ ⟫ ₊ ⟨ ρ ⟩

⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ ∈ ⟪ Γ ⟫ ∥
⟨ zero ⟩ᵛ  = zero
⟨ suc i ⟩ᵛ = suc ⟨ i ⟩ᵛ

infixl 20 _●_

_●_ : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ)) → T Γ (J σ) → T Γ (J τ)
f ● a = ●Ap · f · a
     -- κ (λ h → κ h a) f
 where
  ●Ap : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ) ⇾ J σ ⇾ J τ)
  ●Ap = Lam (Lam (κ · Lam (κ · ν₀ · ν₁) · ν₁))

Rec● : {Γ : Cxt} {ρ : Ty} → T Γ (ρ ⇾ (ι ⇾ J (ρ ⇾ J ρ)) ⇾ ι ⇾ J ρ)
Rec● = Lam (Lam (Rec · (η · ν₁) · Lam (Lam (ν₂ · ν₁ ● ν₀))))
--   Rec●(a,f,0) = η(a)
-- Rec●(a,f,n+1) = fn ● Rec●(a,f,n)

infix 60 _ᴷ

_ᴷ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ ⟨ ρ ⟩ᴷ
Var i ᴷ   = η · Var ⟨ i ⟩ᵛ
Lam t ᴷ   = η · Lam (t ᴷ)
(f · a) ᴷ = f ᴷ ● a ᴷ
Pair ᴷ    = η · Lam (η · Lam (η · (Pair · ν₁ · ν₀)))
Pr1 ᴷ     = η · (η ○ Pr1)
Pr2 ᴷ     = η · (η ○ Pr2)
Zero ᴷ    = η · Zero
Suc ᴷ     = η · (η ○ Suc)
Rec ᴷ     = η · Lam (η · Lam (η · (Rec● · ν₁ · ν₀)))

\end{code}

■ Fundamental theorem of logical relations

The computation relation `C` relates a source value of type `ρ`
to a value of the translated type `J ⟨ ρ ⟩`. The value relation
`V` is equality at natural numbers, componentwise at products,
and relates functions when they send related arguments to
computations related by `C`. We also extend `V` to contexts.

The two compatibility assumptions below correspond to the unit
and Kleisli extension of the nucleus. The theorem says that
related assignments give related interpretations of a term
and its Kuroda-style translation. The proof is by induction on
the term, with a separate induction for primitive recursion.

\begin{code}

module FundamentalTheorem
       (C : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ J ⟨ ρ ⟩ ⟧ʸ → Set)
 where

 V : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ ⟧ʸ → Set
 V ι n a = n ≡ a
 V (σ ⊠ τ) x a = V σ (pr₁ x) (pr₁ a) × V τ (pr₂ x) (pr₂ a)
 V (σ ⇾ τ) f g = ∀ {x a} → V σ x a → C τ (f x) (g a)

 Vˣ : (Γ : Cxt) → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ ⟧ˣ → Set
 Vˣ ε ⋆ ⋆ = 𝟙
 Vˣ (Γ ₊ ρ) (γ , x) (δ , a) = Vˣ Γ γ δ × V ρ x a

 η-compatible : Set
 η-compatible =
   ∀ {Γ ρ} (γ : ⟦ Γ ⟧ˣ) {x : ⟦ ρ ⟧ʸ} {a : ⟦ ⟨ ρ ⟩ ⟧ʸ}
   → V ρ x a → C ρ x (⟦ η ⟧ᵐ γ a)

 κ-compatible : Set
 κ-compatible =
   ∀ {Γ σ τ} (γ : ⟦ Γ ⟧ˣ)
     {f : ⟦ σ ⟧ʸ → ⟦ τ ⟧ʸ}
     {g : ⟦ ⟨ σ ⟩ ⟧ʸ → ⟦ J ⟨ τ ⟩ ⟧ʸ}
   → (∀ {x a} → V σ x a → C τ (f x) (g a))
   → ∀ {x w} → C σ x w → C τ (f x) (⟦ κ ⟧ᵐ γ g w)

 V[Var] : {Γ : Cxt} {ρ : Ty}
        → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ ⟧ˣ}
        → Vˣ Γ γ δ → (i : ∥ ρ ∈ Γ ∥)
        → V ρ (γ ₍ i ₎) (δ ₍ ⟨ i ⟩ᵛ ₎)
 V[Var] (_ , θ) zero = θ
 V[Var] (ξ , _) (suc i) = V[Var] ξ i

 -- The two binds in translated application see successively
 -- extended contexts; κ need not be a closed term.
 C[●] : κ-compatible
      → {Γ : Cxt} {σ τ : Ty} (δ : ⟦ Γ ⟧ˣ)
      → {f : ⟦ σ ⇾ τ ⟧ʸ} {F : ⟦ J ⟨ σ ⇾ τ ⟩ ⟧ʸ}
        {x : ⟦ σ ⟧ʸ} {a : ⟦ J ⟨ σ ⟩ ⟧ʸ}
      → C (σ ⇾ τ) f F → C σ x a
      → C τ (f x)
          (⟦ κ ⟧ᵐ ((δ , F) , a)
            (λ h → ⟦ κ ⟧ᵐ (((δ , F) , a) , h) h a) F)
 C[●] hκ {σ = σ} {τ = τ} δ {F = F} {x = x} {a = a} φ χ =
   hκ {σ = σ ⇾ τ} {τ = τ} ((δ , F) , a)
     {f = λ h → h x}
     {g = λ h → ⟦ κ ⟧ᵐ (((δ , F) , a) , h) h a}
     (λ {y} {h} θ → hκ (((δ , F) , a) , h) θ χ) φ

 -- Induction on the recursion argument, using C[●] at each step.
 C[Rec●] : η-compatible → κ-compatible
         → {Γ : Cxt} {ρ : Ty} (δ : ⟦ Γ ⟧ˣ)
         → {a : ⟦ ρ ⟧ʸ} {a' : ⟦ ⟨ ρ ⟩ ⟧ʸ}
         → V ρ a a'
         → {f : ℕ → ⟦ ρ ⟧ʸ → ⟦ ρ ⟧ʸ}
           {g : ⟦ ⟨ ι ⇾ ρ ⇾ ρ ⟩ ⟧ʸ}
         → V (ι ⇾ ρ ⇾ ρ) f g
         → (n : ℕ)
         → C ρ (rec a f n) (⟦ Rec● ⟧ᵐ δ a' g n)
 C[Rec●] hη hκ δ {a' = a'} θ {g = g} ψ 0 =
   hη ((δ , a') , g) θ
 C[Rec●] hη hκ δ {a' = a'} θ {g = g} ψ (suc n) =
   C[●] hκ ((((δ , a') , g) , n) , ⟦ Rec● ⟧ᵐ δ a' g n)
     (ψ refl) (C[Rec●] hη hκ δ θ ψ n)

 FTLR : η-compatible → κ-compatible
      → {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
      → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ ⟧ˣ}
      → Vˣ Γ γ δ
      → C ρ (⟦ t ⟧ᵐ γ) (⟦ t ᴷ ⟧ᵐ δ)
 FTLR hη hκ (Var i) {δ = δ} ξ = hη δ (V[Var] ξ i)
 FTLR hη hκ (Lam t) {δ = δ} ξ =
   hη δ (λ {x} {a} θ → FTLR hη hκ t (ξ , θ))
 FTLR hη hκ (f · a) {δ = δ} ξ =
   C[●] hκ δ (FTLR hη hκ f ξ) (FTLR hη hκ a ξ)
 FTLR hη hκ Pair {δ = δ} ξ =
   hη δ (λ {x} {a} θ →
     hη (δ , a) (λ {y} {b} ψ →
       hη ((δ , a) , b) (θ , ψ)))
 FTLR hη hκ Pr1 {δ = δ} ξ = hη δ (λ {x} {a} θ → hη δ (pr₁ θ))
 FTLR hη hκ Pr2 {δ = δ} ξ = hη δ (λ {x} {a} θ → hη δ (pr₂ θ))
 FTLR hη hκ Zero {δ = δ} ξ = hη δ refl
 FTLR hη hκ Suc {δ = δ} ξ = hη δ (λ {x} {a} θ → hη δ (ap suc θ))
 FTLR hη hκ (Rec {σ = ρ}) {δ = δ} ξ =
   hη {ρ = ρ ⇾ (ι ⇾ ρ ⇾ ρ) ⇾ ι ⇾ ρ} δ
     (λ {a} {a'} θ →
       hη {ρ = (ι ⇾ ρ ⇾ ρ) ⇾ ι ⇾ ρ} (δ , a')
         (λ {f} {g} ψ →
           hη {ρ = ι ⇾ ρ} ((δ , a') , g)
             (λ {n} {m} e →
               transport
                 (λ j → C ρ (rec a f n)
                   (⟦ Rec● ⟧ᵐ ((δ , a') , g) a' g j))
                 e
                 (C[Rec●] hη hκ {ρ = ρ} ((δ , a') , g)
                   {a = a} {a' = a'} θ {f = f} {g = g} ψ n))))

\end{code}
