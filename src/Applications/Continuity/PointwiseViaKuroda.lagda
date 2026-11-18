
 ==================================================================
 =                                                                =
 =  Application: Pointwise continuity via the Kuroda Translation  =
 =                                                                =
 ==================================================================

    Chuangjie Xu, September 2022

    Updated in October 2026 and restructured in November 2026

This module instantiates the Kuroda-style monadic translation with a
nucleus for pointwise continuity.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.PointwiseViaKuroda where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries
open import Applications.Continuity.Definitions

\end{code}

A computation carries both a value and a bound on the input sequence
needed to determine that value. The operations η and κ introduce and
combine these bounds.

\begin{code}

J : Ty → Ty
J σ = ι ⇾ ιᶥ ⇾ σ ⊠ ι

η : {Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ)
η = Lam (Lam (Lam (Pair · ν₂ · ν₁)))
-- λ x n α . ⟨ x , n ⟩

κ : {Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ)
κ = Lam (Lam (Lam (Lam (Pair · (Pr1 · (ν₃ · (Pr1 · (ν₂ · ν₁ · ν₀)) · ν₁ · ν₀))
                             · (Max · (Max · (Pr2 · (ν₃ · (Pr1 · (ν₂ · ν₁ · ν₀)) · ν₁ · ν₀)) · (Pr2 · (ν₂ · ν₁ · ν₀))) · ν₁)))))
-- λ f x n α . ⟨ (f((xnα)₁,n,α))₁ , max((f((xnα)₁,n,α))₂,(xnα)₂,n) ⟩

open import Framework.Kuroda J η κ

\end{code}

The generic element Ω records each query to the input sequence.
For a closed System T term f of type (ι ⇾ ι) ⇾ ι, the term M f
extracts the bound from the translation of f applied to Ω.

\begin{code}

q : {Γ : Cxt} → T Γ (ι ⇾ J ι)
q = Lam (Lam (Lam (Pair · (ν₀ · ν₂) · (Max · (Suc · ν₂) · ν₁))))
-- λ i n α . ⟨ αi , max(i+1,n) ⟩

Ω : {Γ : Cxt} → T Γ (J (ι ⇾ J ι))
Ω = η · q

M : T ε (ιᶥ ⇾ ι) → T ε ((ι ⇾ ι) ⇾ ι)
M f = Lam (Lam (Pr2 · (ν₁ · ν₀))) · (f ᴷ ● Ω · Zero)
-- pr₂ ∘ ((fᴷ • Ω) 0)

\end{code}

■ Logical relations for pointwise continuity

Fix an input sequence `α` and an incoming bound `n`. The relations
`V` and `C` are defined together: `C` says that a computation's
value is related by `V`, its bound is at least `n`, and its value
is stable on sequences agreeing with `α` through that bound.
The maps `V→K` and `K→V` identify `V` with the value relation
constructed by the generic fundamental theorem.

\begin{code}

module At (α : ℕᴺ) (n : ℕ) where

 mutual
  V : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ ⟧ʸ → Set
  V ι x a = x ≡ a
  V (σ ⊠ τ) x a = V σ (pr₁ x) (pr₁ a) × V τ (pr₂ x) (pr₂ a)
  V (σ ⇾ τ) f g = ∀ {x a} → V σ x a → C τ (f x) (g a)

  C : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ J ⟨ ρ ⟩ ⟧ʸ → Set
  C ρ x w = V ρ x (pr₁ (w n α))
           × (n ≤ pr₂ (w n α))
           × (∀ β → α ≡[ pr₂ (w n α) ] β
                    → pr₁ (w n β) ≡ pr₁ (w n α))

 module K = FundamentalTheorem C

 mutual
  V→K : (ρ : Ty) → ∀ {x a} → V ρ x a → K.V ρ x a
  V→K ι e = e
  V→K (σ ⊠ τ) (p , q) = V→K σ p , V→K τ q
  V→K (σ ⇾ τ) φ {x} {a} θ = φ (K→V σ θ)

  K→V : (ρ : Ty) → ∀ {x a} → K.V ρ x a → V ρ x a
  K→V ι e = e
  K→V (σ ⊠ τ) (p , q) = K→V σ p , K→V τ q
  K→V (σ ⇾ τ) φ {x} {a} θ = φ (V→K σ θ)

 η-compatible : K.η-compatible
 η-compatible {ρ = ρ} γ θ = K→V ρ θ , ≤refl , λ β _ → refl

 κ-compatible : K.κ-compatible
 κ-compatible {σ = σ} {τ = τ} γ {f = f} {g = g}
              ζ {x = x} {w = w} (θ , _ , stablew) =
   pr₁ p , Max-spec₁ (max k m) n , stable
  where
   a : ⟦ ⟨ σ ⟩ ⟧ʸ
   a = pr₁ (w n α)
   m k : ℕ
   m = pr₂ (w n α)
   k = pr₂ (g a n α)
   p : C τ (f x) (g a)
   p = ζ {x = x} {a = a} (V→K σ θ)
   stable : ∀ β → α ≡[ max (max k m) n ] β
            → pr₁ (g (pr₁ (w n β)) n β) ≡ pr₁ (g a n α)
   stable β em = trans first second
    where
     em-w : α ≡[ m ] β
     em-w = ≡[≤] em
       (≤trans (Max-spec₁ k m) (Max-spec₀ (max k m) n))
     em-g : α ≡[ k ] β
     em-g = ≡[≤] em
       (≤trans (Max-spec₀ k m) (Max-spec₀ (max k m) n))
     first : pr₁ (g (pr₁ (w n β)) n β) ≡ pr₁ (g a n β)
     first = ap (λ v → pr₁ (g v n β)) (stablew β em-w)
     second : pr₁ (g a n β) ≡ pr₁ (g a n α)
     second = pr₂ (pr₂ p) β em-g

 q-related : V (ι ⇾ ι) α ⟦ q ⟧
 q-related {x = i} {a = j} refl =
   refl , Max-spec₁ (suc i) n ,
   λ β em → sym (≡[]-< em (Max-spec₀ (suc i) n))

 Ω-related : C (ι ⇾ ι) α ⟦ Ω ⟧
 Ω-related = η-compatible {ρ = ι ⇾ ι} ⋆
   {x = α} {a = ⟦ q ⟧} (V→K (ι ⇾ ι) {x = α} {a = ⟦ q ⟧} q-related)

 fΩ-related : (f : T ε (ιᶥ ⇾ ι))
            → C ι (⟦ f ⟧ α) ⟦ f ᴷ ● Ω ⟧
 fΩ-related f =
   K.C[●] κ-compatible {Γ = ε} {σ = ι ⇾ ι} {τ = ι} ⋆
     {f = ⟦ f ⟧} {F = ⟦ f ᴷ ⟧} {x = α} {a = ⟦ Ω ⟧}
     (K.FTLR η-compatible κ-compatible f ⋆)
     Ω-related

\end{code}

■ Correctness of the extracted modulus

The fundamental theorem relates a closed term to its translation.
Applying the translated term to the generic element relates its
result to the computation whose second component `M` extracts.
The stability clause of `C` then gives pointwise continuity.

\begin{code}

Thm[Cont] : (f : T ε (ιᶥ ⇾ ι))
          → ⟦ M f ⟧ is-a-modulus-of-continuity-of ⟦ f ⟧
Thm[Cont] f α β em = trans eqα (trans (sym stable) (sym eqβ))
 where
  module A = At α 0
  module B = At β 0

  w : ⟦ J ι ⟧ʸ
  w = ⟦ f ᴷ ● Ω ⟧

  pα : A.C ι (⟦ f ⟧ α) w
  pα = A.fΩ-related f

  pβ : B.C ι (⟦ f ⟧ β) w
  pβ = B.fΩ-related f

  eqα : ⟦ f ⟧ α ≡ pr₁ (w 0 α)
  eqα = pr₁ pα

  eqβ : ⟦ f ⟧ β ≡ pr₁ (w 0 β)
  eqβ = pr₁ pβ

  stable : pr₁ (w 0 β) ≡ pr₁ (w 0 α)
  stable = pr₂ (pr₂ pα) β em

\end{code}
