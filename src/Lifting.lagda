
 ======================================================
 =                                                    =
 =  Application: Lifting to higher-order functionals  =
 =                                                    =
 ======================================================

    Chuangjie Xu, July 2019

    Updated in February 2020 and June 2026

This module formalizes a lifting argument for proving properties of all
T-definable functionals of type X ⇾ ι.  The key device is the reader
nucleus Jι = X ⇾ ι.  A term f : X ⇾ ι is translated to fᴶ, and the
translated term can be applied to a generic element Ω : Xᴶ.  Genericity
of Ω gives pointwise agreement between the original functional f and its
lifted representation fᴶ Ω.

The first part of the module develops this representation theorem.  We
first prove the abstract consequence of any generic element Ω.  We then
construct generic elements directly for X = ι and X = ι ⇾ ι; these two
proofs use only reflexivity and congruence, not function extensionality.
For arbitrary finite type X, we construct a uniform Ω from mutually
recursive maps up and down.  Proving genericity of this uniform Ω uses
function extensionality.

The second part packages the intended application.  Let P be a property
of semantic functionals ⟦ X ⟧ʸ → ℕ, such as continuity when X is ι ⇾ ι.
To prove P for every closed System-T term f : X ⇾ ι, we lift P to a
predicate Q on translated types.  The proof then has three ingredients:
Q is preserved by the translated constants η and κ, the generic element
Ω satisfies Q at type X, and Ω represents ordinary inputs correctly.
Applying Q to fᴶ Ω gives P for the lifted functional, and the
representation theorem transfers the result back to f.  The submodule
PredicateUsage formalizes this predicate-transfer argument.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries

\end{code}

■ A nucleus for lifting to higher types

Fix a finite type X and define Jι = X ⇾ ι.  The unit η embeds a natural
number as the corresponding constant function on X.  The operation κ is
pointwise: given g : ι ⇾ Jι and f : Jι, it first computes f x and then
evaluates g (f x) at the same x.  These three terms instantiate the
Gentzen translation with the reader nucleus.

\begin{code}

module Lifting (X : Ty) where

Jι : Ty
Jι = X ⇾ ι

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam (Lam ν₁)
 -- λ(n : ι). λ(x : X). n

κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Lam (Lam (Lam (ν₂ · (ν₁ · ν₀) · ν₀)))
 -- λ(g : ι ⇾ X ⇾ ι). λ(f : X ⇾ ι). λ(x : X). g (f x) x

-- Instantiate the Gentzen translation with the reader nucleus.
open import GentzenTranslation Jι η κ

\end{code}

■ Relating terms and their lifting via a parametrized logical relation

The correctness relation is indexed by a semantic input x : ⟦ X ⟧ʸ.  At
base type, n : ℕ is related to f : ⟦ Jι ⟧ʸ exactly when f evaluates to n
at x.  The lemmas Rη and Rκ show that η and κ preserve this base
relation.  The imported module LogicalRelation then extends it to all
finite types.

\begin{code}

-- Base case: observe a translated natural number at x.
Rι : ⟦ X ⟧ʸ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι x n f = n ≡ f x

-- η preserves Rι because constant functions evaluate to their value.
Rη : (x : ⟦ X ⟧ʸ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ)
   → Rι x n (⟦ η ⟧ᵐ γ n)
Rη x _ n = refl

-- κ preserves Rι by transporting along the equality supplied for h.
Rκ : (x : ⟦ X ⟧ʸ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → Rι x (f i) (g i))
   → ∀ {n h} → Rι x n h
   → Rι x (f n) (⟦ κ ⟧ᵐ γ g h)
Rκ x _ {f} {g} ζ {n} {h} θ = transport (λ z → f n ≡ g z x) θ (ζ n)

-- Extend Rι to all finite types using the fundamental logical relation.
R : ⟦ X ⟧ʸ → {ρ : Ty}
  → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
R x = LR._R_
 where
  import LogicalRelation Jι η κ (Rι x) (Rη x) (Rκ x) as LR

-- Extend the same relation to source and translated environments.
Rˣ : (x : ⟦ X ⟧ʸ) {Γ : Cxt}
   → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ → Set
Rˣ x = LR._Rˣ_
 where
  import LogicalRelation Jι η κ (Rι x) (Rη x) (Rκ x) as LR

\end{code}

■ Abstract consequence of a generic element

A term ω : Xᴶ may depend on variables in any context.  The predicate
is-generic requires ω to be related to every input x under every
assignment to its context.  In Cor, ω has context Γᴶ so that it can be
applied to fᴶ.  If the source and translated assignments are related
at x, the fundamental theorem then gives pointwise agreement between
an open f : X ⇾ ι and fᴶ ω.

\begin{code}

is-generic : {Γ : Cxt} → T Γ ⟨ X ⟩ᴶ → Set
is-generic {Γ} ω = (γ : ⟦ Γ ⟧ˣ) → (x : ⟦ X ⟧ʸ)
                 → R x x (⟦ ω ⟧ᵐ γ)

Cor : {Γ : Cxt}
    → (ω : T ⟪ Γ ⟫ᴶ ⟨ X ⟩ᴶ)
    → is-generic ω
    → (f : T Γ (X ⇾ ι))
    → (x : ⟦ X ⟧ʸ)
    → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
    → Rˣ x γ δ
    → ⟦ f ⟧ᵐ γ x ≡ ⟦ f ᴶ · ω ⟧ᵐ δ x
Cor ω generic f x {δ = δ} ξ = LR.FTLR f ξ (generic δ x)
 where
  import LogicalRelation Jι η κ (Rι x) (Rη x) (Rκ x) as LR

\end{code}

■ A generic element for X = ι without FunExt

Because the module is parametrized by X, the special case is stated
under p : X ≡ ι.  After pattern matching on refl, Ω₀ is the identity
function on ι.  Its genericity is immediate, since the base relation is
just evaluation at x.

\begin{code}

Ω₀ : X ≡ ι
   → {Γ : Cxt} → T Γ ⟨ X ⟩ᴶ
Ω₀ refl = Lam ν₀
       -- λ(n : ι). n

R[Ω₀] : (p : X ≡ ι) → {Γ : Cxt} → is-generic (Ω₀ p {Γ})
R[Ω₀] refl _ _ = refl

Cor[ι] : (p : X ≡ ι)
       → {Γ : Cxt}
       → (f : T Γ (X ⇾ ι))
       → (x : ⟦ X ⟧ʸ)
       → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
       → Rˣ x γ δ
       → ⟦ f ⟧ᵐ γ x ≡ ⟦ f ᴶ · Ω₀ p ⟧ᵐ δ x
Cor[ι] refl = Cor (Ω₀ refl) (R[Ω₀] refl)

\end{code}

■ A generic element for X = ι ⇾ ι without FunExt

After specializing X to ι ⇾ ι, a translated input of type Xᴶ has type
Jι ⇾ Jι, that is, (X ⇾ ι) ⇾ (X ⇾ ι).  The generic element Ω₁ is the
expected generic oracle: given a query f : X ⇾ ι and an input
α : ι ⇾ ι, it returns α (f α).

To prove genericity, fix x : ⟦ ι ⇾ ι ⟧ʸ.  The function clause of R asks
us to send related inputs to related outputs.  Thus, from n Rι x h,
which unfolds to n ≡ h x, we must prove x n ≡ x (h x).  This follows
by congruence of the fixed function x.  No equality between functions is
constructed, so function extensionality is unnecessary.

\begin{code}

Ω₁ : X ≡ (ι ⇾ ι)
   → {Γ : Cxt} → T Γ ⟨ X ⟩ᴶ
Ω₁ refl = Lam (Lam (ν₀ · (ν₁ · ν₀)))
       -- λ(f : (ι ⇾ ι) ⇾ ι). λ(α : ι ⇾ ι). α (f α)

R[Ω₁] : (p : X ≡ (ι ⇾ ι)) → {Γ : Cxt} → is-generic (Ω₁ p {Γ})
R[Ω₁] refl γ x p = ap x p

Cor[ι⇾ι] : (p : X ≡ (ι ⇾ ι))
         → {Γ : Cxt}
         → (f : T Γ (X ⇾ ι))
         → (x : ⟦ X ⟧ʸ)
         → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
         → Rˣ x γ δ
         → ⟦ f ⟧ᵐ γ x ≡ ⟦ f ᴶ · Ω₁ p ⟧ᵐ δ x
Cor[ι⇾ι] refl = Cor (Ω₁ refl) (R[Ω₁] refl)

\end{code}

■ A generic element for arbitrary X

For arbitrary X, the generic element is constructed uniformly.  For each
type ρ, the term up turns an X-indexed ρ-value into a translated value
of type ⟨ ρ ⟩ᴶ.  Conversely, down observes a translated value at a given
x : X and returns an ordinary ρ-value.  The two maps are mutually
recursive at function types: up uses down on the domain, while down uses
up on the domain.

The candidate generic element is obtained by applying up at type X to
the identity function on X.

\begin{code}

up   : (ρ : Ty)
     → {Γ : Cxt}
     → T Γ ((X ⇾ ρ) ⇾ ⟨ ρ ⟩ᴶ)

down : (ρ : Ty)
     → {Γ : Cxt}
     → T Γ (⟨ ρ ⟩ᴶ ⇾ X ⇾ ρ)

up ι = Lam ν₀
    -- λ(f : X ⇾ ι). f

up (σ ⇾ τ) = Lam (Lam (up τ · Lam (ν₂ · ν₀ · (down σ · ν₁ · ν₀))))
          -- λ(f : X ⇾ σ ⇾ τ). λ(a : σᴶ). up τ (λ(x : X). f x (down σ a x))

up (σ ⊠ τ) = Lam (Pair · (up σ · Lam (Pr1 · (ν₁ · ν₀)))
                       · (up τ · Lam (Pr2 · (ν₁ · ν₀))))
          -- λ(f : X ⇾ σ ⊠ τ). ⟨ up σ (pr₁ ∘ f) , up τ (pr₂ ∘ f) ⟩

down ι = Lam ν₀
      -- λ(f : X ⇾ ι). f

down (σ ⇾ τ) = Lam (Lam (Lam (down τ · (ν₂ · (up σ · Lam ν₁)) · ν₁)))
            -- λ(f : σᴶ ⇾ τᴶ). λ(x : X). λ(a : σ). down τ (f (up σ (λ(z : X). a))) x

down (σ ⊠ τ) = Lam (Lam (Pair · (down σ · (Pr1 · ν₁) · ν₀)
                              · (down τ · (Pr2 · ν₁) · ν₀)))
            -- λ(w : σᴶ ⊠ τᴶ). λ(x : X). ⟨ down σ (pr₁ w) x , down τ (pr₂ w) x ⟩

Ω : {Γ : Cxt} → T Γ ⟨ X ⟩ᴶ
Ω = up X · Lam ν₀
 -- up X (λ(x : X). x)

\end{code}

■ Genericity of Ω for arbitrary X

The proofs R[up] and R→down express the two compatibility properties of
up and down.  The lemma R[up] says that up maps an X-indexed value F to
a translated value related to F x.  The lemma R→down says that, if an
ordinary value is related to a translated value, then down recovers that
ordinary value at x.

The only use of function extensionality is in the function-type case of
R→down, where pointwise equalities are assembled into an equality of
functions.  Hence the general proof that Ω is generic requires FunExt,
even though the concrete cases X = ι and X = ι ⇾ ι do not.

\begin{code}

R[up] : FunExt → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
      → (ρ : Ty) (x : ⟦ X ⟧ʸ) (f : ⟦ X ⇾ ρ ⟧ʸ)
      → R x (f x) (⟦ up ρ ⟧ᵐ γ f)

R→down : FunExt → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
       → (ρ : Ty) (x : ⟦ X ⟧ʸ)
       → {a : ⟦ ρ ⟧ʸ} {b : ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ}
       → R x a b → a ≡ ⟦ down ρ ⟧ᵐ γ b x

R[up] funExt ι x f = refl
R[up] funExt {γ = γ} (σ ⇾ τ) x f {u} {h} θ = goal
 where
  up-τ : ⟦ (X ⇾ τ) ⇾ ⟨ τ ⟩ᴶ ⟧ʸ
  up-τ = ⟦ up τ ⟧ᵐ ((γ , f) , h)
  down-σ : ⟦ ⟨ σ ⟩ᴶ ⇾ (X ⇾ σ) ⟧ʸ
  down-σ u y = ⟦ down σ ⟧ᵐ (((γ , f) , u) , y) u y
  IH-R[up-τ] : R x (f x (down-σ h x)) (up-τ (λ y → f y (down-σ h y)))
  IH-R[up-τ] = R[up] funExt {γ = (γ , f) , h} τ x (λ y → f y (down-σ h y))
  IH-R→down-σ : u ≡ down-σ h x
  IH-R→down-σ = R→down funExt {γ = ((γ , f) , h) , x} σ x θ
  goal : R x (f x u) (up-τ (λ y → f y (down-σ h y)))
  goal = transport (λ z → R x (f x z) (up-τ (λ y → f y (down-σ h y))))
                   (sym IH-R→down-σ) IH-R[up-τ]
R[up] funExt {γ = γ} (σ ⊠ τ) x f =
  R[up] funExt {γ = γ , f} σ x (pr₁ ∘ f) ,
  R[up] funExt {γ = γ , f} τ x (pr₂ ∘ f)

R→down funExt ι x θ = θ
R→down funExt {γ = γ} (σ ⇾ τ) x {u} {b = b} θ =
  funExt (λ a →
    R→down funExt {γ = ((γ , b) , x) , a} τ x
      (θ (R[up] funExt {γ = ((γ , b) , x) , a} σ x (λ _ → a))))
R→down funExt {γ = γ} (σ ⊠ τ) x {b = b} θ =
  ap² _,_ (R→down funExt {γ = (γ , b) , x} σ x (pr₁ θ))
          (R→down funExt {γ = (γ , b) , x} τ x (pr₂ θ))

R[Ω] : FunExt → {Γ : Cxt} → is-generic (Ω {Γ})
R[Ω] funExt δ x = R[up] funExt X x (λ a → a)

\end{code}

■ Representation using the uniform generic element

The context-polymorphic Ω satisfies is-generic by R[Ω].  Applying Cor
to this proof gives the representation for open terms in arbitrary
related contexts.

\begin{code}

Cor[Ω] : FunExt → {Γ : Cxt}
       → (f : T Γ (X ⇾ ι))
       → (x : ⟦ X ⟧ʸ)
       → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
       → Rˣ x γ δ
       → ⟦ f ⟧ᵐ γ x ≡ ⟦ f ᴶ · Ω ⟧ᵐ δ x
Cor[Ω] funExt {Γ} f x ξ =
  Cor (Ω {⟪ Γ ⟫ᴶ}) (R[Ω] funExt) f x ξ

\end{code}

■ Correctness for arbitrary X

Specializing the open-term corollary Cor[Ω] to the empty context gives
pointwise agreement between f and fᴶ Ω.  The theorem Cor[X] then uses
function extensionality once more to turn this pointwise agreement into
equality of semantic functions.

\begin{code}

Cor[X] : FunExt
       → (f : T ε (X ⇾ ι))
       → ⟦ f ⟧ ≡ ⟦ f ᴶ · Ω ⟧
Cor[X] funExt f = funExt (λ x → Cor[Ω] funExt f x ⋆)

\end{code}

■ Transferring predicates to T-definable functionals

The submodule PredicateUsage packages the motivating application.  It
starts with a predicate P on semantic functionals of type X ⇾ ι.  The
assumptions Pη and Pκ state that P is preserved by the semantic actions
of η and κ.  The predicate Q lifts P from base type to all translated
types, and Qˣ lifts Q pointwise to translated environments.

The lemma FTQ is a direct unary fundamental theorem for the translated
term tᴶ.  If Ω satisfies Q at type X, then FTQ applied to f : X ⇾ ι
gives P ⟦ fᴶ · Ω ⟧.  Finally, Cor[X] identifies f with fᴶ Ω, so the
property transfers to P ⟦ f ⟧.

This direct unary proof could also be recovered from the binary logical
relation used above by taking its base relation to be Qι n h = P h,
independent of n.  The unary presentation is kept because the lifted
predicate Q and the final theorem P[f] are more readable in this form.

\begin{code}

module PredicateUsage
  (funExt : FunExt)
  (P : ⟦ X ⇾ ι ⟧ʸ → Set)
  (Pη : (n : ⟦ ι ⟧ʸ) → P (λ _ → n))
  (Pκ : {g : ⟦ ι ⇾ Jι ⟧ʸ} → ((n : ⟦ ι ⟧ʸ) → P (g n))
      → {h : ⟦ Jι ⟧ʸ} → P h
      → P (λ x → g (h x) x))
 where

 -- Lift P from base type to all translated types.
 Q : {ρ : Ty} → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
 Q {ι} = P
 Q {σ ⇾ τ} f = ∀ {x} → Q x → Q (f x)
 Q {σ ⊠ τ} (a , b) = Q a × Q b

 -- Pointwise lifting of Q to translated environments. 
 Qˣ : {Γ : Cxt} (δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ) → Set
 Qˣ {ε} ⋆ = 𝟙
 Qˣ {Γ ₊ σ} (δ , a) = Qˣ δ × Q a

 -- Variables preserve Q by lookup in the translated environment.
 Q[Var] : {Γ : Cxt} {ρ : Ty} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
        → Qˣ δ → (i : ∥ ρ ∈ Γ ∥) → Q (δ ₍ ⟨ i ⟩ᵛ ₎)
 Q[Var] (Θ , q)  zero   = q
 Q[Var] (Θ , q) (suc i) = Q[Var] Θ i

 -- Preservation of Q by the lifted extension operator KE.
 Q[KE] : {ρ : Ty} {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ} {g : ⟦ ι ⇾ ⟨ ρ ⟩ᴶ ⟧ʸ}
       → (∀ i → Q (g i))
       → Q {ι ⇾ ρ} (⟦ KE ⟧ᵐ γ g)
 Q[KE] {ι} = Pκ
 Q[KE] {σ ⇾ τ} ζ χ q = Q[KE] {τ} (λ i → ζ i q) χ
 Q[KE] {σ ⊠ τ} ζ χ = Q[KE] (pr₁ ∘ ζ) χ , Q[KE] (pr₂ ∘ ζ) χ

 -- Fundamental theorem for the unary predicate Q.
 FTQ : {Γ : Cxt} {ρ : Ty}
     → (t : T Γ ρ)
     → {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ} → Qˣ δ
     → Q (⟦ t ᴶ ⟧ᵐ δ)
 FTQ (Var i) θ = Q[Var] θ i
 FTQ (Lam t) θ = λ q → FTQ t (θ , q)
 FTQ (f · a) θ = FTQ f θ (FTQ a θ)
 FTQ Pair _ ξ ζ = ξ , ζ
 FTQ Pr1 _ = pr₁
 FTQ Pr2 _ = pr₂
 FTQ Zero _ = Pη 0
 FTQ Suc _ = Pκ (Pη ∘ suc)
 FTQ Rec _ {a} χ {g} ξ = Q[KE] claim
  where
   claim : ∀ i → Q (rec a _ i)
   claim  zero   = χ
   claim (suc i) = ξ (Pη i) (claim i)

 -- Predicate-transfer theorem for all closed T-definable functionals.
 P[T-definable] : Q ⟦ Ω ⟧
                → (f : T ε (X ⇾ ι))
                → P ⟦ f ⟧
 P[T-definable] qΩ f = transport P (sym e) P[fᴶΩ]
  where
   P[fᴶΩ] : P ⟦ f ᴶ · Ω ⟧
   P[fᴶΩ] = FTQ f ⋆ qΩ
   e : ⟦ f ⟧ ≡ ⟦ f ᴶ · Ω ⟧
   e = Cor[X] funExt f

\end{code}
