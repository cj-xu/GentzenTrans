Chuangjie Xu, November 2026

This is the Agda development accompanying the paper

  Chuangjie Xu
  The Gentzen-style monadic translation of Gödel's System T revisited
  https://arxiv.org/abs/2610.05187

The source files are available at

  https://github.com/cj-xu/GentzenTrans

All the files are tested in the safe mode of Agda version 2.8.0.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Revisited.index where

open import Preliminaries
open import SystemT.Base
import Framework.Gentzen.Translation as Gentzen
import Framework.Gentzen.LogicalRelation as GentzenLR

\end{code}

§2.2 Gödel's System T

The paper uses named variables. In the Agda syntax, variables are
represented by de Bruijn indices.

\begin{code}

syntax-of-T : Set × Set × (Cxt → Ty → Set)
syntax-of-T = Ty , Cxt , T

standard-interpretation-of-T
 : (Ty → Set)
 × (Cxt → Set)
 × ({Γ : Cxt} {σ : Ty} → T Γ σ → ⟦ Γ ⟧ˣ → ⟦ σ ⟧ʸ)
standard-interpretation-of-T = ⟦_⟧ʸ , ⟦_⟧ˣ , ⟦_⟧ᵐ

\end{code}

§3.1 Nuclei and the translation

\begin{code}

-- Definition 3.1
nucleus : Set
nucleus = Σ \(Jι : Ty)
        → ({Γ : Cxt} → T Γ (ι ⇾ Jι))
        × ({Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι))

module GentzenTranslation ((Jι , η , κ) : nucleus) where

 open Gentzen Jι η κ

 -- Definition 3.2
 Gentzen-translation
  : Σ \(⟨_⟩ᴶ : Ty → Ty)
  → Σ \(⟪_⟫ᴶ : Cxt → Cxt)
  → ({Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᴶ ⟨ ρ ⟩ᴶ)
  × ({ρ : Ty} {Γ : Cxt} → T Γ ((ι ⇾ ⟨ ρ ⟩ᴶ) ⇾ ⟨ ι ⟩ᴶ ⇾ ⟨ ρ ⟩ᴶ))
 Gentzen-translation = ⟨_⟩ᴶ , ⟪_⟫ᴶ , _ᴶ , KE

\end{code}

§3.2 The fundamental theorem of logical relations

\begin{code}

 module LogicalRelation (_Rι_ : ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set) where

  open GentzenLR Jι η κ _Rι_

  -- Definition 3.3
  logical-relation
   : ({ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set)
   × ({Γ : Cxt} → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ → Set)
  logical-relation = _R_ , _Rˣ_

  -- Compatibility conditions (†)
  compatibility-conditions : Set
  compatibility-conditions = η-compatible × κ-compatible

  -- Lemma 3.4
  preservation-KE
   : κ-compatible
   → {ρ : Ty} {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ} {f : ⟦ ι ⇾ ρ ⟧ʸ} {g : ⟦ ι ⇾ ⟨ ρ ⟩ᴶ ⟧ʸ}
   → (∀ i → f i R g i) → f R (⟦ KE ⟧ᵐ γ g)
  preservation-KE = R[KE]

  -- Theorem 3.5
  fundamental-theorem
   : compatibility-conditions
   → {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
   → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ} → γ Rˣ δ
   → ⟦ t ⟧ᵐ γ R ⟦ t ᴶ ⟧ᵐ δ
  fundamental-theorem (Rη , Rκ) = Soundness.FTLR Rη Rκ

\end{code}

§4.1 Majorizability

\begin{code}

module Majorizability where

 import Applications.Majorizability as M
 open Gentzen M.Jι M.η M.κ using (⟨_⟩ᴶ; _ᴶ)
 open GentzenLR M.Jι M.η M.κ M._⊲ι_

 -- Definition 4.1
 majorizability-relation : {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
 majorizability-relation = M._⊲_

 -- Definition 4.2
 majorizability-nucleus : nucleus
 majorizability-nucleus = M.Jι , M.η , M.κ

 -- Lemma 4.3
 maximum-bound : {i j : ℕ} → i ≤ j → (g : ℕ → ℕ) → g i ≤ ⟦ M.κ ⟧ g j
 maximum-bound i≤j = M.κ-spec i≤j ⋆

 -- Lemma 4.4
 preservation : η-compatible × κ-compatible
 preservation = M.⊲η , M.⊲κ

 -- Corollary 4.5
 majorization : {ρ : Ty} (t : T ε ρ)
              → majorizability-relation ⟦ t ⟧ ⟦ t ᴶ ⟧
 majorization = M.Cor[Maj]

\end{code}

§4.2 Lifting to higher-order functionals

\begin{code}

module Lifting (X : Ty) where

 open import Applications.Lifting X
 open Gentzen Jι η κ using (⟨_⟩ᴶ; ⟪_⟫ᴶ; _ᴶ)
 open import Framework.Gentzen.Genericity Jι η κ X Rι

 -- Definition 4.7
 lifting-nucleus : nucleus
 lifting-nucleus = Jι , η , κ

 -- Definition 4.8
 base-lifting-relation : ⟦ X ⟧ʸ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
 base-lifting-relation x = Rι x

 -- Lemma 4.9
 preservation : (x : ⟦ X ⟧ʸ) → LR.η-compatible x × LR.κ-compatible x
 preservation x = Rη x , Rκ x

 -- Corollary 4.10
 lifting-soundness
  : (x : ⟦ X ⟧ʸ) {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
  → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ} → Rˣ x γ δ
  → R x (⟦ t ⟧ᵐ γ) (⟦ t ᴶ ⟧ᵐ δ)
 lifting-soundness x = LR.Soundness.FTLR x (Rη x) (Rκ x)

 -- Definition 4.11
 generic-element
  : ((Jι , η , κ) : nucleus)
  → (⟦ X ⟧ʸ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set)
  → {Γ : Cxt} → T Γ (Gentzen.⟨_⟩ᴶ Jι η κ X) → Set
 generic-element (A , η , κ) S = G.is-generic
  where
   import Framework.Gentzen.Genericity A η κ X S as G

 -- Proposition 4.12
 representation
  : {Γ : Cxt} (Ω : T ⟪ Γ ⟫ᴶ ⟨ X ⟩ᴶ) → is-generic Ω
  → (f : T Γ (X ⇾ ι)) (x : ⟦ X ⟧ʸ)
  → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ} → Rˣ x γ δ
  → ⟦ f ⟧ᵐ γ x ≡ ⟦ f ᴶ · Ω ⟧ᵐ δ x
 representation = Cor

 -- Example 4.13
 generic-elements-at-types-0-and-1
  : {Γ : Cxt}
  → ((p : X ≡ ι) → is-generic (Ω₀ p {Γ}))
  × ((p : X ≡ (ι ⇾ ι)) → is-generic (Ω₁ p {Γ}))
 generic-elements-at-types-0-and-1
   = (λ p → R[Ω₀] p) , (λ p → R[Ω₁] p)

 -- Definition 4.14
 construction-of-Ω
  : ((ρ : Ty) → {Γ : Cxt} → T Γ ((X ⇾ ρ) ⇾ ⟨ ρ ⟩ᴶ))
  × ((ρ : Ty) → {Γ : Cxt} → T Γ (⟨ ρ ⟩ᴶ ⇾ X ⇾ ρ))
  × ({Γ : Cxt} → T Γ ⟨ X ⟩ᴶ)
 construction-of-Ω = up , down , Ω

 -- Proposition 4.15
 genericity-of-Ω : FunExt → {Γ : Cxt} → is-generic (Ω {Γ})
 genericity-of-Ω = R[Ω]

 -- Theorem 4.16
 representation-of-closed-terms
  : FunExt
  → (f : T ε (X ⇾ ι)) → ⟦ f ⟧ ≡ ⟦ f ᴶ · Ω ⟧
 representation-of-closed-terms = Cor[X]

 module Predicates
   (P : ⟦ X ⇾ ι ⟧ʸ → Set)
   (Pη : (n : ℕ) → P (⟦ η ⟧ n))
   (Pκ : {g : ℕ → ⟦ Jι ⟧ʸ} → ((n : ℕ) → P (g n))
       → {h : ⟦ Jι ⟧ʸ} → P h → P (⟦ κ ⟧ g h))
  where

  open PredicateUsage P Pη Pκ

  -- Definition 4.17
  lifted-predicate : {ρ : Ty} → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
  lifted-predicate = Q

  -- Proposition 4.18
  predicate-transfer-for-T-definable-functionals
   : FunExt
   → lifted-predicate ⟦ Ω ⟧
   → (f : T ε (X ⇾ ι)) → P ⟦ f ⟧
  predicate-transfer-for-T-definable-functionals
   = predicate-transfer

module SequentialContinuity where

 open import Applications.Continuity.SequentialViaLifting
 open import SystemT.Auxiliaries using (type; typeᵀ)

 -- Definition 4.19
 convergence-and-sequential-continuity
  : ((ℕ → type 0) → type 0 → Set)
  × ((ℕ → type 1) → type 1 → Set)
  × ((ℕ → type 2) → type 2 → Set)
  × (type 3 → Set)
 convergence-and-sequential-continuity
  = _is-eventually-equal-to_
  , _converges-pointwise-to_
  , _converges-continuously-to_
  , is-sequentially-continuous

 -- Corollary 4.20
 sequential-continuity
  : FunExt
  → (t : T ε (typeᵀ 3))
  → is-sequentially-continuous ⟦ t ⟧
 sequential-continuity = sequential-continuity-at-type-3

\end{code}

§4.3.1 Pointwise continuity

\begin{code}

module PointwiseContinuity where

 open import Applications.Continuity.PointwiseViaGentzen
 open import SystemT.Auxiliaries using (ιᶥ)
 open Gentzen Jι η κ using (_ᴶ)
 open import Framework.Gentzen.Genericity Jι η κ ιᶥ Rι

 -- Definition 4.21
 _is-a-modulus-of_at_ : ℕ → (ℕᴺ → ℕ) → ℕᴺ → Set
 m is-a-modulus-of f at α = (β : ℕᴺ) → α ≡[ m ] β → f α ≡ f β

 _is-a-modulus-of-pointwise-continuity-of_ : (ℕᴺ → ℕ) → (ℕᴺ → ℕ) → Set
 M is-a-modulus-of-pointwise-continuity-of f
  = (α : ℕᴺ) → M α is-a-modulus-of f at α

 -- Definition 4.22
 pointwise-continuity-nucleus : nucleus
 pointwise-continuity-nucleus = Jι , η , κ

 -- Definition 4.23
 base-continuity-relation : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
 base-continuity-relation = Rι

 -- Lemma 4.24
 preservation : (α : ℕᴺ) → LR.η-compatible α × LR.κ-compatible α
 preservation α = Rη α , Rκ α

 -- Definition 4.25
 generic-element : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
 generic-element = Ω

 -- Lemma 4.26
 genericity-of-Ω : {Γ : Cxt} → is-generic (Ω {Γ})
 genericity-of-Ω = RΩ

 -- Theorem 4.27
 pointwise-continuity
  : (f : T ε (ιᶥ ⇾ ι))
  → ⟦ Pr2 · (f ᴶ · Ω) ⟧ is-a-modulus-of-pointwise-continuity-of ⟦ f ⟧
 pointwise-continuity = pointwise-modulus-correct

\end{code}

§4.3.2 Uniform continuity

\begin{code}

module UniformContinuity where

 open import Applications.Continuity.UniformViaGentzen
 open import SystemT.Auxiliaries using (ιᶥ; _☆_; MaxUpTo)
 open Gentzen Jι η κ using (_ᴶ)
 open import Framework.Gentzen.Genericity Jι η κ ιᶥ Rι

 -- Definition 4.28
 _is-a-modulus-of_on-inputs-bounded-by_ : ℕ → (ℕᴺ → ℕ) → ℕᴺ → Set
 m is-a-modulus-of f on-inputs-bounded-by δ
  = ∀ {α β : ℕᴺ} → α ≤¹ δ → β ≤¹ δ → α ≡[ m ] β → f α ≡ f β

 _is-a-modulus-of-uniform-continuity-of_ : (ℕᴺ → ℕ) → (ℕᴺ → ℕ) → Set
 M is-a-modulus-of-uniform-continuity-of f
  = ∀ {δ : ℕᴺ} → M δ is-a-modulus-of f on-inputs-bounded-by δ

 -- Definition 4.29
 auxiliary-terms
  : ({Γ : Cxt} → T Γ ι → T Γ ιᶥ → T Γ ιᶥ)
  × ({Γ : Cxt} → T Γ (ι ⇾ (ιᶥ ⇾ ι) ⇾ ιᶥ ⇾ ι))
  × ({Γ : Cxt} → T Γ (ιᶥ ⇾ ι ⇾ ι))
 auxiliary-terms = _☆_ , RangeBound , MaxUpTo

 -- Lemma 4.30
 range-bound
  : {f : ℕᴺ → ℕ} {δ : ℕᴺ} (m : ℕ)
  → m is-a-modulus-of f on-inputs-bounded-by δ
  → (α : ℕᴺ) → α ≤¹ δ → f α ≤ ⟦ RangeBound ⟧ m f δ
 range-bound = RangeBound-spec ⋆

 -- Definition 4.31
 uniform-continuity-nucleus : nucleus
 uniform-continuity-nucleus = Jι , η , κ

 -- Definition 4.32
 base-continuity-relation : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
 base-continuity-relation = Rι

 -- Lemma 4.33
 preservation : (δ : ℕᴺ) → LR.η-compatible δ × LR.κ-compatible δ
 preservation δ = Rη δ , Rκ δ

 -- Definition 4.34
 generic-element : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
 generic-element = Ω

 -- Lemma 4.35
 genericity-of-Ω : {Γ : Cxt} → is-generic (Ω {Γ})
 genericity-of-Ω = RΩ

 -- Theorem 4.36
 uniform-continuity
  : (f : T ε (ιᶥ ⇾ ι))
  → ⟦ Pr2 · (f ᴶ · Ω) ⟧ is-a-modulus-of-uniform-continuity-of ⟦ f ⟧
 uniform-continuity = uniform-modulus-correct

\end{code}

§4.4 Church encodings of dialogue trees

\begin{code}

module DialogueTrees where

 open import Applications.InternalizedDialogueTree
 open import SystemT.Auxiliaries using (ιᶥ; typeᵀ)
 open import Framework.Gentzen.Genericity Dᵀ₂ ηᵀ κᵀ ιᶥ Rι

 -- Definition 4.37
 dialogue-trees-and-evaluation
  : Σ \(D : Set)
  → (ℕ → D) × ((ℕ → D) → ℕ → D) × (D → ℕᴺ → ℕ)
 dialogue-trees-and-evaluation = D , η , β , eval

 -- Definition 4.38
 leaf-replacement : (ℕ → D) → D → D
 leaf-replacement = κ

 -- Lemma 4.39
 evaluation-of-leaf-replacement
  : (F : ℕ → D) (d : D) (α : ℕᴺ)
  → eval (κ F d) α ≡ eval (F (eval d α)) α
 evaluation-of-leaf-replacement = eval-κ

 -- Definition 4.40
 church-encoding
  : Σ \(A : Ty)
  → ({Γ : Cxt} → T Γ (ι ⇾ A))
  × ({Γ : Cxt} → T Γ ((ι ⇾ A) ⇾ ι ⇾ A))
  × ({Γ : Cxt} → T Γ ((ι ⇾ A) ⇾ A ⇾ A))
 church-encoding = Dᵀ₂ , ηᵀ , βᵀ , κᵀ

 -- Definition 4.41
 internal-evaluator
  : ({Γ : Cxt} → T Γ (Dᵀ₂ ⇾ typeᵀ 2))
  × ({Γ : Cxt} → T Γ (ι ⇾ typeᵀ 2))
  × ({Γ : Cxt} → T Γ ((ι ⇾ typeᵀ 2) ⇾ ι ⇾ typeᵀ 2))
 internal-evaluator = evalᵀ , leafᵀ , branchᵀ

 -- Definition 4.42
 encoding-relation : ⟦ Dᵀ₂ ⟧ʸ → D → Set
 encoding-relation = _encodes_

 -- Lemma 4.43
 encoding-of-leaf-replacement
  : {g : ℕ → ⟦ Dᵀ₂ ⟧ʸ} {F : ℕ → D} {c : ⟦ Dᵀ₂ ⟧ʸ} {d : D}
  → ((j : ℕ) → g j encodes F j) → c encodes d
  → ⟦ κᵀ ⟧ g c encodes κ F d
 encoding-of-leaf-replacement = enc-κ

 -- Lemma 4.44
 evaluation-of-encoded-tree
  : {c : ⟦ Dᵀ₂ ⟧ʸ} {d : D} → c encodes d
  → (α : ℕᴺ) → ⟦ evalᵀ ⟧ c α ≡ eval d α
 evaluation-of-encoded-tree = encodes-eval

 -- Corollary 4.45
 evaluation-agrees-for-the-same-encoding
  : {c : ⟦ Dᵀ₂ ⟧ʸ} {d d′ : D} → c encodes d → c encodes d′
  → (α : ℕᴺ) → eval d α ≡ eval d′ α
 evaluation-agrees-for-the-same-encoding = encodes-eval-agree

 -- Definition 4.46
 dialogue-tree-nucleus-and-extraction
  : nucleus
  × ({Γ : Cxt} → T Γ (Dᵀ₂ ⇾ Dᵀ₂))
  × (T ε (typeᵀ 2) → T ε Dᵀ₂)
 dialogue-tree-nucleus-and-extraction
  = (Dᵀ₂ , ηᵀ , κᵀ) , Ωᵀ , dialogue-treeᵀ

 -- Definition 4.47
 base-dialogue-relation : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Dᵀ₂ ⟧ʸ → Set
 base-dialogue-relation = Rι

 -- Lemma 4.48
 preservation : (α : ℕᴺ) → LR.η-compatible α × LR.κ-compatible α
 preservation α = Rη α , Rκ α

 -- Lemma 4.49
 genericity-of-Ω : {Γ : Cxt} → is-generic (Ωᵀ {typeᵀ 2} {Γ})
 genericity-of-Ω = RΩ

 -- Theorem 4.50
 correctness-of-extraction
  : (f : T ε (typeᵀ 2))
  → Σ \(d : D) → (⟦ dialogue-treeᵀ f ⟧ encodes d)
               × ((α : ℕᴺ) → ⟦ f ⟧ α ≡ eval d α)
 correctness-of-extraction = Thm[InternalDialogue]

 -- Corollary 4.51
 evaluation-of-extracted-tree
  : (f : T ε (typeᵀ 2)) (α : ℕᴺ)
  → ⟦ f ⟧ α ≡ ⟦ evalᵀ · dialogue-treeᵀ f ⟧ α
 evaluation-of-extracted-tree = Cor[evalᵀdialogue-treeᵀ]

\end{code}

§4.5 Bar recursion

\begin{code}

module BarRecursion where

 open import SystemT.Auxiliaries using (ιᶥ; ι*; lt)

 private
  recursor-type : Ty → Ty
  recursor-type σ = (ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ

 module General (σ : Ty) where

  open import Applications.BarRecursion.General σ
  open import Framework.Gentzen.Genericity Jι η κ ιᶥ Rι

  -- Definition 4.52
  general-bar-recursion-monotonicity-and-security
   : ((ℕ* → ℕ) → ⟦ recursor-type σ ⟧ʸ → Set)
   × ((ℕ* → ℕ) → Set)
   × ((ℕ* → ℕ) → (ℕᴺ → ℕ) → Set)
  general-bar-recursion-monotonicity-and-security
   = GBR , monotone , _secures_

  -- Definition 4.53
  general-bar-recursion-nucleus : nucleus
  general-bar-recursion-nucleus = Jι , η , κ

  -- Definition 4.54
  generic-element : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
  generic-element = Ω

  -- Lemma 4.55
  bar-recursion-for-length-comparison
   : FunExt → (n : ℕ) → GBR (λ s → lt n (len s)) (⟦ Ψ ⟧ n)
  bar-recursion-for-length-comparison = Ψ-GBR

  -- Definition 4.56
  base-bar-recursion-relation : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
  base-bar-recursion-relation = Rι

  -- Lemma 4.57
  preservation : (α : ℕᴺ)
               → LR.η-compatible α
               × (FunExt → LR.κ-compatible α)
  preservation α = Rη α , (λ fe → Rκ fe α)

  -- Lemma 4.58
  genericity-of-Ω : FunExt → {Γ : Cxt} → is-generic (Ω {Γ})
  genericity-of-Ω = RΩ

  -- Theorem 4.59
  extraction-of-general-bar-recursors
   : FunExt → (Y : T ε (ιᶥ ⇾ ι))
   → monotone ⟦ 𝐒 Y ⟧ × ⟦ 𝐒 Y ⟧ secures ⟦ Y ⟧ × GBR ⟦ 𝐒 Y ⟧ ⟦ 𝐠𝐛𝐫 Y ⟧
  extraction-of-general-bar-recursors = gbr-extraction-correct

 module UniformModulus where

  open import Applications.Continuity.UniformViaGeneralBarRecursion
  open UniformContinuity using (_is-a-modulus-of_on-inputs-bounded-by_)

  -- Definition 4.61
  uniform-modulus : T ε (ιᶥ ⇾ ι) → T ε (ιᶥ ⇾ ι)
  uniform-modulus = 𝐌

  -- Proposition 4.62
  correctness-of-uniform-modulus
   : FunExt
   → (Y : T ε (ιᶥ ⇾ ι)) {δ : ℕᴺ}
   → ⟦ 𝐌 Y ⟧ δ is-a-modulus-of ⟦ Y ⟧ on-inputs-bounded-by δ
  correctness-of-uniform-modulus = uniform-modulus-correct

 module Spector (σ : Ty) where

  open import Applications.BarRecursion.General σ
  open import Applications.BarRecursion.SpectorViaGeneral σ

  -- Definition 4.63
  Spector-bar-recursor
   : ({Γ : Cxt} → T Γ ((ιᶥ ⇾ ι) ⇾ recursor-type σ ⇾ recursor-type σ))
   × (FunExt → (Y : ℕᴺ → ℕ) (S : ℕ* → ℕ) (ξ : ⟦ recursor-type σ ⟧ʸ)
      → monotone S × S secures Y × GBR S ξ → SBR Y (⟦ Φ ⟧ Y ξ))
   × (T ε (ιᶥ ⇾ ι) → T ε (recursor-type σ))
  Spector-bar-recursor = Φ , Φ-spec , 𝐬𝐛𝐫

  -- Proposition 4.64
  Spector-bar-recursion-equations
   : FunExt → (Y : T ε (ιᶥ ⇾ ι)) → SBR ⟦ Y ⟧ ⟦ 𝐬𝐛𝐫 Y ⟧
  Spector-bar-recursion-equations = sbr-correct

 module Modified where

  open import Applications.BarRecursion.ModifiedViaGeneral

  private
   modified-recursor-type : Ty
   modified-recursor-type = (ι* ⇾ (ι ⇾ ι) ⇾ ιᶥ) ⇾ ι* ⇾ ι

  -- Definition 4.65
  modified-bar-recursor
   : ({Γ : Cxt} → T Γ ((ιᶥ ⇾ ι) ⇾ recursor-type ι ⇾ modified-recursor-type))
   × (T ε (ιᶥ ⇾ ι) → T ε modified-recursor-type)
  modified-bar-recursor = Θ , 𝐦𝐛𝐫

  -- Proposition 4.66
  modified-bar-recursion-equation
   : FunExt → (Y : T ε (ιᶥ ⇾ ι)) → MBR ⟦ Y ⟧ ⟦ 𝐦𝐛𝐫 Y ⟧
  modified-bar-recursion-equation = mbr-correct

\end{code}

§5.1 Generalized nuclei

\begin{code}

open import SystemT.WithSumsAndLists as E
 using (DataTy; dataᵀ)
 renaming (Ty to Tyᴱ; Cxt to Cxtᴱ; T to Tᴱ; _⇾_ to _⇒_)

-- Definition 5.1
generalized-nucleus : Set
generalized-nucleus
 = Σ \(J : Tyᴱ → Tyᴱ)
 → ({Γ : Cxtᴱ} {A : Tyᴱ} → Tᴱ Γ (A ⇒ J A))
 × ({Γ : Cxtᴱ} {A B : Tyᴱ} → Tᴱ Γ ((A ⇒ J B) ⇒ J A ⇒ J B))

\end{code}

§5.3 Translation of sums and lists

\begin{code}

module SumsAndLists where

 module Translation ((J , η , κ) : generalized-nucleus) where

  open import Framework.Gentzen.WithSumsAndLists J η κ

  -- Definition 5.2
  extended-translation
   : (DataTy → Tyᴱ)
   × (Tyᴱ → Tyᴱ)
   × (Cxtᴱ → Cxtᴱ)
   × ({A : Tyᴱ} (ρ : Tyᴱ) {Γ : Cxtᴱ}
       → Tᴱ Γ ((A ⇒ ⟨ ρ ⟩ᴶ) ⇒ J A ⇒ ⟨ ρ ⟩ᴶ))
   × ({Γ : Cxtᴱ} {ρ : Tyᴱ} → Tᴱ Γ ρ → Tᴱ ⟪ Γ ⟫ᴶ ⟨ ρ ⟩ᴶ)
  extended-translation = ⟨_⟩ᴰ , ⟨_⟩ᴶ , ⟪_⟫ᴶ , KE , _ᴶ

\end{code}

§5.4 The extended fundamental theorem

\begin{code}

  module Relations
    (Rᴰ : (D : DataTy) → E.⟦ dataᵀ D ⟧ʸ → E.⟦ ⟨ dataᵀ D ⟩ᴶ ⟧ʸ → Set)
   where

   open LogicalRelation Rᴰ

   -- Definition 5.3
   logical-relation
    : ((ρ : Tyᴱ) → E.⟦ ρ ⟧ʸ → E.⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set)
    × ((Γ : Cxtᴱ) → E.⟦ Γ ⟧ˣ → E.⟦ ⟪ Γ ⟫ᴶ ⟧ˣ → Set)
   logical-relation = R , Rˣ

   -- Definition 5.4
   lifted-relation : (D : DataTy) → E.⟦ dataᵀ D ⟧ʸ → E.⟦ ⟨ D ⟩ᴰ ⟧ʸ → Set
   lifted-relation = S

   -- Compatibility conditions (5.1) and (5.2)
   compatibility-conditions : Set
   compatibility-conditions = η-compatible × κ-compatible

   -- Lemma 5.5
   preservation-KE
    : κ-compatible
    → {D : DataTy} (ρ : Tyᴱ) {Γ : Cxtᴱ} {γ : E.⟦ Γ ⟧ˣ}
    → {f : E.⟦ dataᵀ D ⟧ʸ → E.⟦ ρ ⟧ʸ} {g : E.⟦ ⟨ D ⟩ᴰ ⟧ʸ → E.⟦ ⟨ ρ ⟩ᴶ ⟧ʸ}
    → (∀ {x a} → S D x a → R ρ (f x) (g a))
    → R (dataᵀ D ⇒ ρ) f (E.⟦ KE ρ ⟧ᵐ γ g)
   preservation-KE = R[KE]

   -- Theorem 5.6
   fundamental-theorem
    : compatibility-conditions
    → {Γ : Cxtᴱ} {ρ : Tyᴱ} (t : Tᴱ Γ ρ)
    → {γ : E.⟦ Γ ⟧ˣ} {δ : E.⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
    → Rˣ Γ γ δ → R ρ (E.⟦ t ⟧ᵐ γ) (E.⟦ t ᴶ ⟧ᵐ δ)
   fundamental-theorem (Rη , Rκ) = Soundness.FTLR Rη Rκ

\end{code}

§6.1 The Kuroda-style monadic translation

\begin{code}

generalized-nucleus-for-T : Set
generalized-nucleus-for-T
 = Σ \(J : Ty → Ty)
 → ({Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ))
 × ({Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ))

module KurodaTranslation ((J , η , κ) : generalized-nucleus-for-T) where

 open import Framework.Kuroda J η κ

 -- Definition 6.1
 Kuroda-translation
  : (Ty → Ty) × (Ty → Ty) × (Cxt → Cxt)
  × ({Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ ⟨ ρ ⟩ᴷ)
  × ({Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ)) → T Γ (J σ) → T Γ (J τ))
  × ({Γ : Cxt} {ρ : Ty} → T Γ (ρ ⇾ (ι ⇾ J (ρ ⇾ J ρ)) ⇾ ι ⇾ J ρ))
 Kuroda-translation = ⟨_⟩ , ⟨_⟩ᴷ , ⟪_⟫ , _ᴷ , _●_ , Rec●

 module Relations (C : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴷ ⟧ʸ → Set) where

  open LogicalRelation C

  -- Definition 6.2
  logical-relations
   : ((ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ ⟧ʸ → Set)
   × ((Γ : Cxt) → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ ⟧ˣ → Set)
  logical-relations = V , Vˣ

  -- Compatibility conditions (6.1) and (6.2)
  compatibility-conditions : Set
  compatibility-conditions = η-compatible × κ-compatible

  -- Theorem 6.3
  fundamental-theorem
   : compatibility-conditions
   → {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
   → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ ⟧ˣ}
   → Vˣ Γ γ δ → C ρ (⟦ t ⟧ᵐ γ) (⟦ t ᴷ ⟧ᵐ δ)
  fundamental-theorem (Rη , Rκ) = Soundness.FTLR Rη Rκ

module PointwiseContinuityViaKuroda where

 open import Applications.Continuity.PointwiseViaKuroda
 open import Framework.Kuroda J η κ using (⟨_⟩; ⟨_⟩ᴷ)
 open import SystemT.Auxiliaries using (ιᶥ)
 open PointwiseContinuity using (_is-a-modulus-of-pointwise-continuity-of_)

 -- Definition 6.4
 pointwise-continuity-nucleus : generalized-nucleus-for-T
 pointwise-continuity-nucleus = J , η , κ

 -- Definition 6.5
 value-and-computation-relations
  : (α : ℕᴺ) (n : ℕ)
  → ((ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ ⟧ʸ → Set)
  × ((ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴷ ⟧ʸ → Set)
 value-and-computation-relations α n = At.V α n , At.C α n

 -- Lemma 6.6
 preservation
  : (α : ℕᴺ) (n : ℕ) → At.K.η-compatible α n × At.K.κ-compatible α n
 preservation α n = At.η-compatible α n , At.κ-compatible α n

 -- Definition 6.7
 generic-element
  : ({Γ : Cxt}
  → T Γ (ι ⇾ J ι)) × ({Γ : Cxt} → T Γ (J (ι ⇾ J ι)))
 generic-element = q , Ω

 -- Lemma 6.8
 genericity-of-Ω
  : (α : ℕᴺ) (n : ℕ)
  → At.V α n (ι ⇾ ι) α ⟦ q ⟧ × At.C α n (ι ⇾ ι) α ⟦ Ω ⟧
 genericity-of-Ω α n = At.q-related α n , At.Ω-related α n

 -- Corollary 6.9
 pointwise-continuity
  : Σ \(M : T ε (ιᶥ ⇾ ι) → T ε (ιᶥ ⇾ ι))
  → (f : T ε (ιᶥ ⇾ ι))
  → ⟦ M f ⟧ is-a-modulus-of-pointwise-continuity-of ⟦ f ⟧
 pointwise-continuity = 𝐌 , pointwise-modulus-correct

module ComparingExtractedModuli where

 open import Applications.Continuity.Comparison
 import Applications.Continuity.PointwiseViaGentzen as G
 import Applications.Continuity.PointwiseViaKuroda as K
 open import SystemT.Auxiliaries using (ιᶥ)

 -- Example 6.10
 comparison-of-extracted-moduli
  : Σ \(t : T ε (ιᶥ ⇾ ι)) → (α : ℕᴺ)
  → (⟦ t ⟧ α ≡ 0) × (⟦ G.𝐌 t ⟧ α ≡ 0) × (⟦ K.𝐌 t ⟧ α ≡ 1)
 comparison-of-extracted-moduli
  = t , λ α → t-zero α , gentzen-modulus-zero α , kuroda-modulus-one α

\end{code}

§6.2 The Kolmogorov-style monadic translation

\begin{code}

module KolmogorovTranslation ((J , η , κ) : generalized-nucleus-for-T) where

 open import Framework.Kolmogorov J η κ

 -- Definition 6.11
 Kolmogorov-translation
  : (Ty → Ty) × (Ty → Ty) × (Cxt → Cxt)
  × ({Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᴷᵒ ⟨ ρ ⟩ᴷᵒ)
  × ({Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ)) → T Γ σ → T Γ (J τ))
  × ({Γ : Cxt} {ρ : Ty} → T Γ (ρ ⇾ (J ι ⇾ J (J ρ ⇾ J ρ)) ⇾ ι ⇾ J ρ))
 Kolmogorov-translation = ⟨_⟩ , ⟨_⟩ᴷᵒ , ⟪_⟫ᴷᵒ , _ᴷᵒ , _◇_ , Rec◇

 open Gentzen (J ι) η κ using (_ᴶ)
 open import Framework.Kuroda J η κ using (_ᴷ ; _●_)

 -- Remark 6.12
 translated-application
  : {Γ : Cxt} {σ τ : Ty} (f : T Γ (σ ⇾ τ)) (a : T Γ σ)
  → ((f · a) ᴶ ≡ (f ᴶ · a ᴶ))    -- Gentzen
  × ((f · a) ᴷ ≡ (f ᴷ ● a ᴷ))    -- Kuroda
  × ((f · a) ᴷᵒ ≡ (f ᴷᵒ ◇ a ᴷᵒ)) -- Kolmogorov
 translated-application f a = refl , refl , refl

\end{code}
