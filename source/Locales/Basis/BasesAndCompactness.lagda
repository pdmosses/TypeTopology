---
title:           Definition of locale bases
author:          Ayberk Tosun
date-started:    2024-08-21
---

These definitions and lemmas originally lived in the `CompactRegular` module.
They were then refactored into `Locales.SmallBasis` on 2024-08-21. On
2024-09-23, they were transferred into this standalone module, which will
hopefully their final home.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Logic
open import MLTT.Spartan
open import UF.Size
open import UF.Base
open import UF.EquivalenceExamples using (Σ-assoc)

module Locales.Basis.BasesAndCompactness
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Basis.Definition pt fe
open import Locales.Compactness.Definition pt fe
open import Locales.Frame pt fe hiding (has-directed-basis₀)
open import Locales.Spectrality.Properties pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import MLTT.List using (List; map; _<$>_; []; _∷_)
open import Slice.Family
open import UF.Equiv renaming (_■ to _𝒬ℰ𝒟)
open import UF.ImageAndSurjection pt
open import UF.SubtypeClassifier
open import UF.Univalence using (Univalence)

open PropositionalTruncation pt

open AllCombinators pt fe

open Locale

\end{code}

Compact opens are basic.

This was previously proved in Tom de Jong's development, I will add a link there
later.

\begin{code}

compact-opens-are-basic : (X : Locale 𝓤 𝓥 𝓦)
                        → (b : Directed-Basisᴰ (𝒪 X))
                        → (K : ⟨ 𝒪 X ⟩)
                        → (is-compact-open X K ⇒ is-basic X K b) holds
compact-opens-are-basic {_} {_} {𝓦} X (ℬ , β) K κ = ‡ (β K)
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

  ‡ : Σ 𝒥 ꞉ Fam 𝓦 (index ℬ) , (K is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆
                            ∧ is-directed (𝒪 X) ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
    → is-basic X K (ℬ , β) holds
  ‡ (𝒥 , c , d) =
   ∥∥-rec (holds-is-prop (is-basic X K (ℬ , β))) † (κ ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ d q)
    where
     q : (K ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆)) holds
     q = reflexivity+ (poset-of (𝒪 X)) (⋁[ 𝒪 X ]-unique ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ K c)

     † : Σ j ꞉ index 𝒥 , (K ≤[ poset-of (𝒪 X) ] ℬ [ 𝒥 [ j ] ]) holds
       → is-basic X K (ℬ , β) holds
     † (j , φ) = ∣ 𝒥 [ j ] , ≤-is-antisymmetric (poset-of (𝒪 X)) ψ φ ∣
      where
       open PosetReasoning (poset-of (𝒪 X))

       Ⅰ = ⋁[ 𝒪 X ]-upper ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ j
       Ⅱ = reflexivity+
            (poset-of (𝒪 X))
            (⋁[ 𝒪 X ]-unique ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ K c ⁻¹)

       ψ : (ℬ [ 𝒥 [ j ] ] ≤[ poset-of (𝒪 X) ] K) holds
       ψ = ℬ [ 𝒥 [ j ] ] ≤⟨ Ⅰ ⟩ ⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ ≤⟨ Ⅱ ⟩ K ■

\end{code}

Bases consisting of compact opens have equivalent images.

\begin{code}

basis-is-unique : (X : Locale 𝓤 𝓥 𝓦)
                → ((ℬ , _) : Directed-Basisᴰ (𝒪 X))
                → consists-of-compact-opens X ℬ holds
                → image (ℬ-compact X [_]) ≃ image (ℬ [_])
basis-is-unique X (ℬ , b) κ =
 r , (s , s-is-section-of-r) , s , r-is-retract-of-s
  where
   r : image (ℬ-compact X [_]) → image (ℬ [_])
   r (K , p) = K , K-is-basic
    where
     K-is-compact : is-compact-open X K holds
     K-is-compact = ∥∥-rec (holds-is-prop (is-compact-open X K)) † p
      where
       † : Σ (λ x → ℬ-compact X [ x ] ＝ K) → is-compact-open X K holds
       † ((K′ , κ′) , q) = transport (λ - → is-compact-open X - holds) q κ′

     K-is-basic : K ∈image (ℬ [_])
     K-is-basic =
      ∥∥-rec ∃-is-prop † (compact-opens-are-basic X (ℬ , b) K K-is-compact)
       where
        † : Σ i ꞉ index ℬ , ℬ [ i ] ＝ K → ∃ j ꞉ index ℬ , ℬ [ j ] ＝ K
        † (i , p) = ∣ i , p ∣

   s : image (ℬ [_]) → image (ℬ-compact X [_])
   s (K , p) = K , ∥∥-rec ∃-is-prop † p
    where
     † : Σ i ꞉ index ℬ , ℬ [ i ] ＝ K → ∃ (K′ , _) ꞉ index (ℬ-compact X) , K′ ＝ K
     † (i , q) = ∣ (ℬ [ i ] , κ i) , q ∣

   s-is-section-of-r : r ∘ s ∼ id
   s-is-section-of-r (U , p) = to-subtype-＝ (λ _ → ∃-is-prop) refl

   r-is-retract-of-s : s ∘ r ∼ id
   r-is-retract-of-s (K , p) = to-subtype-＝ (λ _ → ∃-is-prop) refl

\end{code}

The following was refactored and simplified on 2024-09-23.

\begin{code}

basic-iso-to-𝒦 : (X : Locale 𝓤 𝓥 𝓦)
               → ((ℬ , b) : Directed-Basisᴰ (𝒪 X))
               → consists-of-compact-opens X ℬ holds
               → image (ℬ [_]) ≃ 𝒦 X
basic-iso-to-𝒦 X (ℬ , β) κ = s , qinvs-are-equivs s (r , † , ‡)
 where
  s : image (ℬ [_]) → 𝒦 X
  s (K , φ) = K , ∥∥-rec (holds-is-prop (is-compact-open X K)) † φ
   where
    † : (Σ i ꞉ index ℬ , ℬ [ i ] ＝ K) → is-compact-open X K holds
    † (i , q) = transport (λ - → is-compact-open X - holds) q (κ i)

  r : 𝒦 X → image (ℬ [_])
  r (K , φ) = K , compact-opens-are-basic X (ℬ , β) K φ

  † : r ∘ s ∼ id
  † (U , φ) = to-subtype-＝ (λ - → being-in-the-image-is-prop - (ℬ [_])) refl

  ‡ : s ∘ r ∼ id
  ‡ 𝔘@(U , φ) = to-𝒦-＝ X ψ φ refl
   where
    ψ : is-compact-open X (pr₁ (r 𝔘)) holds
    ψ = ∥∥-rec (holds-is-prop (is-compact-open X (pr₁ (r 𝔘)))) ♢ μ
     where
      ♢ : Σ i ꞉ index ℬ , ℬ [ i ] ＝ pr₁ (r (U , φ))
        → is-compact-open X (pr₁ (r (U , φ))) holds
      ♢ (i , p) = transport (λ - → is-compact-open X - holds) p (κ i)

      μ : pr₁ (r 𝔘) ∈image (ℬ [_])
      μ = pr₂ (r (U , φ))

\end{code}
