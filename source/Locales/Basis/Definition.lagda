---
title:           Definition of locale bases
author:          Ayberk Tosun
date-started:    2024-08-21
---

These definitions originally lived in the `CompactRegular` module. They were
then refactored into `Locales.SmallBasis`. On 2024-09-23, they were transferred
into this standalone module, which will hopefully be their final place.

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

module Locales.Basis.Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

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

\section{Undirected basis}

The type `basis-for F B` expresses that the family `B` forms a basis for frame
`F`.

\begin{code}

basis-forᴰ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
basis-forᴰ {𝓦 = 𝓦} F (I , β) =
 (U : ⟨ F ⟩) → Σ J ꞉ Fam 𝓦 I , (U is-lub-of ⁅ β j ∣ j ε J ⁆) holds
  where
   open Joins (λ x y → x ≤[ poset-of F ] y)

Basisᴰ : (F : Frame 𝓤 𝓥 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
Basisᴰ {𝓤} {𝓥} {𝓦} F = Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , basis-forᴰ F ℬ

\end{code}

\section{Directed basis}

The superscript `_ᴰ` is our notational convention for marking that we are
working with the structural version of a notion.

\begin{code}

directed-basis-forᴰ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
directed-basis-forᴰ {𝓤} {𝓥} {𝓦} F ℬ@(I , β) =
 (U : ⟨ F ⟩) →
  Σ J ꞉ Fam 𝓦 I ,
   (U is-lub-of ⁅ β j ∣ j ε J ⁆ ∧ is-directed F ⁅ β j ∣ j ε J ⁆) holds
    where
     open Joins (λ x y → x ≤[ poset-of F ] y)

Directed-Basisᴰ : Frame 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
Directed-Basisᴰ {𝓤} {𝓥} {𝓦} F = Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , directed-basis-forᴰ F ℬ

directed-basis-is-basis : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩)
                        → directed-basis-forᴰ F ℬ
                        → basis-forᴰ F ℬ
directed-basis-is-basis {_} {_} {𝓦} F ℬ β U = † (β U)
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)

  † : Σ J ꞉ Fam 𝓦 (index ℬ) ,
       (U is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆ ∧ is-directed F ⁅ ℬ [ j ] ∣ j ε J ⁆)
        holds
    → Σ J ꞉ Fam 𝓦 (index ℬ) , (U is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆) holds
  † (J , c , _)= J , c

\end{code}

An open `U` is called _basic_ if it is in the image of some basis.

\begin{code}

is-basic : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Directed-Basisᴰ (𝒪 X) → Ω (𝓤 ⊔ 𝓦)
is-basic X U (ℬ , _) = U ∈image (ℬ [_]) , ∃-is-prop

\end{code}
