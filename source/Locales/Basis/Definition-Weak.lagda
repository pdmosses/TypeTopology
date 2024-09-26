---
title:           Definition of a weak locale basis.
author:          Ayberk Tosun
date-started:    2024-09-24
---

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

module Locales.Basis.Definition-Weak
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

\begin{code}

directed-weak-basis-forᴰ : (X : Locale 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ 𝒪 X ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
directed-weak-basis-forᴰ {𝓤} {𝓥} {𝓦} X ℬ@(I , β) =
 (U : ⟨ 𝒪 X ⟩) →
  ∃ J ꞉ Fam 𝓦 I ,
   (U ＝ ⋁[ 𝒪 X ] ⁅ β j ∣ j ε J ⁆) × is-directed (𝒪 X) ⁅ β j ∣ j ε J ⁆ holds

Directed-Weak-Basisᴰ : Locale 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
Directed-Weak-Basisᴰ {𝓤} {𝓥} {𝓦} X =
 Σ ℬ ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ , directed-weak-basis-forᴰ X ℬ


\end{code}
