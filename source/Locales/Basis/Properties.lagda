---
title:           Properties of locale bases
author:          Ayberk Tosun
date-started:    2024-08-21
---

These definitions originally lived in the `CompactRegular` module. They were
then refactored into `Locales.SmallBasis` around 2024-08-21. On 2024-09-23, they
were transferred into this standalone module, which will hopefully be their
final place.

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

module Locales.Basis.Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
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

\begin{code}

basic-is-small : (X : Locale 𝓤 𝓥 𝓦)
               → ((ℬ , b) : Directed-Basisᴰ (𝒪 X))
               → ⟨ 𝒪 X ⟩ is-locally 𝓦 small
               → (image (ℬ [_])) is 𝓦 small
basic-is-small X (ℬ , b) ψ =
 sr (ℬ [_]) (index ℬ , ≃-refl (index ℬ)) ψ carrier-of-[ poset-of (𝒪 X) ]-is-set

\end{code}
