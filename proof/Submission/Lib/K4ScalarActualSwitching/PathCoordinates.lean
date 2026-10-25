/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 9a98134f7426729d513297455b610395ba5215bf,
Submission/Obl/k4_scalar_mesh_projection/PathCoordinates.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.SwitchTimes

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open MeasureTheory

noncomputable def appendArrayEquiv {A : Type*} [MeasurableSpace A] (n : ℕ) :
    ((Fin n → A) × A) ≃ᵐ (Fin (n + 1) → A) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) (Fin.last n)).symm

theorem appendArrayEquiv_apply {A : Type*} [MeasurableSpace A] (n : ℕ)
    (z : (Fin n → A) × A) : appendArrayEquiv n z = Fin.snoc z.1 z.2 := by
  simp [appendArrayEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last', MeasurableEquiv.prodComm]

theorem measurePreserving_appendArrayEquiv {A : Type*} [MeasurableSpace A]
    (π : Measure A) [SigmaFinite π] (n : ℕ) :
    MeasurePreserving (appendArrayEquiv (A := A) n)
      ((Measure.pi (fun _ : Fin n => π)).prod π) (Measure.pi (fun _ : Fin (n + 1) => π)) := by
  exact ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => π) (Fin.last n)).symm).comp
    Measure.measurePreserving_swap

noncomputable def fourArrayEquiv {A : Type*} [MeasurableSpace A] :
    (((A × A) × A) × A) ≃ᵐ (Fin 4 → A) :=
  (((MeasurableEquiv.piFinTwo (fun _ => A)).symm.prodCongr (MeasurableEquiv.refl A)).trans
    (appendArrayEquiv 2)).prodCongr (MeasurableEquiv.refl A) |>.trans (appendArrayEquiv 3)

theorem fourArrayEquiv_apply {A : Type*} [MeasurableSpace A]
    (z : ((A × A) × A) × A) : fourArrayEquiv z = ![z.1.1.1, z.1.1.2, z.1.2, z.2] := by
  ext i
  fin_cases i <;>
    simp [fourArrayEquiv, MeasurableEquiv.prodCongr, MeasurableEquiv.trans,
      appendArrayEquiv_apply, MeasurableEquiv.piFinTwo_symm_apply, Fin.snoc]

theorem measurePreserving_fourArrayEquiv {A : Type*} [MeasurableSpace A]
    (π : Measure A) [SigmaFinite π] :
    MeasurePreserving (fourArrayEquiv (A := A)) (((π.prod π).prod π).prod π)
      (Measure.pi (fun _ : Fin 4 => π)) := by
  exact (measurePreserving_appendArrayEquiv π 3).comp
    (((measurePreserving_appendArrayEquiv π 2).comp
      ((measurePreserving_piFinTwo (fun _ : Fin 2 => π)).symm.prod
        (MeasurePreserving.id π))).prod (MeasurePreserving.id π))

noncomputable def historyArrayEquiv {H A : Type*}
    [MeasurableSpace H] [MeasurableSpace A] :
    ((((H × A) × A) × A) × A) ≃ᵐ H × (Fin 4 → A) :=
  (((MeasurableEquiv.prodAssoc.prodCongr (MeasurableEquiv.refl A)).prodCongr
      (MeasurableEquiv.refl A)).trans
    ((MeasurableEquiv.prodAssoc.prodCongr (MeasurableEquiv.refl A)).trans
      MeasurableEquiv.prodAssoc)).trans
    ((MeasurableEquiv.refl H).prodCongr fourArrayEquiv)

theorem historyArrayEquiv_apply {H A : Type*}
    [MeasurableSpace H] [MeasurableSpace A]
    (z : (((H × A) × A) × A) × A) :
    historyArrayEquiv z = (z.1.1.1.1, ![z.1.1.1.2, z.1.1.2, z.1.2, z.2]) := by
  simp [historyArrayEquiv, MeasurableEquiv.prodCongr, MeasurableEquiv.trans,
    MeasurableEquiv.prodAssoc, fourArrayEquiv_apply]

theorem measurePreserving_historyArrayEquiv {H A : Type*}
    [MeasurableSpace H] [MeasurableSpace A]
    (μ : Measure H) [SFinite μ] (ρ : Measure A) [SigmaFinite ρ] :
    MeasurePreserving (historyArrayEquiv (H := H) (A := A))
      ((((μ.prod ρ).prod ρ).prod ρ).prod ρ) (μ.prod (Measure.pi (fun _ : Fin 4 => ρ))) := by
  exact ((MeasurePreserving.id μ).prod (measurePreserving_fourArrayEquiv ρ)).comp
    ((measurePreserving_prodAssoc μ ((ρ.prod ρ).prod ρ) ρ).comp
      (((measurePreserving_prodAssoc μ (ρ.prod ρ) ρ).prod (MeasurePreserving.id ρ)).comp
        (((measurePreserving_prodAssoc μ ρ ρ).prod (MeasurePreserving.id ρ)).prod
          (MeasurePreserving.id ρ))))

/-- Group the observed four control/time pairs while keeping the entire
original start state as the first coordinate. -/
noncomputable def pathProductEquiv {H V T : Type*}
    [MeasurableSpace H] [MeasurableSpace V] [MeasurableSpace T] :
    ((((H × (V × T)) × (V × T)) × (V × T)) × (V × T)) ≃ᵐ
      (H × (Fin 4 → V)) × (Fin 4 → T) :=
  historyArrayEquiv.trans
    (((MeasurableEquiv.refl H).prodCongr
      (MeasurableEquiv.arrowProdEquivProdArrow V T (Fin 4))).trans
        MeasurableEquiv.prodAssoc.symm)

theorem pathProductEquiv_apply {H V T : Type*}
    [MeasurableSpace H] [MeasurableSpace V] [MeasurableSpace T]
    (z : (((H × (V × T)) × (V × T)) × (V × T)) × (V × T)) :
    pathProductEquiv z =
      ((z.1.1.1.1, ![z.1.1.1.2.1, z.1.1.2.1, z.1.2.1, z.2.1]),
        ![z.1.1.1.2.2, z.1.1.2.2, z.1.2.2, z.2.2]) := by
  change (((historyArrayEquiv z).1, fun i => ((historyArrayEquiv z).2 i).1),
    fun i => ((historyArrayEquiv z).2 i).2) = _
  rw [historyArrayEquiv_apply]
  refine Prod.ext (Prod.ext rfl ?_) ?_
  all_goals ext i; fin_cases i <;> rfl

theorem measurePreserving_pathProductEquiv {H V T : Type*}
    [MeasurableSpace H] [MeasurableSpace V] [MeasurableSpace T]
    (μ : Measure H) [SFinite μ] (π : Measure V) [SigmaFinite π]
    (τ : Measure T) [SigmaFinite τ] :
    MeasurePreserving (pathProductEquiv (H := H) (V := V) (T := T))
      ((((μ.prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ))
      ((μ.prod (Measure.pi (fun _ : Fin 4 => π))).prod (Measure.pi (fun _ : Fin 4 => τ))) := by
  exact (measurePreserving_prodAssoc μ (Measure.pi (fun _ : Fin 4 => π))
    (Measure.pi (fun _ : Fin 4 => τ))).symm.comp
      (((MeasurePreserving.id μ).prod
        (measurePreserving_arrowProdEquivProdArrow V T (Fin 4) (fun _ => π) (fun _ => τ))).comp
          (measurePreserving_historyArrayEquiv μ (π.prod τ)))

/-- The start-dependent signed-increment change preserves the whole
product reference. It therefore preserves every unnormalized ceiling. -/
theorem measurePreserving_jointSignedIncrements {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (start : H → ℝ) (hstart : Measurable start) :
    MeasurePreserving
      (fun z : H × (Fin 4 → ℝ) => (z.1, Switching.signedIncrements (start z.1) z.2))
      (μ.prod volume) (μ.prod volume) := by
  refine (MeasurePreserving.id μ).skew_product
    (g := fun h (t : Fin 4 → ℝ) => Switching.signedIncrements (start h) t) ?_ ?_
  · apply Measurable.of_eval
    intro i
    simp only [Function.uncurry_def, Switching.signedIncrements_apply]
    fin_cases i <;> fun_prop
  · exact ae_of_all _ (fun h => (Switching.measurePreserving_signedIncrements (start h)).map_eq)

noncomputable def pathIncrementCoordinates {H : Type*} [MeasurableSpace H]
    (start : H → ℝ)
    (z : (((H × (ℝ × ℝ)) × (ℝ × ℝ)) × (ℝ × ℝ)) × (ℝ × ℝ)) :
    (H × (Fin 4 → ℝ)) × (Fin 4 → ℝ) :=
  let p := pathProductEquiv z
  (p.1, Switching.signedIncrements (start p.1.1) p.2)

theorem measurePreserving_pathIncrementCoordinates {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (π : Measure ℝ) [SigmaFinite π]
    (start : H → ℝ) (hstart : Measurable start) :
    MeasurePreserving (pathIncrementCoordinates start)
      ((((μ.prod (π.prod volume)).prod (π.prod volume)).prod (π.prod volume)).prod (π.prod volume))
      ((μ.prod (Measure.pi (fun _ : Fin 4 => π))).prod volume) := by
  exact (measurePreserving_jointSignedIncrements
    (μ.prod (Measure.pi (fun _ : Fin 4 => π))) (fun h => start h.1)
      (hstart.comp measurable_fst)).comp (measurePreserving_pathProductEquiv μ π volume)

/-- Regrouping and taking actual signed increments keeps the original
retained path mass and its entire product reference ceiling. -/
theorem map_pathIncrementCoordinates_le {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (π : Measure ℝ) [SigmaFinite π]
    (start : H → ℝ) (hstart : Measurable start)
    (ρ : Measure (((((H × (ℝ × ℝ)) × (ℝ × ℝ)) × (ℝ × ℝ)) × (ℝ × ℝ))))
    (D : ENNReal)
    (hρ : ρ ≤ D •
      ((((μ.prod (π.prod volume)).prod (π.prod volume)).prod (π.prod volume)).prod (π.prod volume))) :
    ρ.map (pathIncrementCoordinates start) ≤
        D • ((μ.prod (Measure.pi (fun _ : Fin 4 => π))).prod volume) ∧
      ρ.map (pathIncrementCoordinates start) Set.univ = ρ Set.univ := by
  have hmp := measurePreserving_pathIncrementCoordinates μ π start hstart
  have hmap := Measure.map_mono hρ hmp.measurable
  rw [Measure.map_smul D hmp.measurable.aemeasurable, hmp.map_eq] at hmap
  exact ⟨hmap, by rw [Measure.map_apply hmp.measurable MeasurableSet.univ, Set.preimage_univ]⟩

end Submission.Lib.K4ScalarActualSwitching
