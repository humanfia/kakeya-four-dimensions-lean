-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NormalizedFactoring

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file FlatAssembly.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

/-- A globally saturated flat factorization yields exactly the frozen prism
alternative, including Frostman above and below and the local Katz--Tao bound. -/
theorem flat_prisms_of_saturated_cover {n p : ℕ} (A : Fin n → Set Space)
    (W : Fin p → Set Space) {δ ζ₂ ζ₃ a b c H D K : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδa : δ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 2)
    (hflat : min a 1 ≤ δ ^ (ζ₂ / 200) * min b 1)
    (hn : 0 < n) (hc : 0 < c) (hH : 0 < H) (hD : 0 < D) (hK : 0 ≤ K)
    (hE₁ : 32 * H * D ≤ δ ^ (-ζ₃))
    (hE₂ : 2048 * (H * D) ^ 2 ≤ δ ^ (-ζ₃))
    (hE₃ : 8192 * K * (H * D) ^ 2 ≤ δ ^ (-ζ₃))
    (hball : ∀ i, A i ⊆ Metric.ball (0 : Space) 1)
    (hF : Frostman K A)
    (hupper : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((contained A U : ℝ) * δ ^ 2) ≤ ENNReal.ofReal c * volume U)
    (hshape : ∀ j, ∃ e : Space ≃ᵃⁱ[ℝ] Space,
      W j = e '' {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2})
    (hcover : ∀ i, ∃ j, A i ⊆ W j)
    (hdegree : ∀ i, (ncard {j | A i ⊆ W j} : ℝ) ≤ D)
    (hsat : ∀ j, c * a * b ≤ H * (contained A (W j) : ℝ) * δ ^ 2) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧
      (n : ℝ) ≤ 4 * k ∧ FlatPrisms ζ₂ ζ₃ δ (fun i => A (g i)) := by
  classical
  have ha0 : 0 ≤ a := hδ.le.trans hδa
  have hb0 : 0 ≤ b := ha0.trans hab
  have hwidths := normalized_widths hδ.le hδ1 hδa hab hb1
  have hmina : 0 ≤ min a 1 := hδ.le.trans hwidths.1
  have hminb : 0 ≤ min b 1 := hmina.trans hwidths.2.1
  obtain ⟨k, g, q, z, e₁, e₂, e₃, hg, hsize, he, hcov, hdeg, hsat'⟩ :=
    normalize_saturated_cover A W ha0 hb0 (sq_pos_of_pos hδ) hc hH hD
      hball hupper hshape hcover hdegree hsat
  let B := fun i => A (g i)
  let P := fun j => Prism (min a 1) (min b 1) (z j) (e₁ j) (e₂ j) (e₃ j)
  let V := 8 * min a 1 * min b 1
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hk : 0 < k := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hk' : 0 < (k : ℝ) := by nlinarith
    exact_mod_cast hk'
  have hupperB (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal ((contained B U : ℝ) * δ ^ 2) ≤ ENNReal.ofReal c * volume U := by
    have hncard : contained B U ≤ contained A U :=
      Set.ncard_le_ncard_of_injOn g (fun _ h => h) hg.injOn
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hncard) (sq_nonneg δ))).trans (hupper U hU)
  have hP (j) : Convex ℝ (P j) ∧ volume (P j) = ENNReal.ofReal V :=
    ⟨prism_convex _ _ _ _ _ _, prism_volume hmina hminb _ _ _ _ (he j)⟩
  obtain ⟨hbal, habove, hbelow⟩ := saturated_cover_bounds B P (sq_pos_of_pos hδ) hV hc
    (by positivity : 0 ≤ 32 * H * D) (by positivity : 0 ≤ 64 * H * D)
    hupperB hP hdeg hsat'
  have hFP : Frostman ((K * 4) * (32 * H * D) * (64 * H * D)) P :=
    frostman_of_balanced_cover B P hk (by positivity) (by positivity) (by positivity)
      (hF.restrict hK g hg hsize) hcov hbal hdeg
  refine ⟨k, g, hg, hsize, min a 1, min b 1, hwidths.1, hflat,
    hwidths.2.2.1, q, z, e₁, e₂, e₃, he, hcov, ?_, ?_, ?_, ?_⟩
  · intro j j'
    exact (hbal j j').trans (mul_le_mul_of_nonneg_right hE₁ (Nat.cast_nonneg _))
  · apply hFP.mono
    nlinarith only [hE₃]
  · intro j U hU
    change ENNReal.ofReal (ncard {i | B i ⊆ P j ∧ B i ⊆ U} : ℝ) * volume (P j) ≤ _
    rw [(hP j).2, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact (hbelow j U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hE₁ (Nat.cast_nonneg _))) le_rfl)
  · intro j U hU
    change ENNReal.ofReal
      (ncard {j' | P j' ⊆ Metric.thickening (min b 1) (P j) ∧ P j' ⊆ U} : ℝ) *
        volume (P j) ≤ _
    have hncard : ncard {j' | P j' ⊆ Metric.thickening (min b 1) (P j) ∧ P j' ⊆ U} ≤
        contained P U := Set.ncard_le_ncard (fun _ h => h.2)
    rw [(hP j).2, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    calc
      _ ≤ ENNReal.ofReal ((contained P U : ℝ) * V) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hncard) hV)
      _ ≤ ENNReal.ofReal ((32 * H * D) * (64 * H * D)) * volume U := habove U hU
      _ ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * volume U := by
        apply mul_le_mul' _ le_rfl
        apply ENNReal.ofReal_le_ofReal
        nlinarith only [hE₂]

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
