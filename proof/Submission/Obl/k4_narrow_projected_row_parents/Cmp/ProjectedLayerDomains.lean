/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ProjectedLayerDomains.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ProjectedDomainBudget
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ReferenceNumerators
import Submission.Obl.k4_general_parent_projected_layers.Layers

/-! Original reference budget of the literal common domains of an accepted projected layer. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open scoped ENNReal

noncomputable section

/-- Subdividing a full projected layer into common domains preserves its original
reference budget up to a fixed power of its loss. The floors used are exactly those
of the accepted projected layer, against the original residual. -/
theorem projected_layer_common_domains {α : Type} [MeasurableSpace α]
    (L : ProjLayer α) {N H d ell La s χ q m : ℝ}
    (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (π : Measure ℝ) (ρ : Measure (α × ℝ))
    (hgood : L.Good N H d ell La s χ b P π ρ)
    (hN : 0 < N) (hH : 1 ≤ H) (hχ : 0 < χ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hm : 0 < m) (hmβ : m ≤ L.β) :
    ∃ menus : Fin L.n → Finset Code,
      (∀ i l, l ∈ L.C i → ∀ t ∈ Icc (0 : ℝ) 1,
        code q χ (N ^ (-ell * s)) m (b l) t ∈ menus i) ∧
      (∀ i c, c ∈ menus i → c 1 = L.tag i 0 ∧ c 2 = L.tag i 1) ∧
      (∑ i, ∑ c ∈ menus i,
        ENNReal.ofReal (q * χ * m * (N ^ (-s)) ^ d) *
          π {w : ℝ | ⌊w / χ⌋ = c 1}) ≤ ENNReal.ofReal (360 * H ^ 4) * ρ univ := by
  classical
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hg : 0 < N ^ (-ell * s) := Real.rpow_pos_of_pos hN _
  choose menus hcount htags hcover using fun i : Fin L.n =>
    projected_domain_menu hH hq hq1 hg hm hmβ hgood.2.2.1 χ (L.u i) (L.v i) (L.tag i)
  have hsource : ∀ i l, l ∈ L.C i → ∀ t ∈ Icc (0 : ℝ) 1,
      code q χ (N ^ (-ell * s)) m (b l) t ∈ menus i := by
    intro i l hl t ht
    have hfit := (hgood.2.2.2.2.2 i).2.2.2.1 l hl
    apply hcover i (b l) t ht hfit.1 hfit.2.1
    intro r hr
    simpa [Submission.Lib.K4ContactNormalization.point] using (hfit.2.2 r hr).1
  have hweight (i : Fin L.n) :
      (∑ c ∈ menus i, ENNReal.ofReal (q * χ * m * (N ^ (-s)) ^ d) *
        π {w : ℝ | ⌊w / χ⌋ = c 1}) ≤
      ENNReal.ofReal (360 * H ^ 3) * L.weight N d s χ π i := by
    calc
      _ = ∑ _c ∈ menus i, ENNReal.ofReal (q * χ * m * (N ^ (-s)) ^ d) *
          π {w : ℝ | ⌊w / χ⌋ = L.tag i 0} := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [(htags i c hc).1]
      _ = ENNReal.ofReal ((menus i).card * q * m * χ * (N ^ (-s)) ^ d) *
          π {w : ℝ | ⌊w / χ⌋ = L.tag i 0} := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 2
        ring
      _ ≤ ENNReal.ofReal ((360 * H ^ 3 * L.β) * χ * (N ^ (-s)) ^ d) *
          π {w : ℝ | ⌊w / χ⌋ = L.tag i 0} := by
        apply mul_le_mul' _ le_rfl
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcount i) hχ.le)
            (Real.rpow_nonneg (Real.rpow_nonneg hN.le _) _))
      _ = _ := by
        rw [ProjLayer.weight, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  refine ⟨menus, hsource, htags, ?_⟩
  calc
    _ ≤ ∑ i, ENNReal.ofReal (360 * H ^ 3) * L.weight N d s χ π i :=
      Finset.sum_le_sum fun i _ => hweight i
    _ = ENNReal.ofReal (360 * H ^ 3) * ∑ i, L.weight N d s χ π i := (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (360 * H ^ 3) * (ENNReal.ofReal H * ρ univ) :=
      mul_le_mul' le_rfl (hgood.weight_sum_le hHpos)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

/-- The same actual projected menus have the exact real reference budget used
by the two-color comparison theorem. -/
theorem projected_layer_real_common_domains {α : Type} [MeasurableSpace α]
    (L : ProjLayer α) {N H d ell La s χ q m : ℝ}
    (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (π : Measure ℝ) [IsFiniteMeasure π] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    (hgood : L.Good N H d ell La s χ b P π ρ)
    (hN : 0 < N) (hH : 1 ≤ H) (hχ : 0 < χ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hm : 0 < m) (hmβ : m ≤ L.β) :
    ∃ menus : Fin L.n → Finset Code,
      (∀ i l, l ∈ L.C i → ∀ t ∈ Icc (0 : ℝ) 1,
        code q χ (N ^ (-ell * s)) m (b l) t ∈ menus i) ∧
      (∀ i c, c ∈ menus i → c 1 = L.tag i 0 ∧ c 2 = L.tag i 1) ∧
      (∑ i, ∑ c ∈ menus i, (q * χ * m * (N ^ (-s)) ^ d) *
        (π {w : ℝ | ⌊w / χ⌋ = c 1}).toReal) ≤ (360 * H ^ 4) * (ρ univ).toReal := by
  classical
  obtain ⟨menus, hcover, htags, hbudget⟩ := projected_layer_common_domains L b P π ρ hgood
    hN hH hχ hq hq1 hm hmβ
  refine ⟨menus, hcover, htags, ?_⟩
  let Index := Σ i : Fin L.n, (menus i)
  have hsum {M : Type} [AddCommMonoid M] (f : Code → M) :
      (∑ u : Index, f u.2.val) = ∑ i, ∑ c ∈ menus i, f c := by
    dsimp only [Index]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_coe_sort (menus i) f
  have hbudget' : (∑ u : Index, ENNReal.ofReal (q * χ * m * (N ^ (-s)) ^ d) *
      π {w : ℝ | ⌊w / χ⌋ = u.2.val 1}) ≤ ENNReal.ofReal (360 * H ^ 4) * ρ univ := by
    rw [hsum (fun c : Code => ENNReal.ofReal (q * χ * m * (N ^ (-s)) ^ d) *
      π {w : ℝ | ⌊w / χ⌋ = c 1})]
    exact hbudget
  have h := Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison.real_reference_budget
    (fun _ : Index => q * χ * m * (N ^ (-s)) ^ d) (fun _ => by positivity)
    (fun u : Index => π {w : ℝ | ⌊w / χ⌋ = u.2.val 1}) (fun _ => measure_ne_top _ _)
    (by positivity : 0 ≤ 360 * H ^ 4) (ρ univ) (measure_ne_top _ _) hbudget'
  rw [hsum (fun c : Code => (q * χ * m * (N ^ (-s)) ^ d) *
    (π {w : ℝ | ⌊w / χ⌋ = c 1}).toReal)] at h
  exact h

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
