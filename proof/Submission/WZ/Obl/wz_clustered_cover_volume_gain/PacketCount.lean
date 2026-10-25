-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PacketCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketContainment

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open WangZahlLot.Obl.wz_flat_factored_improvement (BodyConvexCount)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

lemma oriented_projective_close {u v : V} {s : ℝ} (h : pd u v ≤ s) :
    ∃ w : V, (w = u ∨ w = -u) ∧ ‖w - v‖ ≤ s := by
  change min ‖u - v‖ ‖u + v‖ ≤ s at h
  by_cases hh : ‖u - v‖ ≤ ‖u + v‖
  · exact ⟨u, Or.inl rfl, by simpa only [min_eq_left hh] using h⟩
  · refine ⟨-u, Or.inr rfl, ?_⟩
    rw [show -u - v = -(u + v) by abel, norm_neg]
    simpa only [min_eq_right (le_of_not_ge hh)] using h

/-- Coarse angular/spatial confinement gives the exact physical hypotheses
needed to use the local dagger count in the frozen grains configuration. -/
theorem packet_convex_count {n L A : ℕ} (hn : 0 < n) (hA : 1 ≤ A)
    (ι : Fin n → Fin L) (hι : Function.Injective ι) {θ a ρ c s m : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (hs : 0 < s) (hac : a ≤ ρ * c) (hscale : s * ρ * c ≤ A * a)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hD : ‖dualLinear θ (boxAxis e₀ 0)‖ ≤ 25 * θ)
    (hangle : ∀ i, ‖unit (dualLinear θ (boxAxis (e (ι i)) 0)) -
      unit (dualLinear θ (boxAxis e₀ 0))‖ ≤ s / 100)
    (hcenter : ∀ i, ‖coarseLinear θ (z (ι i) - z₀)‖ ≤ c / 100)
    (hshort : ∀ i, |inner ℝ (unit (dualLinear θ (boxAxis e₀ 0)))
      (coarseLinear θ (z (ι i) - z₀))| ≤ s * c / 100)
    (hlocal : ∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) :
    BodyConvexCount (fun i => P a (ρ * c) c (z (ι i)) (e (ι i)))
      (a * (ρ * c) * c) (((128 * A ^ 2 + 1) ^ 6 : ℕ) * m) := by
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hsc : s * c ≤ (A : ℝ) * (a / ρ) := by
    apply (mul_le_mul_iff_left₀ hρ).mp
    calc
      s * c * ρ = s * ρ * c := by ring
      _ ≤ A * a := hscale
      _ = (A * (a / ρ)) * ρ := by field_simp
  have hsn : s ≤ (A : ℝ) * ((a / ρ) / c) := by
    apply (mul_le_mul_iff_left₀ hc).mp
    calc
      s * c ≤ A * (a / ρ) := hsc
      _ = (A * ((a / ρ) / c)) * c := by field_simp
  have hpd (i : Fin n) : pd (boxAxis (e (ι i)) 0) (boxAxis e₀ 0) ≤ s := by
    have hh := normal_transport_inverse_pd hθ hθ1 (by norm_num : (0 : ℝ) < 25)
      (boxAxis_norm e₀ 0) (boxAxis_norm (e (ι i)) 0) hD
    have ht : pd (unit (dualLinear θ (boxAxis e₀ 0)))
        (unit (dualLinear θ (boxAxis (e (ι i)) 0))) ≤ s / 100 := by
      apply (min_le_left _ _).trans
      rw [norm_sub_rev]
      exact hangle i
    have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2 * 25)
    have hsym : pd (boxAxis (e (ι i)) 0) (boxAxis e₀ 0) =
        pd (boxAxis e₀ 0) (boxAxis (e (ι i)) 0) := by
      unfold pd
      rw [norm_sub_rev, add_comm]
    rw [hsym]
    linarith
  choose v hv hvclose using fun i => oriented_projective_close (hpd i)
  apply confined_grain_convex_count hn hA ι hι ha hρ hc hac z e v z₀ e₀ hv
  · intro i
    have hh := (norm_le_coarseLinear hθ hθ1 _).trans (hcenter i)
    have hm := mul_le_mul_of_nonneg_right hAr hc.le
    nlinarith
  · intro i
    rw [← inner_boxAxis]
    have hn0 : boxAxis e₀ 0 ≠ 0 := by intro he; have hh := boxAxis_norm e₀ 0; simp [he] at hh
    rw [normal_transport_coordinate hθ hθ1 hn0, abs_mul, abs_norm]
    have hh := mul_le_mul hD (hshort i) (abs_nonneg _) (by positivity : 0 ≤ 25 * θ)
    have ht := mul_le_mul_of_nonneg_right hθ1 (mul_pos hs hc).le
    nlinarith
  · intro i
    exact (hvclose i).trans hsn
  · exact hlocal

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
