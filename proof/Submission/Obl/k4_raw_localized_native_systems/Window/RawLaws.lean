import Submission.Obl.k4_raw_localized_native_systems.RawWitnesses
import Submission.Obl.k4_raw_localized_native_systems.Window.Witness

/-! Original earlier graph laws. Their full masses and coordinates are retained. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The original graph point, before any earlier affine change of coordinates. -/
def rawGraph (q : Point) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (x q.1 q.2)

theorem measurable_rawGraph : Measurable rawGraph := by
  unfold rawGraph x
  fun_prop

theorem base4_rawGraph (q : Point) : base4 (rawGraph q) = basePt q := rfl

/-- The full earlier incidence law in its original graph coordinates. -/
def rawLaw (W : Atlas p k) (H : Fin W.C → Set Point) (e : Fin W.C) : Measure (EuclideanSpace ℝ (Fin 4)) :=
  Measure.map rawGraph ((priorMass p k (W.γ e)).restrict (H e))

/-- The mass of the entire earlier witness event, before current-chart restrictions. -/
def rawMass (W : Atlas p k) (H : Fin W.C → Set Point) (e : Fin W.C) : ENNReal :=
  priorMass p k (W.γ e) (H e)

theorem rawLaw_mass (W : Atlas p k) (H : Fin W.C → Set Point) (e : Fin W.C) :
    rawLaw W H e univ = rawMass W H e := by
  rw [rawLaw, Measure.map_apply measurable_rawGraph MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rfl

theorem rawMass_ne_top (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ}
    {H : Fin W.C → Set Point} {κ r : ℝ} (hW : WChart p k W M D κ r e)
    (hHsub : H e ⊆ W.F e) : rawMass W H e ≠ ⊤ :=
  ne_top_of_le_ne_top (wmass_ne_top hp hW) (measure_mono hHsub)

theorem rawMass_pos {W : Atlas p k} {e : Fin W.C}
    {H : Fin W.C → Set Point} {κ r : ℝ} (hκ : 0 < κ) (hN : 0 < p.N k)
    (hdet : (W.Q e).det ≠ 0)
    (hfloor : ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ rawMass W H e) : 0 < rawMass W H e := by
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr ?_) hfloor
  have := abs_pos.mpr hdet
  positivity

theorem raw_weighted_mass_le_one (hp : Valid p) {W : Atlas p k} {M D : ℕ}
    {H : Fin W.C → Set Point} {κ r : ℝ}
    (hW : ∀ e, WChart p k W M D κ r e)
    (hHsub : ∀ e, H e ⊆ W.F e)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e')) :
    (∑ e, ENNReal.ofReal (p.ω k (W.γ e)) * rawLaw W H e univ) ≤ 1 := by
  apply le_trans _ (sum_wwt_le_one hp W hW hdisj)
  apply Finset.sum_le_sum
  intro e he
  rw [rawLaw_mass]
  exact mul_le_mul' le_rfl (measure_mono (hHsub e))

theorem rawLaw_base (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ}
    {H : Fin W.C → Set Point} {κ r τ χ : ℝ} (hκ : 1 ≤ κ) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (hW : WChart p k W M D κ r e)
    (hHm : MeasurableSet (H e)) (hHsub : H e ⊆ W.F e)
    (hfloor : ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ rawMass W H e)
    (hgood : ∀ q ∈ H e, p.g k (W.γ e) r (obs (p.B k (W.γ e)) (δ (p.N k) r) q) ≤
      ENNReal.ofReal (p.N k ^ (-p.f r + τ)))
    (hbudget : 64 * κ ^ 3 * p.N k ^ τ ≤ p.N k ^ χ) :
    Measure.map base4 (rawLaw W H e) ≤
      (ENNReal.ofReal (p.N k ^ χ / ((1 / (2 : ℝ) ^ W.T) * |(W.Q e).det|)) *
        rawLaw W H e univ) • volume := by
  have hN : 0 < p.N k := hp.scale_pos k
  have hB : 0 < p.B k (W.γ e) := hp.B_pos k (W.γ e)
  have hκ0 : 0 < κ := by linarith
  have hd : 0 < |(W.Q e).det| := abs_pos.mpr hW.det_ne
  have h2 : (0 : ℝ) < (2 : ℝ) ^ W.T := by positivity
  let ρ := (priorMass p k (W.γ e)).restrict (H e)
  have hρμ : ρ ≤ selected p k (W.γ e) :=
    Measure.restrict_mono (fun q hq => (hW.sel (hHsub hq)).1) le_rfl
  obtain ⟨hgm, hlaw⟩ := valid_g_law hp k (W.γ e) hr hrL
  have hbase := chart_depth_base_ceiling (selected p k (W.γ e)) ρ hρμ hκ
    (delta_pos (p.N k) r) hB (W.c e) (W.u e) (W.Q e) (W.R e) hW.R_degree
    (p.g k (W.γ e) r) hgm hlaw (ENNReal.ofReal (p.N k ^ (-p.f r + τ))) (by
      refine ae_restrict_of_forall_mem hHm fun q hq => ?_
      obtain ⟨-, hqA, hqt, hfl⟩ := hW.sel (hHsub hq)
      obtain ⟨hfit, hR0, hR1, hR2⟩ := hW.fit hqA hqt
      exact ⟨hqt, hfit, hR0, hR1, hR2, hfl, hgood q hq⟩)
  have hmap : Measure.map base4 (rawLaw W H e) = Measure.map basePt ρ := by
    rw [rawLaw, Measure.map_map measurable_base4 measurable_rawGraph]
    rfl
  rw [hmap, rawLaw_mass]
  apply hbase.trans
  apply smul_measure_le_smul_left
  calc
    ENNReal.ofReal (p.N k ^ (-p.f r + τ)) * ENNReal.ofReal (64 * κ ^ 2)
      = ENNReal.ofReal (p.N k ^ (-p.f r) * (64 * κ ^ 2 * p.N k ^ τ)) := by
          rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_add hN]
          congr 1
          ring
    _ ≤ ENNReal.ofReal (p.N k ^ (-p.f r) * (p.N k ^ χ / κ)) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ hκ0]
          calc 64 * κ ^ 2 * p.N k ^ τ * κ = 64 * κ ^ 3 * p.N k ^ τ := by ring
            _ ≤ _ := hbudget
    _ = ENNReal.ofReal (p.N k ^ χ / ((1 / (2 : ℝ) ^ W.T) * |(W.Q e).det|)) *
        ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * κ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
    _ ≤ ENNReal.ofReal (p.N k ^ χ / ((1 / (2 : ℝ) ^ W.T) * |(W.Q e).det|)) *
        rawMass W H e := mul_le_mul' le_rfl hfloor

end
end Submission.Obl.k4_raw_localized_native_systems.Window
