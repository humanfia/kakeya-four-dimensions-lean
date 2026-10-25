-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismCarrier.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LongRescale
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorDyadic

/-! # Passing between factoring prisms and bounded-length carriers -/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- A prism lies in a carrier of its long dimension, with radius twice its middle dimension. -/
theorem box_subset_carrier {a b c : ℝ} (hab : a ≤ b) (hb : 0 < b) (hc : 0 < c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hw : e w = EuclideanSpace.single 2 (1 : ℝ)) :
    Factor.box a b c z e ⊆ Carrier c (2 * b) (z - (1 / 2 : ℝ) • w) w := by
  intro p hp
  obtain ⟨hp0, hp1, hp2⟩ := hp
  let t : ℝ := e (p - z) 2
  apply mem_thickening_iff.mpr
  refine ⟨z + t • w, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(t + c / 2) / c, ?_, ?_⟩
    · have ht := abs_le.mp hp2
      change -(c / 2) ≤ t ∧ t ≤ c / 2 at ht
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_one hc]; linarith
    · simp only [add_sub_cancel_left, smul_smul]
      rw [div_mul_cancel₀ _ hc.ne']
      module
  · have heq : e (p - (z + t • w)) =
        EuclideanSpace.single 0 (e (p - z) 0) + EuclideanSpace.single 1 (e (p - z) 1) := by
      rw [show p - (z + t • w) = (p - z) - t • w by module, map_sub, map_smul, hw]
      ext i
      fin_cases i <;> simp [t, EuclideanSpace.single]
    have hnorm : ‖e (p - (z + t • w))‖ ≤ |e (p - z) 0| + |e (p - z) 1| := by
      rw [heq]
      simpa using norm_add_le (EuclideanSpace.single (0 : Fin 3) (e (p - z) 0))
        (EuclideanSpace.single (1 : Fin 3) (e (p - z) 1))
    rw [e.norm_map] at hnorm
    rw [dist_eq_norm]
    linarith

/-- A carrier lies in the concentric prism obtained by adding its radius at each end. -/
theorem carrier_subset_box {c ρ : ℝ} (hc : 0 ≤ c) (z : Space)
    (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hw : e w = EuclideanSpace.single 2 (1 : ℝ)) :
    Carrier c ρ (z - (1 / 2 : ℝ) • w) w ⊆ Factor.box (2 * ρ) (2 * ρ) (c + 2 * ρ) z e := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  set q := z - (1 / 2 : ℝ) • w + ((1 - c) / 2) • w + s • (c • w)
  have hqeq : q - z = (c * (s - 1 / 2)) • w := by dsimp [q]; module
  have hqframe : e (q - z) = (c * (s - 1 / 2)) • EuclideanSpace.single 2 (1 : ℝ) := by
    rw [hqeq, map_smul, hw]
  have hcoord (i : Fin 3) : |e (p - z) i - e (q - z) i| < ρ := by
    have heq : e (p - z) - e (q - z) = e (p - q) := by rw [← map_sub]; congr 1; abel
    have h := PiLp.norm_apply_le (e (p - q)) i
    rw [e.norm_map] at h
    have hdist : ‖p - q‖ < ρ := by simpa [q, dist_eq_norm] using hpq
    have hi : e (p - z) i - e (q - z) i = e (p - q) i := by
      exact congrArg (fun v : Space => v i) heq
    rw [hi]
    have h' : |e (p - q) i| ≤ ‖p - q‖ := by simpa [Real.norm_eq_abs] using h
    exact h'.trans_lt hdist
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  rw [hqframe] at h0 h1 h2
  norm_num [EuclideanSpace.single, PiLp.single_apply] at h0 h1 h2
  have hlong : |c * (s - 1 / 2)| ≤ c / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hs.1, hs.2]
  change |e (p - z) 0| ≤ 2 * ρ / 2 ∧ |e (p - z) 1| ≤ 2 * ρ / 2 ∧
    |e (p - z) 2| ≤ (c + 2 * ρ) / 2
  have hlast := abs_add_le (e (p - z) 2 - c * (s - 1 / 2)) (c * (s - 1 / 2))
  simp only [sub_add_cancel] at hlast
  simp only [map_sub, PiLp.sub_apply] at hlast ⊢
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The Katz--Tao count of prisms passes to their enclosing carriers. -/
theorem carrier_katz_of_box {a b c m : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    {N : ℕ} (z : Fin N → Space) (e : Fin N → Space ≃ₗᵢ[ℝ] Space) (w : Fin N → Space)
    (hw : ∀ k, e k (w k) = EuclideanSpace.single 2 (1 : ℝ))
    (hK : ∀ W, Convex ℝ W →
      ENNReal.ofReal (({k | Factor.box a b c (z k) (e k) ⊆ W}.ncard : ℝ) * (a * b * c)) ≤
        ENNReal.ofReal m * volume W) :
    ∀ W, Convex ℝ W →
      ENNReal.ofReal (({k | Carrier c (2 * b) (z k - (1 / 2 : ℝ) • w k) (w k) ⊆ W}.ncard : ℝ) *
        (2 * b) ^ 2) ≤ ENNReal.ofReal ((4 * b / (a * c)) * m) * volume W := by
  intro W hW
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 ≤ 4 * b / (a * c) := by positivity
  let q : ℝ := ({k | Carrier c (2 * b) (z k - (1 / 2 : ℝ) • w k) (w k) ⊆ W}.ncard : ℝ)
  have hcount : ENNReal.ofReal (q * (a * b * c)) ≤ ENNReal.ofReal m * volume W := by
    apply le_trans _ (hK W hW)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.mpr
    exact Set.ncard_mono fun k hk => (box_subset_carrier hab hb hc (z k) (e k) (hw k)).trans hk
  calc
    ENNReal.ofReal (q * (2 * b) ^ 2) =
        ENNReal.ofReal (4 * b / (a * c)) * ENNReal.ofReal (q * (a * b * c)) := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      field_simp
      ring
    _ ≤ ENNReal.ofReal (4 * b / (a * c)) * (ENNReal.ofReal m * volume W) :=
      mul_le_mul_right hcount _
    _ = ENNReal.ofReal ((4 * b / (a * c)) * m) * volume W := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC]

/-- Enlarging a prism to the doubled carrier loses at most `640 b/a` in reference volume. -/
theorem dilated_carrier_volume_le_box {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hw : e w = EuclideanSpace.single 2 (1 : ℝ)) :
    volume (Carrier (2 * c) (4 * b) (z - (1 / 2 : ℝ) • w) w) ≤
      ENNReal.ofReal (640 * (b / a)) * volume (Factor.box a b c z e) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  calc
    volume (Carrier (2 * c) (4 * b) (z - (1 / 2 : ℝ) • w) w) ≤
        volume (Factor.box (2 * (4 * b)) (2 * (4 * b)) (2 * c + 2 * (4 * b)) z e) :=
      measure_mono (carrier_subset_box (by positivity) z e hw)
    _ = ENNReal.ofReal ((2 * (4 * b)) * (2 * (4 * b)) * (2 * c + 2 * (4 * b))) :=
      Factor.box_volume (by positivity) (by positivity) (by positivity) z e
    _ ≤ ENNReal.ofReal (640 * (b / a)) * volume (Factor.box a b c z e) := by
      rw [Factor.box_volume ha.le hb.le hc.le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have heq : 640 * (b / a) * (a * b * c) = 640 * b ^ 2 * c := by field_simp
      rw [heq]
      nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hbc)]

/-- Slab counts relative to a factoring prism transfer to the doubled long carrier. -/
theorem reference_slab_count_box_to_carrier {a b c l : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hw : e w = EuclideanSpace.single 2 (1 : ℝ)) {n : ℕ} {T : Fin n → Set Space}
    (hT : ∀ i, T i ⊆ Factor.box a b c z e) (hcount : ReferenceSlabCount (Factor.box a b c z e) l T) :
    ReferenceSlabCount (Carrier (2 * c) (4 * b) (z - (1 / 2 : ℝ) • w) w)
      (640 * (b / a) * l) T := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hsub := (box_subset_carrier hab hb hc z e hw).trans
    (carrier_subset_dilate (by positivity : 0 ≤ 2 * b) (z - (1 / 2 : ℝ) • w) w)
  have heq : 2 * (2 * b) = 4 * b := by ring
  rw [heq] at hsub
  exact reference_slab_count_enlarge (by positivity) hsub
    (dilated_carrier_volume_le_box ha hab hbc z e hw) hT hcount

namespace Interfaces

/-- Local rescaling inside a factoring prism, with its own normalized slab hypothesis. -/
theorem local_rescaling_box_of_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ a b c : ℝ, δ ≤ a → a ≤ b → b ≤ (1 / 2 : ℝ) → b ≤ c → 1 ≤ c → c ≤ 8 →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V),
    0 < n → (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ P a b c z e ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    X δ n x v → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → K δ m n x v →
    ReferenceSlabCount (P a b c z e) l (fun i => T δ (x i) (v i)) →
    o (κ * δ ^ ε * (δ / b) ^ ω * m⁻¹ * (n * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / a)) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨κ, hκ, η, hη, hbound⟩ := local_rescaling_carrier_of_estimate hσ hσ2 hω hE ε hε
  refine ⟨κ * (1 / 2 : ℝ) ^ ω * (320 : ℝ) ^ (-σ), by positivity, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl a b c hδa hab hb2 hbc hc1 hc8 n x v Y z e hn hfib hX hdense hK hB
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  let w : V := e.symm (EuclideanSpace.single 2 (1 : ℝ))
  have hew : e w = EuclideanSpace.single 2 (1 : ℝ) := e.apply_symm_apply _
  have hw : ‖w‖ = 1 := by rw [← e.norm_map w, hew]; simp
  have hbox : P a b c z e ⊆ Carrier c (2 * b) (z - (1 / 2 : ℝ) • w) w :=
    box_subset_carrier hab hb hc z e hew
  have hB' := reference_slab_count_box_to_carrier ha hab hbc z e hew
    (fun i => (hfib i).2.1) hB
  have hl' : 1 ≤ 640 * (b / a) * l := by
    have hr : 1 ≤ b / a := (one_le_div ha).mpr hab
    nlinarith
  have h := hbound δ (2 * b) hδ hδ100 (by linarith) (by linarith) m
    (640 * (b / a) * l) hm hl' c hc1 hc8 n x v Y (z - (1 / 2 : ℝ) • w) w hn hw
    (fun i => ⟨(hfib i).1, ((hfib i).2.1).trans hbox, (hfib i).2.2⟩) hX hdense hK
    (by simpa only [show 2 * (2 * b) = 4 * b by ring] using hB')
  have hscale : δ / (2 * b) = (1 / 2 : ℝ) * (δ / b) := by ring
  have hproduct : m ^ (-(3 / 2 : ℝ)) * (640 * (b / a) * l) * (n * δ / (2 * b)) =
      320 * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / a)) := by field_simp; ring
  change ENNReal.ofReal _ ≤ volume _ at h ⊢
  rw [hproduct, hscale, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 320) (by positivity)] at h
  convert h using 1
  congr 1
  ring

end Interfaces

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
