-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.AnisotropicPrismPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPrismPacking

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- A prism meeting an aligned rectangular box lies in the box enlarged
by twice each corresponding prism side. -/
theorem prism_enclosure_of_meeting_box {a b c A B C : ℝ} {z p₀ : V}
    (e : V ≃ₗᵢ[ℝ] V) (hmeet : (P a b c z e ∩ P A B C p₀ e).Nonempty) :
    P a b c z e ⊆ P (A + 2 * a) (B + 2 * b) (C + 2 * c) p₀ e := by
  obtain ⟨q, hqP, hqB⟩ := hmeet
  intro p hp
  have hcoord (i : Fin 3) (d D : ℝ)
      (hp' : |e (p - z) i| ≤ d / 2) (hq' : |e (q - z) i| ≤ d / 2)
      (hqB' : |e (q - p₀) i| ≤ D / 2) :
      |e (p - p₀) i| ≤ (D + 2 * d) / 2 := by
    have he : e (p - p₀) i = e (p - z) i - e (q - z) i + e (q - p₀) i := by
      simp only [map_sub, PiLp.sub_apply]
      ring
    rw [he]
    have ha := abs_add_le (e (p - z) i - e (q - z) i) (e (q - p₀) i)
    have hs := abs_sub (e (p - z) i) (e (q - z) i)
    linarith
  exact ⟨hcoord 0 a A hp.1 hqP.1 hqB.1,
    hcoord 1 b B hp.2.1 hqP.2.1 hqB.2.1,
    hcoord 2 c C hp.2.2 hqP.2.2 hqB.2.2⟩

/-- Packing in an anisotropic box preserves its three distinct scales. -/
theorem prism_packing_in_box {a b c A B C : ℝ} {p₀ : V}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (e : V ≃ₗᵢ[ℝ] V) (F : Finset V)
    (hdisj : (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e))
    (hmeet : ∀ z ∈ F, (P a b c z e ∩ P A B C p₀ e).Nonempty) :
    o ((F.card : ℝ) * (a * b * c)) ≤ o ((A + 2 * a) * (B + 2 * b) * (C + 2 * c)) := by
  have hsub : (⋃ z ∈ F, P a b c z e) ⊆ P (A + 2 * a) (B + 2 * b) (C + 2 * c) p₀ e := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
    exact prism_enclosure_of_meeting_box e (hmeet z hz) hpz
  have hvol (z : V) : μ (P a b c z e) = o (a * b * c) :=
    Factor.box_volume ha hb hc z e
  calc
    o ((F.card : ℝ) * (a * b * c)) = ∑ z ∈ F, μ (P a b c z e) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.ofReal_mul (Nat.cast_nonneg F.card) |>.trans
        (by rw [ENNReal.ofReal_natCast]; rfl)
    _ = μ (⋃ z ∈ F, P a b c z e) :=
      (measure_biUnion_finset hdisj (fun z _ => measurableSet_prism _ _ _ z e)).symm
    _ ≤ μ (P (A + 2 * a) (B + 2 * b) (C + 2 * c) p₀ e) := measure_mono hsub
    _ = _ := Factor.box_volume (by positivity) (by positivity) (by positivity) p₀ e

/-- An adapted frame sees a tube-shaped ellipsoid with its transverse
scale intact. -/
theorem anisotropic_frame_coord {ρ r A : ℝ} {w q : V}
    (hρ : 0 ≤ ρ) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3)
    (hperp : ‖q - (inner ℝ w q) • w‖ ≤ ρ * r)
    (haxial : |inner ℝ w q| ≤ r) (hframe : |e w i| ≤ A * ρ) :
    |e q i| ≤ (A + 1) * ρ * r := by
  have he : e q i = e (q - (inner ℝ w q) • w) i + (inner ℝ w q) * e w i := by
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ |e (q - (inner ℝ w q) • w) i| + |(inner ℝ w q) * e w i| := abs_add_le _ _
    _ ≤ ρ * r + r * (A * ρ) := by
      rw [abs_mul]
      exact add_le_add ((abs_rotated_coord_le e _ i).trans hperp)
        (mul_le_mul haxial hframe (abs_nonneg _) hr)
    _ = _ := by ring

/-- The long coordinate needs only the norm-one axis bound. -/
theorem anisotropic_frame_coord_long {ρ r : ℝ} {w q : V}
    (hρ1 : ρ ≤ 1) (hr : 0 ≤ r) (hw : ‖w‖ = 1)
    (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3)
    (hperp : ‖q - (inner ℝ w q) • w‖ ≤ ρ * r)
    (haxial : |inner ℝ w q| ≤ r) : |e q i| ≤ 2 * r := by
  have he : q = (q - (inner ℝ w q) • w) + (inner ℝ w q) • w := by module
  have hnorm : ‖q‖ ≤ 2 * r := by
    calc
      _ = ‖(q - (inner ℝ w q) • w) + (inner ℝ w q) • w‖ := congrArg norm he
      _ ≤ ‖q - (inner ℝ w q) • w‖ + ‖(inner ℝ w q) • w‖ := norm_add_le _ _
      _ ≤ ρ * r + r := by
        rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
        exact add_le_add hperp haxial
      _ ≤ _ := by nlinarith
  exact (abs_rotated_coord_le e q i).trans hnorm

/-- A planar ellipsoidal cell fits into an adapted rectangular box with
transverse side proportional to rho*r and long side proportional to r. -/
theorem anisotropic_slab_subset_box {ρ r a t : ℝ} {w p₀ : V}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : 0 ≤ r) (hw : ‖w‖ = 1)
    (e : V ≃ₗᵢ[ℝ] V) (hframe : |e w 1| ≤ 10 * ρ) :
    {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
      |inner ℝ w (p - p₀)| ≤ r ∧ |e (p - p₀) 0 - t| ≤ a} ⊆
      P (2 * a) (22 * ρ * r) (4 * r) (p₀ + e.symm (EuclideanSpace.single 0 t)) e := by
  intro p hp
  have h1 := anisotropic_frame_coord hρ hr (by norm_num : (0 : ℝ) ≤ 10)
    e 1 hp.1 hp.2.1 hframe
  have h2 := anisotropic_frame_coord_long hρ1 hr hw e 2 hp.1 hp.2.1
  change |e (p - (p₀ + e.symm (EuclideanSpace.single 0 t))) 0| ≤ (2 * a) / 2 ∧
    |e (p - (p₀ + e.symm (EuclideanSpace.single 0 t))) 1| ≤ (22 * ρ * r) / 2 ∧
    |e (p - (p₀ + e.symm (EuclideanSpace.single 0 t))) 2| ≤ (4 * r) / 2
  rw [show p - (p₀ + e.symm (EuclideanSpace.single 0 t)) =
      (p - p₀) - e.symm (EuclideanSpace.single 0 t) by abel, map_sub, e.apply_symm_apply]
  simp only [PiLp.sub_apply, EuclideanSpace.single_apply, Fin.isValue,
    ite_true, ite_false, sub_zero]
  have h0 := hp.2.2
  simp only [map_sub, PiLp.sub_apply] at h0 h1 h2
  norm_num
  exact ⟨h0, by linarith, by linarith⟩

/-- The local packing budget for physical prisms is O(a*rho*r^2),
matching the pullback of the planar lower volume estimate. -/
theorem prism_packing_in_anisotropic_slab {ρ r a b c d t : ℝ} {w p₀ : V}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hda : d ≤ 2 * a) (hbr : b ≤ 128 * ρ * r) (hcr : c ≤ r) (hw : ‖w‖ = 1)
    (e : V ≃ₗᵢ[ℝ] V) (hframe : |e w 1| ≤ 10 * ρ) (F : Finset V)
    (hdisj : (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e))
    (hmeet : ∀ z ∈ F, (P a b c z e ∩
      {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
        |inner ℝ w (p - p₀)| ≤ r ∧ |e (p - p₀) 0 - t| ≤ d}).Nonempty) :
    o ((F.card : ℝ) * (a * b * c)) ≤ o (10008 * a * ρ * r ^ 2) := by
  have hbox := anisotropic_slab_subset_box hρ hρ1 hr hw e hframe (a := d) (t := t)
    (p₀ := p₀)
  have hmeet' (z : V) (hz : z ∈ F) : (P a b c z e ∩
      P (2 * d) (22 * ρ * r) (4 * r) (p₀ + e.symm (EuclideanSpace.single 0 t)) e).Nonempty := by
    obtain ⟨p, hp, hps⟩ := hmeet z hz
    exact ⟨p, hp, hbox hps⟩
  have hh := prism_packing_in_box ha hb hc (by positivity : 0 ≤ 2 * d)
    (by positivity : 0 ≤ 22 * ρ * r) (by positivity : 0 ≤ 4 * r) e F hdisj hmeet'
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (2 * d + 2 * a) * (22 * ρ * r + 2 * b) * (4 * r + 2 * c) ≤
        (6 * a) * (278 * ρ * r) * (6 * r) := by gcongr <;> nlinarith
    _ = _ := by ring

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
